#!/usr/bin/env python3

# Script to build all benchmarks

# Copyright (C) 2017, 2019 Embecosm Limited
#
# Contributor: Graham Markall <graham.markall@embecosm.com>
# Contributor: Jeremy Bennett <jeremy.bennett@embecosm.com>
#
# This file is part of Embench.

# SPDX-License-Identifier: GPL-3.0-or-later

"""
Build all Embench programs.
"""


import argparse
import os
import shutil
import subprocess
import sys
import telnetlib
import queue
import re
import threading
import time
import datetime
from pathlib import Path
import shutil
import json
from statistics import mean
import multiprocessing
import pynrfjprog
from pynrfjprog import HighLevel

sys.path.append(
    os.path.join(os.path.abspath(os.path.dirname(__file__)), '../../embench-iot')
)
sys.path.append(
    os.path.join(os.path.abspath(os.path.dirname(__file__)), '../../embench-iot/pylib')
)


from embench_core import check_python_version
from embench_core import log
from embench_core import gp
from embench_core import setup_logging
from embench_core import log_args
from embench_core import find_benchmarks
from embench_core import log_benchmarks
from embench_core import arglist_to_str
from benchmark_size import benchmark_size
from benchmark_size import ALL_METRICS

import benchiot_measure_static_flash_and_ram

def sloc_files(results_pip_dir, files, category_name, static_results):
    static_results["SLOC"][category_name] = {}
    tot_sloc = 0
    for file in files:
            try:
                filename = os.path.basename(file)
                shrinked_file_path = os.path.join(results_pip_dir, f'results_static_pip-only_shrinked_{filename}')
                shrinked_file = open(shrinked_file_path, 'w')
                res = subprocess.run(
                    ["arm-none-eabi-gcc", "-fpreprocessed",
                        "-dD", "-E", "-P", file],
                    stdout=shrinked_file
                )
                shrinked_file.close()
                shrinked_file = open(shrinked_file_path, 'r')

                if res.returncode != 0:
                    print("***NOK***")
                    print(f'Investigate with command: arm-none-eabi-gcc -fpreprocessed -dD -E {file}')
                    return 0
                else:
                    sloc = sum(1 for _ in shrinked_file)
                    static_results["SLOC"][category_name] |= { filename: sloc }
                    tot_sloc += sloc

            except subprocess.TimeoutExpired:
                log.warning('Warning: computing SLOC timed out')
                return 0
    static_results["SLOC"]["Total"] += tot_sloc
    return 1

def pip_static_metrics(results_pip_dir, bench_dir, pip_app_dir, benchmarks, sequences):
    print("\n-----> Collecting Pip's static data:\n")

    static_results = {}

    # Pip SLOC (Source Lines of Code = same code without comments and blank lines)
    print("Computing Pip's SLOC", end='...')
    # Careful -fpreprocessed does not capture comments splitted with \
    boot_dir = "src/arch/nrf52-common/boot"
    exceptions = os.path.join(boot_dir, 'exception_handlers.c')
    svc = os.path.join(boot_dir, 'svc_handler.c')
    yield_c = os.path.join(boot_dir, 'yield_c.c')
    pip_interrupt_calls = os.path.join(boot_dir, 'pip_interrupt_calls.c')
    mpu = os.path.join(boot_dir, 'mpu.c')
    mal_dir = "src/arch/nrf52-common/MAL"
    malinit = os.path.join(mal_dir, 'malinit.c')
    mal = os.path.join(mal_dir, 'mal.c')
    malinternal = os.path.join(mal_dir, 'malinternal.c')
    generated_dir = "generated"
    services = os.path.join(generated_dir, 'Services.c')
    internal = os.path.join(generated_dir, 'Internal.c')

    pipcore = [services, internal, yield_c, pip_interrupt_calls]
    pip = [svc, exceptions]
    mal = [mal, malinternal, mpu]
    pipinit = [malinit]

    static_results["SLOC"] = {}
    static_results["SLOC"]["Total"] = 0

    success = sloc_files(results_pip_dir, pipcore, "pipcore", static_results)
    success &= sloc_files(results_pip_dir, pip, "pip", static_results)
    success &= sloc_files(results_pip_dir, mal, "mal", static_results)
    success &= sloc_files(results_pip_dir, pipinit, "pipinit", static_results)
    if success:
        print("OK")
    else:
        print("***ERROR in SLOC")


    # Report Pip size: code, bss, rodata, data
    succeeded = True
    first_bench = benchmarks[0] if benchmarks[0] != None else "pip"
    pip_root_scenario = "bench-pip-root" if "bench-pip-root" in sequences else "pip-only"
    try:
        print(f'Configuring {first_bench} in release mode', end='...')
        res = subprocess.run(
            ["./configure.sh", "--architecture=nrf52840", "--debugging-mode=semihosting",
                f'--boot-sequence={pip_root_scenario}', "--release"],
            capture_output=True,
        )
        if res.returncode != 0:
            print("***NOK***")
            print(f'Investigate with command: ./configure.sh --architecture=nrf52840--boot-sequence={pip_root_scenario} --release')
            succeeded = False

        else:
            log.debug(f'Configuration of {pip_root_scenario} successful')
            print("OK")

    except subprocess.TimeoutExpired:
        log.warning(f'Warning: link of {pip_root_scenario} timed out')
        succeeded = False

    if succeeded:
        print(f'Building {first_bench}', end='...')
        try:
            if "pip" in first_bench :
                make_cmd = ["make", "-B", "-s"]
                elf_dir = "."
                elf_path = "pip.elf"
                res = subprocess.run(
                    make_cmd,
                    capture_output=True,
                )
                if res.returncode != 0:
                    print("***NOK***")
                    print(f'--> Investigate with shell command: {make_cmd}')
                    log.warning(f'Warning: Compilation of {first_bench} failed')
                    succeeded = False
                else:
                    log.debug(f'Compilation of {first_bench} successful')
                    print("OK")
            else :
                # Split compilation of Pip and benchmark app
                # Compile benchmark app
                res_bench_clean = subprocess.run(
                        ["make", "-s", "-C", pip_app_dir, "cleanbench-soft"],
                        capture_output=True,
                    )
                res_bench = subprocess.run(
                        ["make", "-s", "-C", pip_app_dir, f'BENCH_NAME={first_bench}'],
                        capture_output=True,
                    )
                # Compile Pip and link with benchmark app
                res_pip_clean = subprocess.run(
                        ["make", "-s", "clean-soft"],
                        capture_output=True,
                    )
                res_pip = subprocess.run(
                        ["make", "-s", "all"],
                        capture_output=True,
                    )
                res_link = subprocess.run(
                        ["./root-partition-linker.sh", "pip.bin" , f'{pip_app_dir}/gen_benchmarks/{first_bench}/{first_bench}.bin'],
                        capture_output=True,
                    )
                if res_bench_clean.returncode != 0 or res_bench.returncode != 0\
                    or res_pip_clean.returncode != 0 or res_pip.returncode != 0 or res_link.returncode != 0:
                    print("***NOK***")
                    print(f'--> Investigate with shell commands: 1) make -C {pip_app_dir} BENCH_NAME={first_bench} \
                            2) make clean-soft\
                            3) make all\
                            4) ./root-partition-linker.sh pip.bin {pip_app_dir}/gen_benchmarks/{first_bench}/{first_bench}.bin')
                    log.warning('Warning: Compilation of benchmark "{first_bench}" failed'.format(bench=first_bench))
                    succeeded = False

                else:
                    log.debug(f'Compilation of benchmark {first_bench} successful')
                    log.info(first_bench)
                    print("OK")
                    elf_dir = "."
                    elf_path = "pip.elf"
        except subprocess.TimeoutExpired:
            log.warning(f'Warning: link of {first_bench}y timed out')
            succeeded = False

        if succeeded:
            print(f'Compiling Pip\'s static metrics using {first_bench}', end='...')
            try:
                pip_static_result_filename = os.path.join(bench_dir, f'results_static_pip_{first_bench}.txt')
                size_out_fd = open(pip_static_result_filename, 'w+')
                res = subprocess.run(
                    ["size", "-A", elf_path],
                    stdout=size_out_fd,
                    timeout=20
                )
                if res.returncode != 0:
                    print("***NOK***")
                    print(f'--> Investigate with shell command: size -A {elf_path}')
                    log.warning('Warning: Compilation of static metrics for pip failed')
                    succeeded = False

                else:
                    log.debug('Compilation of static metrics for pip successful')
                    size_out_fd.close()
                    static_results["Pip_size"] = {}
                    tot_pip_size = 0
                    size_out_fd = open(pip_static_result_filename, 'r')
                    lines = size_out_fd.readlines()
                    for line in lines:
                        if "_pip" in line:
                            " ".join(line.split())
                            words = line.split()
                            static_results["Pip_size"] |= { words[0] : words[1] }
                            tot_pip_size += int(words[1])
                    static_results["Pip_size"]["Total"] = tot_pip_size
                    # Write Pip's static metrics in file
                    pip_static_result_filename = os.path.join(results_pip_dir, 'results_static_pip.txt')
                    with open(pip_static_result_filename, 'w+') as fout:
                        json.dump(static_results, fout, indent=4, sort_keys=True)
                        fout.close()
                    print("OK -> written in %s" % pip_static_result_filename)

            except subprocess.TimeoutExpired:
                log.warning('Warning: link of benchmark pip-only timed out')
                succeeded = False
        else:
            print('ERROR: Not all benchmarks built successfully')

def static_metrics(results_dir, bench_dir, benchmarks, sequence):
    successful = True
    raw_section_data = {}
    raw_totals = {}
    rel_data = {}
    static_results = {}

    # invoke BenchIoT ROP gadgets and indirect calls
    #exec(open("benchmarks/benchiot_measure_static_flash_and_ram.py").read())
    benchiot_measure_static_flash_and_ram.measure_static(benchmarks)

    # Collect data
    for bench in benchmarks:
        raw_section_data[bench] = benchmark_size(bench, ALL_METRICS)
        raw_totals[bench] = sum(raw_section_data[bench].values())
        bench_path = os.path.join(bench_dir, bench)
        size_out = raw_section_data[bench]
        static_results[bench] = {}
        for f in os.listdir(bench_path):
            file_path = os.path.join(bench_path, f)
            if os.path.isfile(file_path):
                filename, file_extension = os.path.splitext(file_path)
                if file_extension == ".json":
                    with open(file_path) as fdata:
                        data = json.load(fdata)
                        static_out = size_out | {"ROP_gadgets" : int(data["ROP_gadgets"]), "Indirect_calls" : int(data["Indirect_calls"])}
                        static_results[bench] |= static_out
                if file_extension == ".bin":
                    static_results[bench] |= {"binsize" : (os.path.getsize(file_path))}
    res_rec_filename = 'results_static_' + str(sequence) + '.json'
    static_metrics_file = os.path.join(results_dir, res_rec_filename)
    with open(static_metrics_file, "w") as outfile:
        json.dump(static_results, outfile, indent=4, sort_keys=True)

    if successful:
        return raw_totals, rel_data

    # Otherwise failure return
    return [], []

""" Retrieve the dynamic analysis results is in the output string """
def decode_results(file_str):
    results = {}
    cycles = re.search('Ticks:(\d+)', file_str, re.S)
    if cycles:
        results["Cycles"] = cycles.group(1)
    priv_cycles = re.search('Privileged counter:(\d+)', file_str, re.S)
    if priv_cycles:
        results["Privileged_cycles_tot"] = priv_cycles.group(1)
    priv_cycles_test = re.search('Privileged counter after init:(\d+)', file_str, re.S)
    if priv_cycles_test:
        results["Privileged_cycles_test"] = priv_cycles.group(1)
    init_end_cycles = re.search('Init end counter:(\d+)', file_str, re.S)
    if init_end_cycles:
        results["Init_end_cycles"] = init_end_cycles.group(1)
    main_stack_usage = re.search('Main stack usage:(\d+)', file_str, re.S)
    if main_stack_usage:
        results["Main_stack_usage"] = main_stack_usage.group(1)
    app_stack_usage = re.search('App stack usage:(\d+)', file_str, re.S)
    if app_stack_usage:
        results["App_stack_usage"] = app_stack_usage.group(1)
    return results

def decode_results_energy(file_str):
    results = {}
    current_avg = re.search('Average current: (\d+\.\d+) uA', file_str, re.S)
    if current_avg:
        results["Current_mean"] = current_avg.group(1)
    current_max = re.search('Max current: (\d+\.\d+) uA', file_str, re.S)
    if current_max:
        results["Current_max"] = current_max.group(1)
    current_min = re.search('Min current: (\d+\.\d+) uA', file_str, re.S)
    if current_min:
        results["Current_min"] = current_min.group(1)
    current_std = re.search('Std current: (\d+\.\d+) uA', file_str, re.S)
    if current_std:
        results["Current_std"] = current_std.group(1)
    power_avg = re.search('Average power: (\d+\.\d+) mW', file_str, re.S)
    if power_avg:
        results["Power_mean"] = power_avg.group(1)
    energy_tot = re.search('Total energy consumption: (\d+\.\d+|\d+) mWs \(mJ\)', file_str, re.S)
    if energy_tot:
        results["Energy_tot"] = energy_tot.group(1)
    time = re.search('Total test duration: (\d+\.\d+) s', file_str, re.S)
    if time:
        results["Time_sec_energy"] = time.group(1)
    return results

""" Join the static and the dynamic results taking into account all runs """
def produce_recap(results_dir, benchmarks, sequence, runs):
    # Compute the baseline data we need
    baseline = {}

    recap_tot = {}
    for f in os.listdir(results_dir):
        file_path = os.path.join(results_dir, f)
        if os.path.isfile(file_path):
            filename, file_extension = os.path.splitext(file_path)
            # read static
            res_static_filename = "results_static_" + str(sequence)
            if file_extension == ".json" and os.path.basename(filename) == res_static_filename:
                with open(file_path) as fstatics:
                    static_data = json.load(fstatics)

            res_dyn_filename = "results_dynamic_" + str(sequence)
            if file_extension == ".json" and os.path.basename(filename) == res_dyn_filename:
                with open(file_path) as fdynamics:
                    dynamic_data_all = json.load(fdynamics)
                    dynamic_data = {}
                    # Average, min, max
                    for bench in dynamic_data_all:
                        recap_tot[bench] = {}
                        deployment_time_data = {"average" : 0, "min" : sys.maxsize, "max" : 0 , "var" : 0}
                        test_cycles_data = {"average" : 0, "min" : sys.maxsize, "max" : 0 , "var" : 0}
                        priv_cycles_data = {"average" : 0, "min" : sys.maxsize, "max" : 0 , "var" : 0}
                        priv_cycles_test_data = {"average" : 0, "min" : sys.maxsize, "max" : 0 , "var" : 0}
                        current_data = {"average" : 0, "min" : sys.maxsize, "max" : 0 , "var" : 0}
                        power_data = {"average" : 0, "min" : sys.maxsize, "max" : 0 , "var" : 0}
                        energy_data = {"average" : 0, "min" : sys.maxsize, "max" : 0 , "var" : 0}
                        cycles_average = 0
                        cycles_min = sys.maxsize
                        cycles_max = 0
                        cycles_var = 0
                        main_stack_average = 0
                        main_stack_min = sys.maxsize
                        main_stack_max = 0
                        main_stack_var = 0
                        app_stack_average = 0
                        app_stack_min = sys.maxsize
                        app_stack_max = 0
                        app_stack_var = 0
                        for run_nb in dynamic_data_all[bench]:
                            run = dynamic_data_all[bench][run_nb]
                            run_cycles = run["Cycles"]
                            cycles_average += run_cycles
                            if cycles_max < run_cycles:
                                cycles_max = run_cycles
                            if cycles_min > run_cycles:
                                cycles_min = run_cycles
                            run_main_stack = run["Main_stack_usage"]
                            main_stack_average += run_main_stack
                            if main_stack_max < run_main_stack:
                                main_stack_max = run_main_stack
                            if main_stack_min > run_main_stack:
                                main_stack_min = run_main_stack
                            run_app_stack = run["App_stack_usage"]
                            app_stack_average += run_app_stack
                            if app_stack_max < run_app_stack:
                                app_stack_max = run_app_stack
                            if app_stack_min > run_app_stack:
                                app_stack_min = run_app_stack
                            deployment_time = run["Deployment_time_sec"]
                            deployment_time_data["average"] += deployment_time
                            if deployment_time_data["max"] < deployment_time:
                                deployment_time_data["max"] = deployment_time
                            if deployment_time_data["min"] > deployment_time:
                                deployment_time_data["min"] = deployment_time
                            test_cycles = run["Test_cycles"]
                            test_cycles_data["average"] += test_cycles
                            if test_cycles_data["max"] < test_cycles:
                                test_cycles_data["max"] = test_cycles
                            if test_cycles_data["min"] > test_cycles:
                                test_cycles_data["min"] = test_cycles
                            current = run["Current_mean"]
                            current_data["average"] += current
                            if current_data["max"] < current:
                                current_data["max"] = current
                            if current_data["min"] > current:
                                current_data["min"] = current
                            power = run["Power_mean"]
                            power_data["average"] += power
                            if power_data["max"] < power:
                                power_data["max"] = power
                            if power_data["min"] > power:
                                power_data["min"] = power
                            energy = run["Energy_tot"]
                            energy_data["average"] += energy
                            if energy_data["max"] < energy:
                                energy_data["max"] = energy
                            if energy_data["min"] > energy:
                                energy_data["min"] = energy
                            if "pip" in sequence:
                                # privileged cycles tot
                                priv_cycles = run["Privileged_cycles_tot_ratio"]
                                priv_cycles_data["average"] += priv_cycles
                                if priv_cycles_data["max"] < priv_cycles:
                                    priv_cycles_data["max"] = priv_cycles
                                if priv_cycles_data["min"] > priv_cycles:
                                    priv_cycles_data["min"] = priv_cycles
                                # privileged cycles after init
                                priv_cycles_test = run["Privileged_cycles_test_ratio"]
                                priv_cycles_test_data["average"] += priv_cycles_test
                                if priv_cycles_test_data["max"] < priv_cycles_test:
                                    priv_cycles_test_data["max"] = priv_cycles_test
                                if priv_cycles_test_data["min"] > priv_cycles_test:
                                    priv_cycles_test_data["min"] = priv_cycles_test
                        cycles_average /= runs
                        main_stack_average /= runs
                        app_stack_average /= runs
                        deployment_time_data["average"] /= runs
                        test_cycles_data["average"] /= runs
                        priv_cycles_data["average"] /= runs
                        priv_cycles_test_data["average"] /= runs
                        current_data["average"] /= runs
                        power_data["average"] /= runs
                        energy_data["average"] /= runs
                        # Variance
                        for run_nb in dynamic_data_all[bench]:
                            run = dynamic_data_all[bench][run_nb]
                            cycles_var += (run["Cycles"]-cycles_average)**2
                            main_stack_var += (run["Main_stack_usage"]-main_stack_average)**2
                            app_stack_var += (run["App_stack_usage"]-app_stack_average)**2
                            deployment_time_data["var"] += (run["Deployment_time_sec"]-deployment_time_data["average"])**2
                            test_cycles_data["var"] += (run["Test_cycles"]-test_cycles_data["average"])**2
                            current_data["var"] += (run["Current_mean"]-current_data["average"])**2
                            power_data["var"] += (run["Power_mean"]-power_data["average"])**2
                            energy_data["var"] += (run["Energy_tot"]-energy_data["average"])**2
                            if "pip" in sequence:
                                priv_cycles_data["var"] += (run["Privileged_cycles_tot_ratio"]-priv_cycles_data["average"])**2
                                priv_cycles_test_data["var"] += (run["Privileged_cycles_test_ratio"]-priv_cycles_test_data["average"])**2
                        cycles_var /= runs
                        main_stack_var /= runs
                        app_stack_var /= runs
                        priv_cycles_data["var"] /= runs
                        priv_cycles_test_data["var"] /= runs
                        deployment_time_data["var"] /= runs
                        test_cycles_data["var"] /= runs
                        current_data["var"] /= runs
                        power_data["var"] /= runs
                        energy_data["var"] /= runs
                        # Full results
                        dynamic_data[bench] = { 'Cycles_average': cycles_average,
                                                'Cycles_min': cycles_min,
                                                'Cycles_max': cycles_max,
                                                'Cycles_var': cycles_var,
                                                'Time_sec_average': float(int(cycles_average)) / float(64000000), # TODO: set real cpu frequency
                                                'Main_stack_average': main_stack_average,
                                                'Main_stack_min': main_stack_min,
                                                'Main_stack_max': main_stack_max,
                                                'Main_stack_var': main_stack_var,
                                                'App_stack_average': app_stack_average,
                                                'App_stack_min': app_stack_min,
                                                'App_stack_max': app_stack_max,
                                                'App_stack_var': app_stack_var,
                                                'Deployment_time_sec_average': deployment_time_data["average"],
                                                'Deployment_time_sec_min': deployment_time_data["min"],
                                                'Deployment_time_sec_max': deployment_time_data["max"],
                                                'Deployment_time_sec_var': deployment_time_data["var"],
                                                'Test_cycles_average': test_cycles_data["average"],
                                                'Test_cycles_min': test_cycles_data["min"],
                                                'Test_cycles_max': test_cycles_data["max"],
                                                'Test_cycles_var': test_cycles_data["var"],
                                                'Current_average': current_data["average"],
                                                'Current_min': current_data["min"],
                                                'Current_max': current_data["max"],
                                                'Current_var': current_data["var"],
                                                'Power_average': power_data["average"],
                                                'Power_min': power_data["min"],
                                                'Power_max': power_data["max"],
                                                'Power_var': power_data["var"],
                                                'Energy_tot_average': energy_data["average"],
                                                'Energy_tot_min': energy_data["min"],
                                                'Energy_tot_max': energy_data["max"],
                                                'Energy_tot_var': energy_data["var"]
                                             }
                        if "pip" in sequence:
                            dynamic_data[bench] |= {
                                                    'Privileged_cycles_tot_ratio_average': priv_cycles_data["average"],
                                                    'Privileged_cycles_tot_ratio_min': priv_cycles_data["min"],
                                                    'Privileged_cycles_tot_ratio_max': priv_cycles_data["max"],
                                                    'Privileged_cycles_tot_ratio_var': priv_cycles_data["var"],
                                                    'Privileged_cycles_test_ratio_average': priv_cycles_test_data["average"],
                                                    'Privileged_cycles_test_ratio_min': priv_cycles_test_data["min"],
                                                    'Privileged_cycles_test_ratio_max': priv_cycles_test_data["max"],
                                                    'Privileged_cycles_test_ratio_var': priv_cycles_test_data["var"]
                                                    }
    for bench in benchmarks:
        recap_tot[bench]["Static"] = static_data[bench]
        recap_tot[bench]["Dynamic"] = dynamic_data[bench]
    res_rec_filename = 'results_recap_' + str(sequence) + '.json'
    recap_file = os.path.join(results_dir, res_rec_filename)
    with open(recap_file, "w") as outfile:
        json.dump(recap_tot, outfile, indent=4, sort_keys=True)


""" Generic function to start a process"""
def start_process(func, name=None, args = []):
    proc = multiprocessing.Process(target=func, name=name, args=args)
    proc.start()
    return proc

""" Start a JLinkGDBServer """
def init_gdbserver(bench_name):
    try:
        process = subprocess.Popen(
                    ["/opt/SEGGER/JLink/JLinkGDBServer", "-if", "swd", "-device", "nRF52840_xxAA", #"nRF52832_xxAA",
                    "-select", "USB=683957092",
                    "-endian", "little", "-speed", "1000", "-port", "2331", "-swoport", "2332",
                    "-telnetport", "2333", "-vd", "-ir", "-localhostonly", "1", "-singlerun", "-strict",
                    "-timeout", "0", "-nogui"],
                    #capture_output=True, # doesn't work
                    stdin=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    stdout=subprocess.DEVNULL
                    #timeout=gp['timeout'],
                )
    except BaseException:
        print("Error in init_gdbserver")

""" Start a telnet to retrive the semihosting output"""
def init_telnet(bench_name, run, sequence):
    succeeded = True
    output = ""
    try:
        tn = telnetlib.Telnet("localhost", 2333)
        #tn.set_debuglevel(1)
        output = tn.read_all()
        tn.close()
    except ConnectionRefusedError:
        print(f'Telnet error: Run of {bench_name} timed out.')
        succeeded = False
    except BaseException:
        print(f'Telnet error: {bench_name} failed')
        succeeded = False
    # Dump the data if successful
    outfile = os.path.join("generated/benchmarks", bench_name, f'{sequence}_{bench_name}_{run}.txt')
    if succeeded:
        with open(outfile, "w") as fileh:
            linecount = 0
            for line in output.decode('utf-8').splitlines(keepends=True):
               # if not 'All benchmarks ' + desc + ' successfully' in line:
                fileh.writelines(line)
                linecount=linecount+1
            fileh.close()
            print("Result written in %s" % outfile)
            if linecount == 1:
                print("***ERROR: " + bench_name + " failed, check gdbserver connection (is the device up and running? or try to augment sleep delay?)")
    else:
        print("***ERROR: " + bench_name + " failed, check gdbserver connection (is the device up and running? or try to augment sleep delay)")
        with open(outfile, 'w') as fileh:
            fileh.write("NOK")
            fileh.close()

""" Flash and launch """
def init_gdb(bench_name, results):
    try:
        pyscript_cmd = f' py arg0 = \"{bench_name}\"'
        #print("Using %s" % pyscript_cmd)
        res = subprocess.run(
                    ["arm-none-eabi-gdb", "--batch", "-ex", pyscript_cmd, "-x", "benchmarks/gdb_connect_flash_run.py"],
                    #timeout=10,
                    capture_output=True,
                )
        #print("the commandline is {}".format(res.args))
    except subprocess.TimeoutExpired:
        print(f'Warning: Run of GDB {bench_name} timed out.')
        print("NOK***")
        results = 0
        return
    except BaseException:
        print(f'GDB error: {bench_name} failed. Investigate with command: arm-none-eabi-gdb --batch -ex \'py arg0="{bench_name}"\' -x benchmarks/gdb_connect_flash_run.py ')
        print("NOK***")
        results = 0
        return
    print("OK")
    results = 1

def energy_monitoring(bench_name, run, sequence, time):
    try:
        outfile = os.path.join("generated/benchmarks", bench_name, f'{sequence}_{bench_name}_{run}_energy.csv')
        res = subprocess.run(
                    ["../../nRFConnect/ppk_api/ppk/bin/python3", # run in virtual env with pynrfjprog version 9.8.1
                    "../../nRFConnect/ppk_api/main.py",
                    "-s", "683926732", # connect to ppk
                     "-p", # reset board
                     "-a", f'{time}', # benchmark time
                     "-o", f'{outfile}', "-z", "-v"], # output csv + graph with same name
                    #timeout=10,
                    capture_output=False,
                )

    except BaseException:
        print(f'PPK error: {bench_name} failed. Investigate with command: ~/nRFConnect/ppk_api/ppk/bin/python3 ~/nRFConnect/ppk_api/main.py -s 683926732 -p -a 30 -o trig_data.csv -z -v')
        print("NOK***")
        return
    print("OK")

from threading import Timer

class RepeatTimer(Timer):
    def run(self):
        while not self.finished.wait(self.interval):
            self.function(*self.args, **self.kwargs)

def repeat_func(start):
    #print("-%s" % (str(datetime.timedelta(seconds=(time.time()-start)))))
    print(".", end='',flush=True)


def run_dynamic_metrics(benchmarks, sequence, runs, energy_analysis):
    print("\n-----> Collecting dynamic data:")

    for bench in benchmarks:
        print(f'\n***Launching {sequence} benchmark for {bench}***')
        for run in range(1, runs+1):
            # Start timer thread
            start_run = time.time()
            timer = RepeatTimer(3, repeat_func, args=[time.time()])
            timer.start()

            print("***RUN "+ str(run) + "/" + str(runs) + "***")
            print("Starting GDBServer", end='...')
            gdbs = start_process(init_gdbserver, args=[bench])
            print("OK")
            print("Starting Telnet", end='...')
            time.sleep(0.5) # wait GDBServer is up
            tn = start_process(init_telnet, args=[bench, run, sequence])
            print("OK")
            print("Flashing and running %s" % bench, end="...")
            results = 0
            gdb = start_process(init_gdb, args=[bench, results])
            gdb.join()
            tn.join()
            gdbs.join()
            end_run = time.time()
            delta = end_run-start_run
            print("Run %s ended in %s (HH:MM:SS)" % (run, str(datetime.timedelta(seconds=(delta)))))
            if energy_analysis:
                # Start an energy analysis on the flashed firmware (can't monitor at the same time because of debugger)
                ppk = start_process(energy_monitoring, args=[bench, run, sequence, round(delta)])
                ppk.join()
            timer.cancel()
            # All threads have returned

def analyse_dynamic_metrics(results_dir, bench_dir, benchmarks, sequence):
    dynamic_results = {}
    # Analyse all dynamic outputs
    for bench in benchmarks:
        dir_path = os.path.join(bench_dir, bench)
        for f in os.listdir(dir_path):
            file_path = os.path.join(dir_path, f)
            if os.path.isfile(file_path):
                filename, file_extension = os.path.splitext(file_path)
                if file_extension == ".txt" and sequence in filename and "energy" not in filename:
                    with open(file_path) as fdata:
                        read_data = fdata.read()
                        data = decode_results(read_data)
                        cycles = int(data["Cycles"])
                        init_end_cycles = int(data["Init_end_cycles"])
                        test_cycles = cycles - init_end_cycles
                        priv_cycles = int(data["Privileged_cycles_tot"])
                        priv_cycles_test = int(data["Privileged_cycles_test"])
                        file_name = re.search('.*_(\D+\d*)_(\d+).*$', f, re.S)
                        if file_name:
                            run_res_out = { 'Cycles': cycles,
                                            'Time_sec': float(cycles) / float(64000000), # TODO: set real cpu frequency
                                            'Main_stack_usage': int(data["Main_stack_usage"]),
                                            'App_stack_usage': int(data["App_stack_usage"]),
                                            'Privileged_cycles_tot' : priv_cycles,
                                            'Privileged_cycles_test' : priv_cycles_test,
                                            'Deployment_time_sec' : float(init_end_cycles) / float(64000000), # TODO: set real cpu frequency
                                            'Test_cycles' : test_cycles,
                                            'Privileged_cycles_tot_ratio' : float(priv_cycles)/float(cycles),
                                            'Privileged_cycles_test_ratio' : float(priv_cycles_test)/float(test_cycles)
                                        }
                            '''if "pip" in sequence:
                                run_res_out |= {
                                    'Privileged_cycles_tot_ratio' : float(priv_cycles)/float(cycles),
                                    'Privileged_cycles_test_ratio' : float(priv_cycles_test)/float(cycles-init_end_cycles)
                                }
                            '''
                            run_nb = int(file_name.group(2))
                            if file_name.group(1) not in dynamic_results:
                                dynamic_results[file_name.group(1)] = {}
                            if run_nb not in dynamic_results[file_name.group(1)]:
                                dynamic_results[file_name.group(1)][run_nb] = {}
                            dynamic_results[file_name.group(1)][run_nb] |= run_res_out
                        else:
                            print("***Error: Didn't find any output for " + f)
                            sys.exit(1)
                if file_extension == ".csv" and sequence in filename:
                    out_energy_file_path = f'{filename}_analysis.txt'
                    out_energy_file = open(out_energy_file_path, 'w')
                    res = subprocess.run(
                                ["python3",
                                "benchmarks/energy_csv_analysis.py",
                                f'{file_path}'],
                                #timeout=10,
                                stdout=out_energy_file,
                            )
                    out_energy_file.close()

                    if res.returncode != 0:
                        print("***NOK***")
                        print(f'Investigate with command: python3 benchmarks/energy_csv_analysis.py {file_path}')
                        return 0
                    else:
                        out_energy_file = open(out_energy_file_path, 'r')
                        with open(out_energy_file_path, 'r') as fdata:
                            read_data = fdata.read()
                            data = decode_results_energy(read_data)
                            file_name = re.search('.*_(\D+\d*)_(\d+).*$', f, re.S)
                            if file_name:
                                run_res_out = { 'Time_test_sec': float(data["Time_sec_energy"]),
                                                'Current_mean': float(data["Current_mean"]),
                                                'Current_max' : float(data["Current_max"]),
                                                'Current_min' : float(data["Current_min"]),
                                                'Current_std' : float(data["Current_std"]),
                                                'Power_mean' : float(data["Power_mean"]),
                                                'Energy_tot' : float(data["Energy_tot"])
                                            }
                                run_nb = int(file_name.group(2))
                                if file_name.group(1) not in dynamic_results:
                                    dynamic_results[file_name.group(1)] = {}
                                if run_nb not in dynamic_results[file_name.group(1)]:
                                    dynamic_results[file_name.group(1)][run_nb] = {}
                                dynamic_results[file_name.group(1)][run_nb] |= run_res_out
                            else:
                                print("***Error: Didn't find any output for " + f)
                                sys.exit(1)
    res_dyn_filename = 'results_dynamic_' + str(sequence) + '.json'
    baseline_file = os.path.join(results_dir, res_dyn_filename)
    with open(baseline_file, "w") as outfile:
        json.dump(dynamic_results, outfile, indent=4, sort_keys=True)

def compare_baseline(results_dir, sequence, baseline_name):
    # TODO: check variance is small
    if "bench-baseline" in sequence: # reject "bench-baseline-w-systick" and "bench-baseline-wo-systick":
        return
    print("Producing comparison report for %s" % sequence, end="...")
    rel_baseline_data = {}
    rel_total_recap_mean = {}
    # Open baseline file
    res_recap_baseline_filename = f'results_recap_{baseline_name}.json'
    recap_file = os.path.join(results_dir, res_recap_baseline_filename)
    with open(recap_file) as frecapbase:
        b_data = json.load(frecapbase)
        # Open baseline file
        '''res_recap_baseline_wo_systick_filename = 'results_recap_bench-baseline-wo-systick.json'
        recap_file = os.path.join(results_dir, res_recap_baseline_wo_systick_filename)
        with open(recap_file) as frecapbase:
            b_wo_systick_data = json.load(frecapbase)
        '''
        # open sequence file
        res_recap_filename = 'results_recap_' + str(sequence) + '.json'
        recap_file = os.path.join(results_dir, res_recap_filename)
        with open(recap_file) as frecap:
            data = json.load(frecap)
            for bench in data:
                # Load average on ALL benchmark runs
                base_cycles = b_data[bench]["Dynamic"]["Cycles_average"]
                sequence_cycles = data[bench]["Dynamic"]["Cycles_average"]
                base_time = b_data[bench]["Dynamic"]["Time_sec_average"]
                sequence_time = data[bench]["Dynamic"]["Time_sec_average"]
                base_test_cycles = b_data[bench]["Dynamic"]["Test_cycles_average"]
                sequence_test_cycles = data[bench]["Dynamic"]["Test_cycles_average"]
                base_main_stack = b_data[bench]["Dynamic"]["Main_stack_average"]
                sequence_main_stack = data[bench]["Dynamic"]["Main_stack_average"]
                base_app_stack = b_data[bench]["Dynamic"]["App_stack_average"]
                sequence_app_stack = data[bench]["Dynamic"]["App_stack_average"]
                #base_privileged_cycles = b_data[bench]["Dynamic"]["Privileged_cycles_test"] # 100% we don't care
                sequence_privileged_cycles_tot_ratio = data[bench]["Dynamic"]["Privileged_cycles_tot_ratio_average"]
                sequence_privileged_cycles_test_ratio = data[bench]["Dynamic"]["Privileged_cycles_test_ratio_average"]
                base_current = b_data[bench]["Dynamic"]["Current_average"]
                sequence_current = data[bench]["Dynamic"]["Current_average"]
                base_power = b_data[bench]["Dynamic"]["Power_average"]
                sequence_power = data[bench]["Dynamic"]["Power_average"]
                base_energy = b_data[bench]["Dynamic"]["Energy_tot_average"]
                sequence_energy = data[bench]["Dynamic"]["Energy_tot_average"]
                base_indirect_calls = b_data[bench]["Static"]["Indirect_calls"]
                sequence_indirect_calls = data[bench]["Static"]["Indirect_calls"]
                base_gadgets = b_data[bench]["Static"]["ROP_gadgets"]
                sequence_gadgets = data[bench]["Static"]["ROP_gadgets"]
                # Compute relative compared to baseline
                rel_baseline_data[bench] = {"Dynamic" : {
                                                            "Cycles_rel_average" : sequence_cycles*100/base_cycles if base_cycles != 0 else sequence_cycles,
                                                            "Cycles_base_var" : b_data[bench]["Dynamic"]["Cycles_var"],
                                                            f'Cycles_{sequence}_var' : int(data[bench]["Dynamic"]["Cycles_var"]),
                                                            "Time_sec_rel_average" : sequence_time*100/base_time if base_time != 0 else sequence_time,
                                                            #"Time_ms_base_var" : b_data[bench]["Dynamic"]["Time_ms_var"],
                                                            #f'Time_ms_{sequence}_var' : data[bench]["Dynamic"]["Time_ms_var"],
                                                            "Main_stack_base": base_main_stack,
                                                            "Main_stack_base_var": b_data[bench]["Dynamic"]["Main_stack_var"],
                                                            f'Main_stack_{sequence}_var' : data[bench]["Dynamic"]["Main_stack_var"],
                                                            f'Main_stack_{sequence}' : sequence_main_stack,
                                                            "App_stack_rel_average": sequence_app_stack*100/base_app_stack if base_app_stack != 0 else sequence_app_stack,
                                                            "App_stack_base_var": b_data[bench]["Dynamic"]["App_stack_var"],
                                                            f'App_stack_{sequence}_var' : data[bench]["Dynamic"]["App_stack_var"],
                                                            "Privileged_cycles_tot_ratio_rel_average":  sequence_privileged_cycles_tot_ratio,
                                                            "Privileged_cycles_tot_ratio_base_var": 0, # baseline is privileged so 100% during the benchmark time
                                                            f'Privileged_cycles_tot_ratio_{sequence}_var' : data[bench]["Dynamic"]["Privileged_cycles_tot_ratio_var"],
                                                            "Privileged_cycles_test_ratio_rel_average":  sequence_privileged_cycles_test_ratio,
                                                            "Privileged_cycles_test_ratio_base_var": 0, # baseline is privileged so 100% during the benchmark time
                                                            f'Privileged_cycles_test_ratio_{sequence}_var' : data[bench]["Dynamic"]["Privileged_cycles_test_ratio_var"],
                                                            "Test_cycles_rel_average":  sequence_test_cycles*100/base_test_cycles if base_test_cycles != 0 else sequence_test_cycles,
                                                            "Test_cycles_base_var" : b_data[bench]["Dynamic"]["Test_cycles_var"],
                                                            f'Test_cycles_{sequence}_var' : int(data[bench]["Dynamic"]["Test_cycles_var"]),
                                                            "Current_rel_average" : sequence_current*100/base_current if base_current != 0 else sequence_current,
                                                            "Current_base_var" : b_data[bench]["Dynamic"]["Current_var"],
                                                            f'Current_{sequence}_var' : int(data[bench]["Dynamic"]["Current_var"]),
                                                            "Power_rel_average" : sequence_power*100/base_power if base_power != 0 else sequence_power,
                                                            "Power_base_var" : b_data[bench]["Dynamic"]["Power_var"],
                                                            f'Power_{sequence}_var' : int(data[bench]["Dynamic"]["Power_var"]),
                                                            "Energy_tot_rel" : sequence_energy*100/base_energy if base_energy != 0 else sequence_energy,
                                                            "Energy_tot_base_var" : b_data[bench]["Dynamic"]["Energy_tot_var"],
                                                            f'Energy_tot_{sequence}_var' : int(data[bench]["Dynamic"]["Energy_tot_var"]),
                                                        },
                                            "Static" : {
                                                            "Indirect_calls_overhead" : sequence_indirect_calls - base_indirect_calls,
                                                            "ROP_gadgets_overhead": sequence_gadgets - base_gadgets
                                                        }
                                            }
                # Compute global stats on ALL benchmarks of all benchmark runs
                if "Cycles_rel_total_mean" not in rel_total_recap_mean \
                    or "Test_cycles_rel_total_mean" not in rel_total_recap_mean \
                    or "Privileged_cycles_tot_ratio_rel_total_mean" not in rel_total_recap_mean \
                    or "Privileged_cycles_test_ratio_rel_total_mean" not in rel_total_recap_mean \
                    or "Time_sec_rel_average" not in rel_total_recap_mean \
                    or "Indirect_calls_overhead" not in rel_total_recap_mean \
                    or "ROP_gadgets_overhead" not in rel_total_recap_mean \
                    or "Current_rel_total_mean" not in rel_total_recap_mean \
                    or "Power_rel_total_mean" not in rel_total_recap_mean \
                    or "Energy_tot_rel_total_mean" not in rel_total_recap_mean :
                    rel_total_recap_mean["Cycles_rel_total_mean"] = []
                    rel_total_recap_mean["Test_cycles_rel_total_mean"] = []
                    rel_total_recap_mean["Privileged_cycles_tot_ratio_rel_total_mean"] = []
                    rel_total_recap_mean["Privileged_cycles_test_ratio_rel_total_mean"] = []
                    rel_total_recap_mean["Time_sec_rel_total_mean"] = []
                    rel_total_recap_mean["Indirect_calls_overhead_total_mean"] = []
                    rel_total_recap_mean["ROP_gadgets_overhead_total_mean"] = []
                    rel_total_recap_mean["Current_rel_total_mean"] = []
                    rel_total_recap_mean["Power_rel_total_mean"] = []
                    rel_total_recap_mean["Energy_tot_rel_total_mean"] = []
                    #rel_total_recap_mean["bss_rel_total_mean"] = []
                    #rel_total_recap_mean["data_rel_total_mean"] = []
                    #rel_total_recap_mean["rodata_rel_total_mean"] = []
                    #rel_total_recap_mean["text_rel_total_mean"] = []
                    #rel_total_recap_mean["binsize_rel_total_mean"] = []
                rel_total_recap_mean["Cycles_rel_total_mean"].append(rel_baseline_data[bench]["Dynamic"]["Cycles_rel_average"])
                rel_total_recap_mean["Test_cycles_rel_total_mean"].append(rel_baseline_data[bench]["Dynamic"]["Test_cycles_rel_average"])
                rel_total_recap_mean["Privileged_cycles_tot_ratio_rel_total_mean"].append(rel_baseline_data[bench]["Dynamic"]["Privileged_cycles_tot_ratio_rel_average"])
                rel_total_recap_mean["Privileged_cycles_test_ratio_rel_total_mean"].append(rel_baseline_data[bench]["Dynamic"]["Privileged_cycles_test_ratio_rel_average"])
                rel_total_recap_mean["Time_sec_rel_total_mean"].append(rel_baseline_data[bench]["Dynamic"]["Time_sec_rel_average"])
                rel_total_recap_mean["Current_rel_total_mean"].append(rel_baseline_data[bench]["Dynamic"]["Current_rel_average"])
                rel_total_recap_mean["Power_rel_total_mean"].append(rel_baseline_data[bench]["Dynamic"]["Power_rel_average"])
                rel_total_recap_mean["Energy_tot_rel_total_mean"].append(rel_baseline_data[bench]["Dynamic"]["Energy_tot_rel"])
                #rel_total_recap_mean["Main_stack_base_total_mean"].append(rel_baseline_data[bench]["Dynamic"]["Main_stack_base"])
                #rel_total_recap_mean["Main_stack_rel_total_mean"].append(rel_baseline_data[bench]["Dynamic"]["Main_stack_rel_average"])
                #rel_total_recap_mean["App_stack_rel_total_mean"].append(rel_baseline_data[bench]["Dynamic"]["App_stack_rel_average"])
                rel_total_recap_mean["Indirect_calls_overhead_total_mean"].append(rel_baseline_data[bench]["Static"]["Indirect_calls_overhead"])
                rel_total_recap_mean["ROP_gadgets_overhead_total_mean"].append(rel_baseline_data[bench]["Static"]["ROP_gadgets_overhead"])
                #rel_total_recap_mean["bss_rel_total_mean"].append(rel_baseline_data[bench]["Static"]["bss_rel"])
                #rel_total_recap_mean["data_rel_total_mean"].append(rel_baseline_data[bench]["Static"]["data_rel"])
                #rel_total_recap_mean["rodata_rel_total_mean"].append(rel_baseline_data[bench]["Static"]["rodata_rel"])
                #rel_total_recap_mean["text_rel_total_mean"].append(rel_baseline_data[bench]["Static"]["text_rel"])
                #rel_total_recap_mean["binsize_rel_total_mean"].append(rel_baseline_data[bench]["Static"]["binsize_rel"])
    # relative mean for each metric
    rel_baseline_data["Total"] = { "Cycles_rel_average_tot" :  mean(rel_total_recap_mean["Cycles_rel_total_mean"]),
                                    "Test_cycles_rel_average_tot" :  mean(rel_total_recap_mean["Test_cycles_rel_total_mean"]),
                                    #"Main_stack_rel_average_tot" :  mean(rel_total_recap_mean["Main_stack_rel_total_mean"]),
                                    #"App_stack_rel_average_tot" :  mean(rel_total_recap_mean["App_stack_rel_total_mean"]),
                                    "Current_rel_average_tot" :  mean(rel_total_recap_mean["Current_rel_total_mean"]),
                                    "Power_rel_average_tot" :  mean(rel_total_recap_mean["Power_rel_total_mean"]),
                                    "Energy_tot_rel_average_tot" :  mean(rel_total_recap_mean["Energy_tot_rel_total_mean"]),
                                    "Indirect_calls_rel_average_tot" :  mean(rel_total_recap_mean["Indirect_calls_overhead_total_mean"]),
                                    "ROP_gadgets_rel_average_tot" :  mean(rel_total_recap_mean["ROP_gadgets_overhead_total_mean"]),
                                    "Privileged_cycles_tot_ratio_rel_average_tot" :  mean(rel_total_recap_mean["Privileged_cycles_tot_ratio_rel_total_mean"]),
                                    "Privileged_cycles_test_rel_average_tot" :  mean(rel_total_recap_mean["Privileged_cycles_test_ratio_rel_total_mean"])
                                    }
    res_compare_filename = 'results_baseline_compare_' + str(sequence) + '.json'
    compare_file = os.path.join(results_dir, res_compare_filename)
    with open(compare_file, "w") as outfile:
        json.dump(rel_baseline_data, outfile, indent=4, sort_keys=True)
    print("OK -> written in %s" % compare_file)


""" Build and run the benchmarks, then analyse the results"""
def main():
    # Start benchmark time measurement
    start = time.time()
    # Establish the root directory of the repository, since we know this file is
    # in that directory.
    gp['rootdir'] = os.path.abspath(os.path.dirname(__file__))

    bench_dir = "generated/benchmarks"
    results_dir = os.path.join(bench_dir,"results_sequences")
    results_pip_dir = os.path.join(bench_dir,"results_pip")

    runs = 1

    do_all = False # do not include energy analysis
    build_only= False
    dynamic_analysis_only = False
    dynamic_analysis_only_no_run = False
    static_analysis_only = False
    pip_static_analysis_only = False
    recap_only = False
    baseline_compare_only = False
    energy_analysis = False

    args = sys.argv[1:]

    if(len(sys.argv)==1 or (len(sys.argv)==2 and "energy" in args)):
        do_all = True
        if "energy" in args:
            energy_analysis = True
    else:
        for arg in args:
            if "build" in arg:
                build_only= True
            if "dynamic" in arg:
                if "no-run" in arg:
                    dynamic_analysis_only_no_run = True
                else:
                    dynamic_analysis_only = True
            if "static" in arg:
                static_analysis_only = True
            if "pip-metrics" in arg:
                pip_static_analysis_only = True
            if "recap" in arg:
                recap_only = True
            if "compare" in arg:
                baseline_compare_only = True
            if "energy" in arg:
                energy_analysis = True

    if do_all:
        if(os.path.isdir(results_dir)):
            shutil.rmtree(results_dir) # erase dir
        Path(results_dir).mkdir(parents=True, exist_ok=True) # create dir
        if(os.path.isdir(results_pip_dir)):
            shutil.rmtree(results_pip_dir) # erase dir
        Path(results_pip_dir).mkdir(parents=True, exist_ok=True) # create dir

    baseline_name = "bench-baseline-priv-w-systick"
    pip_app_dir = "../pip-mpu-benchmark"
    # Find the benchmarks
    #benchmarks = []
    benchmarks = find_benchmarks()

    benchmarks.remove('matmult-int')

    benchmarks.remove('md5sum')
    benchmarks.remove('nettle-aes')
    benchmarks.remove('picojpeg')
    benchmarks.remove('ud')
    benchmarks.remove('tarfind')
    benchmarks.remove('st')
    benchmarks.remove('huffbench')

    # Not working with bench-pip-child
    benchmarks.remove('wikisort')

    # not working with bench-pip-root
    benchmarks.remove('cubic')
    benchmarks.remove('edn')
    benchmarks.remove('minver')
    benchmarks.remove('nbody')
    benchmarks.remove('nettle-sha256')
    benchmarks.remove('qrduino')
    benchmarks.remove('statemate')

    '''
    # working
    benchmarks.remove('aha-mont64')

    benchmarks.remove('crc32')





    benchmarks.remove('nsichneu')
    benchmarks.remove('primecount')


    '''

    benchmarks.remove('slre')
    benchmarks.remove('sglib-combined')


    #not working

    # snrs can be checked with the command "nrfjprog -i"
    with HighLevel.API('NRF52') as api:
        snrs = api.get_connected_probes()
        print(f'Connected boards SN: {snrs}')
        if len(snrs) == 1 and 683957092 in snrs:
            if energy_analysis:
                print("***ERROR: PPK not connected, energy analysis cannot be performed, stop")
                sys.exit(0)
        if len(snrs) == 1 and 683926732 in snrs:
            if energy_analysis:
                print("***ERROR: Board not detected, energy analysis cannot be performed, stop")
                sys.exit(0)
        if len(snrs) == 2 and not energy_analysis:
            # With the two boards connected, there is a risk of erasing the PPK HW by the benchmark FW
            # -> no issue if the boards are identified in the segger commands used later
            print("***Warning: risk of erasing connected PPK FW")

    #benchmarks = ['aha-mont64', 'crc32', 'cubic', 'edn', 'huffbench']
    print("benchmarks.py: Considered benchmarks: %s " % benchmarks)
    log_benchmarks(benchmarks)

    # Launch the benchmark batch in different scenarios (baseline, without the systick interrupt, with Pip...)
    # Always keep the baseline scenarios at first
    boot_sequences = [baseline_name, "bench-pip-root", "bench-pip-child"]# ["bench-baseline-priv-w-systick"] #, "bench-pip-root"]  # ["bench-pip-child"] # "bench-baseline-wo-systick",
    for sequence in boot_sequences:
        print("\n\n-----> Configuring sequence %s" % sequence, end="...")
        try:
            res = subprocess.run(
                ["./configure.sh", "--architecture=nrf52840", "--debugging-mode=semihosting",
                    f'--boot-sequence={sequence}'],
                capture_output=True,
            )
            if res.returncode != 0:
                print("***NOK***")
                print("Investigate with commands: ./configure.sh --architecture=nrf52840 --debugging-mode=semihosting --boot-sequence=%s" % sequence)
                succeeded = False

            else:
                log.debug('Configuration of sequence "{sequence}" successful'.format(sequence=sequence))
                print("OK")

        except subprocess.TimeoutExpired:
            log.warning('Warning: configuration of benchmark "{sequence}" timed out'.format(sequence=sequence))
            succeeded = False

        if do_all or build_only:
            # Track success
            successful = True
            for bench in benchmarks:
                print("Building " + bench, end='...')
                try:
                    if baseline_name in sequence:
                        # already compiled in bench_dir
                        res_clean = subprocess.run(
                                ["make", "cleanbench-soft", "-s", "BENCH_NAME=" + bench],
                                capture_output=True,
                            )
                        res = subprocess.run(
                                ["make", "-s", "all", "BENCH_NAME=" + bench],
                                capture_output=True,
                            )
                        if res_clean.returncode != 0 or res.returncode != 0:
                            print("***NOK***")
                            print("the commandline is {}".format(res.args))
                            print("the commandline is {}".format(res_clean.args))
                            print(f'--> Investigate with shell command: 1) make cleanbench-soft BENCH_NAME={bench} 2) make all BENCH_NAME={bench}')
                            log.warning('Warning: Compilation of benchmark "{bench}" failed'.format(bench=bench))
                            succeeded = False

                        else:
                            log.debug('Compilation of benchmark "{bench}" successful'.format(bench=bench))
                            log.info(bench)
                            print("OK")
                    else:
                        # Split compilation of Pip and benchmark app
                        # Compile benchmark app
                        res_bench_clean = subprocess.run(
                                ["make", "-s", "-C", pip_app_dir, "cleanbench-soft"],
                                capture_output=True,
                            )
                        res_bench = subprocess.run(
                                ["make", "-s", "-C", pip_app_dir, "BENCH_NAME=" + bench],
                                capture_output=True,
                            )
                        # Compile Pip and link with benchmark app
                        res_pip_clean = subprocess.run(
                                ["make", "-s", "clean-soft"],
                                capture_output=True,
                            )
                        res_pip = subprocess.run(
                                ["make", "-s", "all"],
                                capture_output=True,
                            )
                        res_link = subprocess.run(
                                ["./root-partition-linker.sh", "pip.bin" , f'{pip_app_dir}/gen_benchmarks/{bench}/{bench}.bin',
                                 f'{bench_dir}/{bench}/{bench}.elf'],
                                capture_output=True,
                            )
                        if res_bench_clean.returncode != 0 or res_bench.returncode != 0\
                            or res_pip_clean.returncode != 0 or res_pip.returncode != 0 or res_link.returncode != 0:
                            print("***NOK***")
                            print(f'--> Investigate with shell commands: 1) make -C {pip_app_dir} BENCH_NAME={bench} \
                                    2) make clean-soft\
                                    3) make all\
                                 4) ./root-partition-linker.sh pip.bin {pip_app_dir}/gen_benchmarks/{bench}/{bench}.bin {bench_dir}/{bench}/{bench}.elf')
                            log.warning('Warning: Compilation of benchmark "{bench}" failed'.format(bench=bench))
                            succeeded = False

                        else:
                            log.debug('Compilation of benchmark "{bench}" successful'.format(bench=bench))
                            log.info(bench)
                            print("OK")

                except subprocess.TimeoutExpired:
                    log.warning('Warning: link of benchmark "{bench}" timed out'.format(bench=bench))
                    succeeded = False

            if successful:
                log.info('All benchmarks built successfully')
            else:
                print('ERROR: Not all benchmarks built successfully')
                sys.exit(1)

        if do_all or dynamic_analysis_only:
            run_dynamic_metrics(benchmarks, sequence, runs, energy_analysis)

        if do_all or dynamic_analysis_only or dynamic_analysis_only_no_run:
            analyse_dynamic_metrics(results_dir, bench_dir, benchmarks, sequence)

        if do_all or static_analysis_only:
            static_metrics(results_dir, bench_dir, benchmarks, sequence)

        if do_all or recap_only:
            produce_recap(results_dir, benchmarks, sequence, runs)

        if do_all or baseline_compare_only:
            compare_baseline(results_dir, sequence, baseline_name)

    if do_all or pip_static_analysis_only:
        pip_static_metrics(results_pip_dir, bench_dir, pip_app_dir, benchmarks, boot_sequences)
    end = time.time()
    print("\n\nDONE in %s (HH:MM:SS): Nothing to do left" % str(datetime.timedelta(seconds=(end-start))))

# Make sure we have new enough Python and only run if this is the main package

check_python_version(3, 10)
if __name__ == '__main__':
    sys.exit(main())
