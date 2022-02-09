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
from pathlib import Path
import shutil
import json
import collections

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

def static_metrics(bench_dir, benchmarks):
    #baseline_file = os.path.join(results_dir, 'results_baseline.json')

    # Compute the baseline data we need
    baseline = {}

    successful = True
    raw_section_data = {}
    raw_totals = {}
    rel_data = {}
    static_results = {}

    # invoke BenchIoT ROP gadgets and indirect calls
    #exec(open("benchmarks/benchiot_measure_static_flash_and_ram.py").read())
    benchiot_measure_static_flash_and_ram.measure_static()

    # Collect data
    for bench in benchmarks:
        raw_section_data[bench] = benchmark_size(bench, ALL_METRICS)
        raw_totals[bench] = sum(raw_section_data[bench].values())
        bench_path = os.path.join(bench_dir, bench)
        size_out = raw_section_data[bench]
        for f in os.listdir(bench_path):
            file_path = os.path.join(bench_path, f)
            if os.path.isfile(file_path):
                filename, file_extension = os.path.splitext(file_path)
                if file_extension == ".json":
                    with open(file_path) as fdata:
                        data = json.load(fdata)
                        static_out = size_out | {"ROP_gadgets" : int(data["ROP_gadgets"]), "Indirect_calls" : int(data["Indirect_calls"])}
                        static_results[bench] = static_out
    static_metrics_file = os.path.join(bench_dir, 'results', 'results_static_baseline.json')
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
    main_stack_usage = re.search('Main stack usage:(\d+)', file_str, re.S)
    if main_stack_usage:
        results["Main_stack_usage"] = main_stack_usage.group(1)
    app_stack_usage = re.search('App stack usage:(\d+)', file_str, re.S)
    if app_stack_usage:
        results["App_stack_usage"] = app_stack_usage.group(1)
    return results

""" Join the static and the dynamic results """
def produce_recap(results_dir, benchmarks):
    # Compute the baseline data we need
    baseline = {}

    recap_tot = {}
    for f in os.listdir(results_dir):
        file_path = os.path.join(results_dir, f)
        if os.path.isfile(file_path):
            filename, file_extension = os.path.splitext(file_path)
            # read static
            if file_extension == ".json" and os.path.basename(filename) == "results_static_baseline":
                with open(file_path) as fstatics:
                    static_data = json.load(fstatics)

                    #static_out = size_out | {"ROP_gadgets" : int(data["ROP_gadgets"]), "Indirect_calls" : int(data["Indirect_calls"])}
            if file_extension == ".json" and os.path.basename(filename) == "results_dynamic_baseline":
                with open(file_path) as fdynamics:
                    dynamic_data = json.load(fdynamics)
    for bench in benchmarks:
        recap_tot[bench] = []
        recap_tot[bench].append({"Static" : static_data[bench]})
        recap_tot[bench].append({"Dynamic" : dynamic_data[bench]})

    recap_file = os.path.join(results_dir, 'results_recap_baseline.json')
    with open(recap_file, "w") as outfile:
        json.dump(recap_tot, outfile, indent=4, sort_keys=True)


""" Generic function to start a thread"""
def start_thread(func, name=None, args = []):
    thread = threading.Thread(target=func, name=name, args=args)
    thread.start()
    return thread

""" Start a JLinkGDBServer """
def init_gdbserver(bench_name):
    try:
        process = subprocess.Popen(
                    ["/opt/SEGGER/JLink/JLinkGDBServer", "-if", "swd", "-device", "nRF52832_xxAA",
                    "-endian", "little", "-speed", "1000", "-port", "2331", "-swoport", "2332",
                    "-telnetport", "2333", "-vd", "-ir", "-localhostonly", "1", "-singlerun", "-strict",
                    "-timeout", "0", "-nogui"],
                    #capture_output=True, # doesn't work
                    stdin=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    stdout=subprocess.DEVNULL
                    #timeout=gp['timeout'],
                )
    except subprocess.TimeoutExpired:
            log.warning(f'Warning: Run of {bench_name} timed out.')
    except BaseException:
        print("Error in init_gdbserver")

""" Start a telnet to retrive the semihosting output"""
def init_telnet(bench_name, run, queue):
    succeeded = True
    output = ""
    try:
        tn = telnetlib.Telnet("localhost", 2333, timeout=20)
        output = tn.read_all()
        tn.close()
    except ConnectionRefusedError:
        log.warning(f'Warning: Run of {bench_name} timed out.')
        succeeded = False
    except BaseException:
        log.warning(f'Warning: {bench_name} failed')
        succeeded = False
    # Dump the data if successful
    outfile = os.path.join("generated/benchmarks/results", f'baseline_{bench_name}_{run}.txt')
    if succeeded:
        queue.put_nowait([bench_name, output])
        with open(outfile, "w") as fileh:
            linecount = 0
            for line in output.decode('utf-8').splitlines(keepends=True):
               # if not 'All benchmarks ' + desc + ' successfully' in line:
                fileh.writelines(line)
                linecount=linecount+1
            fileh.close()
            if linecount == 1:
                print("***ERROR: " + bench_name + "failed, check gdbserver connection (is the device up and running? or try to augment sleep delay)")
    else:
        print("***ERROR: " + bench_name + "failed, check gdbserver connection (is the device up and running? or try to augment sleep delay)")
        queue.put_nowait([bench_name, "Failed"])
        mode = 'a'
        with open(outfile, mode) as fileh:
            fileh.write("NOK")
            fileh.close()

""" Build and run the benchmarks, then analyse the results"""
def main():
    # Establish the root directory of the repository, since we know this file is
    # in that directory.
    gp['rootdir'] = os.path.abspath(os.path.dirname(__file__))

    results_dir = "generated/benchmarks/results"

    runs = 1

    do_all = False
    build_only= False
    dynamic_analysis_only = False
    static_analysis_only = False
    recap_only = False

    if(len(sys.argv)==1):
        do_all = True
    else:
        match (sys.argv[1]):
            case "build-only":
                build_only= True
            case "dynamic-only":
                dynamic_analysis_only = True
            case "static-only":
                static_analysis_only = True
            case "recap-only":
                recap_only = True
            case _:
                do_all = True

    if do_all:
        if(os.path.isdir(results_dir)):
            shutil.rmtree(results_dir) # erase dir
        Path(results_dir).mkdir(parents=True, exist_ok=True) # create dir

    # Find the benchmarks
    benchmarks = find_benchmarks()
    benchmarks.remove('matmult-int')
    benchmarks.remove('md5sum')
    benchmarks.remove('nettle-aes')
    benchmarks.remove('picojpeg')
    benchmarks.remove('st')
    benchmarks.remove('tarfind')
    benchmarks.remove('ud')
    benchmarks.remove('wikisort')

    '''benchmarks.remove('aha-mont64')
    benchmarks.remove('crc32')
    benchmarks.remove('cubic')
    benchmarks.remove('edn')
    benchmarks.remove('huffbench')
    benchmarks.remove('minver')
    benchmarks.remove('nettle-sha256')
    benchmarks.remove('nsichneu')
    benchmarks.remove('nbody')
    benchmarks.remove('primecount')
    benchmarks.remove('qrduino')
    benchmarks.remove('sglib-combined')
    benchmarks.remove('slre')
    benchmarks.remove('statemate')'''


    #benchmarks = ['aha-mont64', 'crc32', 'cubic', 'edn', 'huffbench']
    print("benchmarks.py: Considered benchmarks: ", end="")
    print(benchmarks)
    log_benchmarks(benchmarks)

    '''Outer loop for all benchmark types
    BUILD_OPTIONS = {
    'mbed-os':{
        MBED_CMD: ['mbed','export', '-m',str(BOARD_NAME), '-i', 'GCC_ARM', '--profile', 'release'],
        CLEAN_CMD: ['make', '-j4', 'BOARD=' + str(BOARD_NAME), 'IOT2_ALL=1',
                   'CUSTOM_BIN_SUFFIX=--baseline',
                   'clean'],
        MAKE_CMD: ['make', '-j4', 'BOARD='+str(BOARD_NAME), 'IOT2_ALL=1', 'CUSTOM_BIN_SUFFIX=--baseline',
                   'iot2benchmark']
    },
    'mbed': {
        MBED_CMD: ['mbed', 'export', '-m',str(BOARD_NAME), '-i', 'GCC_ARM', '--profile', 'release'],
        CLEAN_CMD: ['make', '-j4', 'BOARD=' + str(BOARD_NAME), 'IOT2_ALL=1', 'CUSTOM_BIN_SUFFIX=--baseline',
                   'clean'],
        MAKE_CMD: ['make', '-j4', 'BOARD=' + str(BOARD_NAME), 'IOT2_ALL=1',
                   'CUSTOM_BIN_SUFFIX=--baseline',
                   'iot2benchmark']
    },
    'uvisor':{
        MBED_CMD: ['mbed', 'export', '-m',str(BOARD_NAME), '-i', 'GCC_ARM', '--profile', 'release'],
        CLEAN_CMD: ['make', '-j4', 'BOARD=' + str(BOARD_NAME), 'IOT2_ALL=1', 'IOT2_UVISOR=1',
                   'IOT2_CONFIG=3', 'CUSTOM_LINKER=uvisor', 'CUSTOM_BIN_SUFFIX=--uvisor', 'clean'],
        MAKE_CMD: ['make', '-j4', 'BOARD=' + str(BOARD_NAME), 'IOT2_ALL=1', 'IOT2_UVISOR=1',
                   'IOT2_CONFIG=3', 'CUSTOM_LINKER=uvisor', 'CUSTOM_BIN_SUFFIX=--uvisor', 'iot2benchmark']
    }
}'''


    if do_all or build_only:
        # Track success
        successful = True
        for bench in benchmarks:
            print("Building " + bench, end='...')
            try:
                res = subprocess.run(
                    ["make", "-s", "bench", "BENCH_NAME=" + bench],
                    capture_output=True,
                )
                if res.returncode != 0:
                    print("***NOK***")
                    print("--> Investigate with shell command: make bench BENCH_NAME=" + bench)
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
        print("\nCollecting dynamic data: please ensure the line number corresponds to 'while(1)' instruction in gdb_connect_flash_run.py")
        for bench in benchmarks:
            que = queue.Queue()
            print("\n***Launching baseline benchmark for "+ bench + "***")
            for run in range(1, runs+1):
                print("***RUN "+ str(run) + "/" + str(runs) + "***")
                print("Starting GDBServer", end='...')
                gdbs = start_thread(init_gdbserver, args=[bench])
                print("OK")
                print("Starting Telnet", end='...')
                time.sleep(0.5) # wait GDBServer is up
                tn = start_thread(init_telnet, args=[bench, run, que])
                print("OK")

                print("Flashing and running " + bench + "...")
                try:
                    res = subprocess.run(
                        ["arm-none-eabi-gdb", "--batch", "-ex", f'py arg0 = "{bench}"', "-x", "benchmarks/gdb_connect_flash_run.py"],
                        capture_output=True,
                        #timeout=gp['timeout'],
                    )
                except subprocess.TimeoutExpired:
                        log.warning(f'Warning: Run of {bench} timed out.')
                        print("NOK***")

                tn.join()
                gdbs.join()
                print("Benchmark ended")
                # All threads have returned

        dynamic_results = {} #collections.defaultdict(dict)
        # Analyse all dynamic outputs
        for f in os.listdir(results_dir):
            file_path = os.path.join(results_dir, f)
            if os.path.isfile(file_path):
                filename, file_extension = os.path.splitext(file_path)
                if file_extension == ".json":
                    continue
                with open(file_path) as fdata:
                    read_data = fdata.read()
                    data = decode_results(read_data)
                    cycles = int(data["Cycles"])
                    file_name = re.search('.*_(\D+\d*)_(\d+).*$', f, re.S)
                    if file_name:
                        run_res_out = { 'Run': int(file_name.group(2)),
                                        'Cycles': cycles,
                                        'Time_ms': float(int(cycles)) / float(64000000), # TODO: set real cpu frequency
                                        'Main_stack_usage': int(data["Main_stack_usage"]),
                                        'App_stack_usage': int(data["App_stack_usage"])
                                    }
                        if file_name.group(1) not in dynamic_results:
                            dynamic_results[file_name.group(1)] = []
                        dynamic_results[file_name.group(1)].append(run_res_out)
                    else:
                        print("***Error: Didn't find any output for " + f)
        baseline_file = os.path.join(results_dir, 'results_dynamic_baseline.json')
        with open(baseline_file, "w") as outfile:
            json.dump(dynamic_results, outfile, indent=4, sort_keys=True)

    if do_all or static_analysis_only:
        print("\nCollecting static data:\n")
        static_metrics('generated/benchmarks', benchmarks)

    if do_all or recap_only:
        produce_recap(results_dir, benchmarks)
    print("Nothing to do left")

# Make sure we have new enough Python and only run if this is the main package

check_python_version(3, 10)
if __name__ == '__main__':
    sys.exit(main())
