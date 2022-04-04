# BENCHMARKS
We evaluate Pip by computing static metrics (lines of code and size) and by measuring its performances (cycles, memory footprint, energy consumption).
The performances are assessed compared to a baseline scenario which is an application running in privileged mode.
The application is part of the Embench Test suite.

Important notice:
The benchmarks only work for the DWM1001 board (Decawave) and the nRF52840dk board (Nordic Semiconductor).
The energy consumption is monitored through a Power Profiler Kit plugged onto an nRF52840 dk board, with an additional nRF52840dk board that flahes the firmware and retrieves the debut output stream. Without the PPK, the energy consumption cannot be monitored.

## Scenarios
We evaluate 3 scenarios:
- an application without Pip
- an application running in Pip's root partition
- an application running in a child partition of Pip's root partition

We compute the relative differences between each scenario for the application.

## Application
The application is choosen out of the Embench Test Suite (https://github.com/embench/embench-iot).
Our Python benchmark script *benchmarks.py* evaluate Pip for several applications out of the suite.
The performance measurements are then averaged over all these applications to compute Pip's mean overhead.

## Installation requirements
Tested with Python 3.10.2

### Download the pip-mpu-benchmark partition
```console
~/pipcore-mpu$ git clone https://gitlab.univ-lille.fr/2xs/pip/pip-mpu-benchmark ..
```

## Running the benchmarks

### The automated way
#### Install the Python script dependencies
```console
~/pipcore-mpu$ cd benchmarks
~/pipcore-mpu/benchmarks$ pip3 install -r requirements.txt
~/pipcore-mpu/benchmarks$ cd ..
```
#### Download the Embench Test Suite and the ROPgadget tool
```console
~/pipcore-mpu$ git clone https://github.com/JonathanSalwan/ROPgadget.git tools/ROPgadget
~/pipcore-mpu$ cd tools/ROPgadget
~/pipcore-mpu/tools/ROPgadget$ git checkout 0703ad
```
```console
~/pipcore-mpu$ git clone https://github.com/embench/embench-iot.git ..
~/pipcore-mpu$ cd ../embench-iot
~/embench-iot$ git checkout 2d2aaa7
```

#### Modify the Embench source
Change line 39 of embench-iot/support/beebsc.h from

`#define assert_beebs(expr) { if (!(expr)) exit (1); }`
to
`#define assert_beebs(expr) { if (!(expr)) while (1); } // changed "exit" to "while" to avoid undefined reference to _fini`

#### OPTIONAL : Monitor the energy consumption
Only works with PPKI and 2 nRF52840dk boards. (TODO: add set-up picture)

TODO: remove the nRFConnect level in the benchmarks.py file
```console
~/pipcore-mpu$ mkdir ../../nRFConnect
~/pipcore-mpu$ git clone https://github.com/wlgrd/ppk_api.git ../../nRFConnect
~/pipcore-mpu$ cd ../../nRFConnect/ppk_api
nRFConnect/ppk_api$ git checkout 3dde4
nRFConnect/ppk_api$ python3 -m venv ppk
nRFConnect/ppk_api$ pip install -r ../pipcore-mpu/benchmarks/ppk_requirements.txt
```
Install nrfjrpog for your ditribution, only then :
Check nrfjprog recognises the PPK and the serial number matches with the output of the command:
```console
nRFConnect/ppk_api$ nrfjprog -i
```
The PPK's serial number is refered below as <ppk_serial_nb>.

We need to replace the PPK FW by the 2.1.0 version.
Download the PPK FW ppk_nrfconnect.hex from https://github.com/NordicSemiconductor/pc-nrfconnect-ppk/tree/master/firmware.
Move it to the hex folder of the ppk_api repository.

Erase and replace the PPK firmware.
```console
nRFConnect/ppk_api$ nrfjprog -s <ppk_serial_nb> --program hex/ppk_nrfconnect.hex --sectorerase -r --verify
```
Check the PPK is working correctly.
```console
nRFConnect/ppk_api$ python3 main.py -s <ppk_serial_nb> -p 3 -a 5 -v
```
#### Run
```console
~/pipcore-mpu$ python3 benchmarks/benchmarks.py
```
With the *energy* parameter you will measure the energy consumption (see previous point).
```console
~/pipcore-mpu$ python3 benchmarks/benchmarks.py energy
```
#### Results
The results are stored in the generated/benchmarks folder.

### The manual way

#### Configuration of the benchmark scenario
```console
~/pipcore-mpu$ ./configure.sh --architecture=nrf52840 --debugging-mode=semihosting --boot-sequence=bench-pip-child
```
--boot-sequence is the target scenario from the following (non-exhaustive) list:
- bench-baseline-priv-w-systick
- bench-pip-root
- bench-pip-child

By default, the MPU and the SysTick are enabled but can be disabled forthe sake of the benchmark.

#### Compilation of the baseline scenario

```console
~/pipcore-mpu$ make all BENCH_NAME=aha-mont64
```
#### Compilation of the Pip scenarios, example with app in a child partition
```console
~/pipcore-mpu$ ./configure.sh --architecture=nrf52840 --debugging-mode=semihosting --boot-sequence=bench-pip-child
~/pipcore-mpu$ make all
```

#### Compilation of the benchmark partition
The compilation used the configured elements of the previous scenario.
```console
~/pip-mpu-benchmark$ make all BENCH_NAME=aha-mont64
```

#### Link the benchmark partition with PIP

```console
~/pipcore-mpu$ ./root-partition-linker.sh pip.bin ../pip-mpu-benchmark/gen_benchmarks/aha-mont64/aha-mont64.bin
```

#### Flash and run the pip.elf file
