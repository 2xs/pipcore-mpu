import gdb
# GDB commands to connect to the target and execute the executable until the end of the benchmark
# WARNING: check the line number in the file corresponds to the while(1) instruction at line #12 ->

gdb.execute('target remote :2331')
gdb.execute('monitor semihosting enable')
elf_file="generated/benchmarks/" + arg0 + "/" + arg0 + ".elf"
gdb.execute('file ' + elf_file)
gdb.execute('load')
gdb.execute('delete breakpoints')
halt_breakpoint = "break svc_handler.c:" + arg1
gdb.execute(halt_breakpoint) ### -> Check number here
gdb.execute('monitor reset')
gdb.execute('monitor halt')
gdb.execute('continue') # start -> benchmark ends at while(1) breakpoint
gdb.execute('quit')





