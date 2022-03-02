import gdb
# GDB commands to connect to the target and execute the executable until the end of the benchmark

gdb.execute('target remote :2331')
gdb.execute('monitor semihosting enable')
elf_file="generated/benchmarks/" + arg0 + "/" + arg0 + ".elf"
gdb.execute('file ' + elf_file)
gdb.execute('load')
gdb.execute('delete breakpoints')
gdb.execute('break shutoff')
gdb.execute('monitor reset')
gdb.execute('monitor halt')
gdb.execute('continue') # start -> #benchmark ends at shutoff
gdb.execute('quit')





