Install:

* Install llvm-6.0 in debug mode at ~/installed/
* gcc-8 should be in the machine (8.2 and 8.3 to be specific)
* gnat-8


Locations:

./lib/gcc/x86_64-linux-gnu/8/plugin/include/print-tree.h


gcc-8 -S -fplugin=./dragonegg.so ./Examples/test3.adb
gcc-8 -S -fplugin=./dragonegg.so -fplugin-arg-dragonegg-emit-ir ./Examples/test4.adb -o test4.s



If the following error at runtime

  gcc-<version>: error trying to exec 'gnat1': execvp: No such file or directory

install coresponding gnat-<version>



To run in debug mode, use the following command


gdb -q --args /usr/lib/gcc/x86_64-linux-gnu/8/gnat1 -quiet -dumpbase test3.adb -auxbase test3 -fplugin=./dragonegg.so -mtune=generic -march=x86-64 Examples/test3.adb -o test3.s

gdb -q --args /usr/lib/gcc/x86_64-linux-gnu/8/gnat1 -quiet -dumpbase test4.adb -auxbase test4 -fplugin=./dragonegg.so -mtune=generic -march=x86-64 Examples/test4.adb -o test4.s

gdb -q --args /usr/lib/gcc/x86_64-linux-gnu/8/gnat1 -fplugin=./dragonegg.so -fplugin-arg-dragonegg-emit-ir Examples/test4.adb


