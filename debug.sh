#!/bin/bash 

rm *.s a.out

CC=$1
if [[ -z "$CC" ]]; then
  CC=gcc
fi
$CC --version
CPATH=
LIBPATH=
LIB=
if [ $CC == "arm-linux-gnu-gcc" ]; then
  CPATH="-I/usr/arm-linux-gnu/include"
  LIBPATH="-Wl,-rpath-link=/usr/arm-linux-gnu/lib -L/usr/arm-linux-gnu/lib"
  LIB="-nostdlib /usr/arm-linux-gnu/lib/crt1.o /usr/arm-linux-gnu/lib/crti.o /usr/arm-linux-gnu/lib/crtn.o -lc -lgcc -ldl"
fi

LC=$2
if [[ -z "$LC" ]]; then
  LC=llvm-config
fi
echo "LLVM version:" $($LC --version)

export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:$($LC --libdir)

SRC=$3
if [[ -z "$SRC" ]]; then
  SRC=test/validator/c/hello.c
fi

ASM=$4
if [[ -z "$ASM" ]]; then
  $CC -fplugin=./dragonegg.so \
      $CPATH \
      -fplugin-arg-dragonegg-debug-pass-arguments \
      -ftime-report \
      -fverbose-asm \
      -fplugin-arg-dragonegg-enable-gcc-optzns \
      -fplugin-arg-dragonegg-emit-ir \
      -S \
      $SRC \
      -wrapper gdb,--args
else
  $CC -fplugin=./dragonegg.so \
      $CPATH \
      -fplugin-arg-dragonegg-save-gcc-output \
      -fplugin-arg-dragonegg-debug-pass-arguments \
      -fverbose-asm \
      -ftime-report \
      $SRC \
      $LIBPATH \
      $LIB
fi
