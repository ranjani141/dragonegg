#!/bin/bash 

rm *.s a.out

CC=$1
if [[ -z "$CC" ]]; then
    CC=gcc
fi
$CC --version

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
        -fplugin-arg-dragonegg-save-gcc-output \
        -fplugin-arg-dragonegg-debug-pass-arguments \
        -fverbose-asm \
        -ftime-report \
        $SRC
fi
