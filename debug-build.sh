#!/bin/bash

make clean

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

LANG=en_US.UTF-8 GCC=$CC LLVM_CONFIG=$LC ENABLE_LLVM_PLUGINS=1 DRAGONEGG_DEBUG=1 make -j4 &> /tmp/build.log
