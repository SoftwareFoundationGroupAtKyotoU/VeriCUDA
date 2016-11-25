#!/bin/bash

# runs verifier without simplification on each samples, with 1h timelimit

basedir=.
verifier=${basedir}/a.opt

make -r opt || exit 1

run () {
    file=$1
    prog=$2
    ${verifier} --check-diverge --no-inline --no-transform --use-triggers \
        --timelimit 3600 samples/${file} ${prog}
}

run scp.cu scp
run rotate.cu rotate
run vectorAdd.cu vectorAdd
run matrixMul.cu matrixMul
run matrixMul.cu matrixMul2
run matrixMul.cu matrixMul4
run diffusion1d.cu diffusion1d
