#!/bin/bash

# usage:
# ./run.sh [n]

basedir=.
outdir=${basedir}/data/`date +%y-%m-%d`
verifier=${basedir}/a.opt

make -r opt || exit 1

mkdir -p ${outdir}

n=$1

if test -z ${n}; then
    echo "the number of iterations is not provided; use 10";
    n=10
fi

run () {
    file=$1
    prog=$2
    for i in `seq 1 $n`
    do
        ${verifier} --check-diverge --no-inline --no-transform --use-triggers \
            samples/${file} ${prog} >> ${outdir}/${prog}_N
    done
    for i in `seq 1 $n`
    do
        ${verifier} --check-diverge samples/${file} ${prog} \
            >> ${outdir}/${prog}_Y
    done
}

run scp.cu scp
run rotate.cu rotate
run vectorAdd.cu vectorAdd
run matrixMul.cu matrixMul
run matrixMul.cu matrixMul2
run matrixMul.cu matrixMul4
run diffusion1d.cu diffusion1d
