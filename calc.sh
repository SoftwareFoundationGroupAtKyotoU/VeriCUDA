#!/bin/bash

# usage:
# ./calc.sh <data-dir>

dir=$1

if test -z ${dir}; then
    echo "usage: . calc.sh <data-dir>"
    exit 1
fi

files="scp_Y scp_N rotate_Y rotate_N vectorAdd_Y vectorAdd_N \
    matrixMul_Y matrixMul_N matrixMul2_Y matrixMul2_N \
    matrixMul4_Y matrixMul4_N diffusion1d_Y diffusion1d_N"

for file in ${files}; do
    grep -e '^Result:' ${dir}/${file} | head -n 1 | \
        awk '{printf " %d/%d &", $2, $3}'
    grep -e '^VCG:' ${dir}/${file} | \
        awk '{count+=1; sum+=$2} END {printf " %.4f &", sum/count}'
    grep -e '^SMT:' ${dir}/${file} | \
        awk '{count+=1; sum+=$2} END {printf " %.4f &", sum/count}'
    grep -e '^Size:' ${dir}/${file} | head -n 1 | \
        awk '{printf " %d (%d)", $2, $3}'
    echo ''
done
