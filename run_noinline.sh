#!/bin/bash

# runs verifier without simplification on each samples, with 1h timelimit

basedir=.
verifier=${basedir}/a.opt

make -r opt || exit 1

run () {
    file=$1
    prog=$2
    ${verifier} --check-diverge --no-inline \
        samples/${file} ${prog}
}

run scp.cu scp
run rotate.cu rotate
run vectorAdd.cu vectorAdd
run matrixMul.cu matrixMul
run matrixMul.cu matrixMul2
run matrixMul.cu matrixMul4
run diffusion1d.cu diffusion1d


## output

# Result: 0 1
# VCG: 0.048402
# SMT: 5.911971
# Size: 1646 1
# Result: 0 2
# VCG: 0.098883
# SMT: 14.039834
# Size: 3365 2
# Result: 4 7
# VCG: 0.283711
# SMT: 39.363525
# Size: 20948 12
# Result: 14 16
# VCG: 2.184182
# SMT: 26.854666
# Size: 112714 28
# Result: 17 20
# VCG: 4.273511
# SMT: 42.266685
# Size: 194815 35
# Result: 23 28
# VCG: 9.663190
# SMT: 104.948894
# Size: 409587 49
# Result: 2 3
# VCG: 0.150750
# SMT: 11.764220
# Size: 11527 6
