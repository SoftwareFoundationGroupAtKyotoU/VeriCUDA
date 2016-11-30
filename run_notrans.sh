#!/bin/bash

# runs verifier without simplification on each samples, with 1h timelimit

basedir=.
verifier=${basedir}/a.opt

make -r opt || exit 1

run () {
    file=$1
    prog=$2
    ${verifier} --check-diverge --no-transform \
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

# Result: 1 2
# VCG: 0.003461
# SMT: 6.714775
# Size: 2527 2
# Result: 1 3
# VCG: 0.010778
# SMT: 24.118131
# Size: 3870 3
# Result: 3 7
# VCG: 0.017660
# SMT: 28.904486
# Size: 9196 7
# Result: 15 17
# VCG: 0.271460
# SMT: 20.284746
# Size: 26221 17
# Result: 18 21
# VCG: 2.743615
# SMT: 56.095650
# Size: 44842 21
# Result: 23 29
# VCG: 331.421013
# SMT: 741.106044
# Size: 445070 29
# Result: 1 4
# VCG: 192.522438
# SMT: 8682.740279
# Size: 10564478 4
