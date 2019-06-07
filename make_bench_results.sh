#!/bin/bash
# simple script to run benchmarks and collect them

set -x

FSTAR_OTHERFLAGS="--admit_smt_queries true"
TASKSET_WRAP='taskset --cpu-list 4'

TIMESTAMP=`date +'%Y%m%d_%H%M%S'`
OUTDIR=bench_results/${TIMESTAMP}

mkdir -p ${OUTDIR}

# setup clean fstar to clean state
make clean
make -C src clean_boot
make -C src clean
T0=`date +'%Y%m%d_%H%M%S'`
echo "Starting fstar compiler bootstrap ${T0}"
make -C src ocaml-fstar-ocaml 2>&1 | tee ${OUTDIR}/build.log
T1=`date +'%Y%m%d_%H%M%S'`
echo "Finished fstar compiler boostrap ${T1} (started at ${T0})"

# benchmark runs
for i in examples/micro-benchmarks ulib; do
	NME=${i##*/}
	${TASKSET_WRAP} make -C $i ORUN_FSTAR=true OTHERFLAGS="${FSTAR_OTHERFLAGS}" 2>&1 | tee ${OUTDIR}/${NME}.log
	cat ${i}/*.bench > ${OUTDIR}/${NME}.bench
done

# ocaml_extract: make -C src ocaml
make -C src clean
make -C src clean_boot
${TASKSET_WRAP} make -C src ocaml ORUN_FSTAR=true OTHERFLAGS="${FSTAR_OTHERFLAGS}" 2>&1 | tee ${OUTDIR}/ocaml_extract.log
cat src/ocaml-output/*.bench > ${OUTDIR}/ocaml_extract.bench

