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
git checkout -- src/ocaml-output

# build fstar compiler bootstrap
T0=`date +'%Y%m%d_%H%M%S'`
echo "Starting fstar compiler bootstrap ${T0}"
make -C src ocaml-fstar-ocaml 2>&1 | tee ${OUTDIR}/build_fstar.log
T1=`date +'%Y%m%d_%H%M%S'`
echo "Finished fstar compiler boostrap ${T1} (started at ${T0})"

# verify ulib and install
T0=`date +'%Y%m%d_%H%M%S'`
echo "Starting fstarlib build ${T0}"
make -C src fstarlib 2>&1 | tee ${OUTDIR}/build_fstarlib.log
T1=`date +'%Y%m%d_%H%M%S'`
echo "Finished fstar compiler boostrap ${T1} (started at ${T0})"

ls -ltr ulib >> ${OUTDIR}/build_fstarlib.log

# benchmark examples/micro-benchmarks
BENCH_DIR=examples/micro-benchmarks; NME=micro-benchmarks
rm -f ${BENCH_DIR}/*.bench
${TASKSET_WRAP} make -C ${BENCH_DIR} ORUN_FSTAR=true OTHERFLAGS="${FSTAR_OTHERFLAGS}" 2>&1 | tee ${OUTDIR}/${NME}.log
cat ${BENCH_DIR}/*.bench > ${OUTDIR}/${NME}.bench

# benchmark ulib
BENCH_DIR=ulib; NME=ulib
rm -f ${BENCH_DIR}/*.bench
${TASKSET_WRAP} make -C ${BENCH_DIR} benchmark ORUN_FSTAR=true OTHERFLAGS="${FSTAR_OTHERFLAGS}" 2>&1 | tee ${OUTDIR}/${NME}.log
cat ${BENCH_DIR}/*.bench > ${OUTDIR}/${NME}.bench

# ocaml_extract: make -C src ocaml
make -C src clean_boot
#make -C src clean # will do a clean-ocaml as well
${TASKSET_WRAP} make -C src ocaml ORUN_FSTAR=true OTHERFLAGS="${FSTAR_OTHERFLAGS}" 2>&1 | tee ${OUTDIR}/ocaml_extract.log
cat src/ocaml-output/*.bench > ${OUTDIR}/ocaml_extract.bench

