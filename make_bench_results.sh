#!/bin/bash
# simple script to run benchmarks and collect them

set -x

FSTAR_OTHERFLAGS="--admit_smt_queries true"
TASKSET_CPU=4

TIMESTAMP=`date +'%Y%m%d_%H%M%S'`
OUTDIR=bench_results/${TIMESTAMP}

if hash taskset 2>/dev/null; then
	echo "taskset found, will run on CPU ${TASKSET_CPU}"
	TASKSET_WRAP='taskset --cpu-list '${TASKSET_CPU}
else
	echo "taskset not found, will run without it"
	TASKSET_WRAP=''
fi

simple_summary() {
    awk -F',' 'BEGIN {total=0; user=0; sys=0} NR>0 {total+=$2; user+=$3; sys+=$4} END {printf "total\tuser\tsystem\t\n%.4g\t%.4g\t%.4g\n", total, user, sys}'
}

mkdir -p ${OUTDIR}

# setup clean fstar to clean state
make clean
make -C src clean_boot
make -C src clean
git checkout -- src/ocaml-output

# log the git state of the tree
git log -n 1 2>&1 | tee -a ${OUTDIR}/git_info.log
git status -v -v 2>&1 | tee -a ${OUTDIR}/git_info.log

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
cat ${OUTDIR}/${NME}.bench | ./make_csv_from_bench.sh > ${OUTDIR}/${NME}.csv
cat ${OUTDIR}/${NME}.csv | simple_summary > ${OUTDIR}/${NME}.summary

# benchmark ulib
BENCH_DIR=ulib; NME=ulib
rm -f ${BENCH_DIR}/*.bench
${TASKSET_WRAP} make -C ${BENCH_DIR} benchmark ORUN_FSTAR=true OTHERFLAGS="${FSTAR_OTHERFLAGS}" 2>&1 | tee ${OUTDIR}/${NME}.log
cat ${BENCH_DIR}/*.bench > ${OUTDIR}/${NME}.bench
cat ${OUTDIR}/${NME}.bench | ./make_csv_from_bench.sh > ${OUTDIR}/${NME}.csv
cat ${OUTDIR}/${NME}.csv | simple_summary > ${OUTDIR}/${NME}.summary

# ocaml_extract: make -C src ocaml
make -C src clean_boot
#make -C src clean # will do a clean-ocaml as well
NME=ocaml_extract
${TASKSET_WRAP} make -C src ocaml ORUN_FSTAR=true OTHERFLAGS="${FSTAR_OTHERFLAGS}" 2>&1 | tee ${OUTDIR}/${NME}.log
cat src/ocaml-output/*.bench > ${OUTDIR}/${NME}.bench
cat ${OUTDIR}/${NME}.bench | ./make_csv_from_bench.sh > ${OUTDIR}/${NME}.csv
cat ${OUTDIR}/${NME}.csv | simple_summary > ${OUTDIR}/${NME}.summary

