#!/bin/bash

# example script to run benchmarks and collate them

set -x

# BENCH_OTHERFLAGS are passed to the benchmark commands when they execute,
#  we default to '--admit_smt_queries true' to exclude Z3 execution time from the benchmarks
BENCH_OTHERFLAGS=${BENCH_OTHERFLAGS-"--admit_smt_queries true"}

# BENCH_WRAP can be used to set up CPU affinity with taskset, for example:
#   BENCH_WRAP='taskset --cpu-list 4'
BENCH_WRAP=${BENCH_WRAP-}

# BENCH_OUTDIR is the location of the output directory
BENCH_OUTDIR=${BENCH_OUTDIR-"./bench_results/"`date +'%Y%m%d_%H%M%S'`}

write_simple_summary() {
	IN=${1}
	OUT=${1}.summary
	echo ${IN} > ${OUT}
    cat ${IN}.csv | awk -F',' 'BEGIN {total=0; user=0; sys=0} NR>0 {total+=$2; user+=$3; sys+=$4} END {printf "n\ttotal\tuser\tsystem\t\n%d\t%.4g\t%.4g\t%.4g\n", NR-1,total, user, sys}' >> ${OUT}
}

write_csv() {
	IN=${1}
	OUT=${1}.csv

	FIELDS=('name', 'time_secs', 'user_time_secs', 'sys_time_secs', 'maxrss_kB', 'gc.allocated_words', 'gc.minor_words', 'gc.promoted_words', 'gc.major_words', 'gc.minor_collections', 'gc.major_collections', 'gc.heap_words', 'gc.heap_chunks', 'gc.top_heap_words', 'gc.compactions')
	HEADER=$(printf "%s" ${FIELDS[@]})
	JQ_ARGS=$(printf ".%s" ${FIELDS[@]})

	echo $HEADER > ${OUT}
	cat ${IN}.bench | jq -s -r ".[] | [$JQ_ARGS] | @csv" >> ${OUT}
}

write_csv_and_summary() {
	if hash jq 2>/dev/null; then
		write_csv $1
		write_simple_summary $1
	else
		echo "Unable to find jq to create csv and summary (https://stedolan.github.io/jq/)"
	fi
}

mkdir -p ${BENCH_OUTDIR}

# setup clean fstar to clean state
make clean
make -C src clean_boot
make -C src clean
git checkout -- src/ocaml-output
rm src/.cache.boot/*.checked.lax

# log the git state of the tree
git log -n 1 2>&1 | tee -a ${BENCH_OUTDIR}/git_info.log
git status -v -v 2>&1 | tee -a ${BENCH_OUTDIR}/git_info.log

# build fstar compiler bootstrap
T0=`date +'%Y%m%d_%H%M%S'`
echo "Starting fstar compiler bootstrap ${T0}"
make -C src ocaml-fstar-ocaml 2>&1 | tee ${BENCH_OUTDIR}/build_fstar.log
T1=`date +'%Y%m%d_%H%M%S'`
echo "Finished fstar compiler boostrap ${T1} (started at ${T0})"

# verify ulib and install
T0=`date +'%Y%m%d_%H%M%S'`
echo "Starting fstarlib build ${T0}"
make -C src fstarlib 2>&1 | tee ${BENCH_OUTDIR}/build_fstarlib.log
T1=`date +'%Y%m%d_%H%M%S'`
echo "Finished fstar compiler boostrap ${T1} (started at ${T0})"

ls -ltr ulib >> ${BENCH_OUTDIR}/build_fstarlib.log

# benchmark examples/micro-benchmarks
BENCH_DIR=examples/micro-benchmarks; NME=micro-benchmarks
rm -f ${BENCH_DIR}/*.bench
${BENCH_WRAP} make -C ${BENCH_DIR} BENCHMARK_FSTAR=true BENCHMARK_CMD=orun OTHERFLAGS="${BENCH_OTHERFLAGS}" 2>&1 | tee ${BENCH_OUTDIR}/${NME}.log
cat ${BENCH_DIR}/*.bench > ${BENCH_OUTDIR}/${NME}.bench
write_csv_and_summary ${BENCH_OUTDIR}/${NME}

# benchmark ulib
BENCH_DIR=ulib; NME=ulib
rm -f ${BENCH_DIR}/*.bench
${BENCH_WRAP} make -C ${BENCH_DIR} benchmark BENCHMARK_FSTAR=true BENCHMARK_CMD=orun OTHERFLAGS="${BENCH_OTHERFLAGS}" 2>&1 | tee ${BENCH_OUTDIR}/${NME}.log
cat ${BENCH_DIR}/*.bench > ${BENCH_OUTDIR}/${NME}.bench
write_csv_and_summary ${BENCH_OUTDIR}/${NME}

# ocaml_extract: make -C src ocaml
make -C src clean_boot
#make -C src clean # will do a clean-ocaml as well
NME=ocaml_extract
rm -f src/ocaml-output/*.bench
${BENCH_WRAP} make -C src ocaml BENCHMARK_FSTAR=true BENCHMARK_CMD=orun OTHERFLAGS="${BENCH_OTHERFLAGS}" 2>&1 | tee ${BENCH_OUTDIR}/${NME}.log
cat src/ocaml-output/*.bench > ${BENCH_OUTDIR}/${NME}.bench
write_csv_and_summary ${BENCH_OUTDIR}/${NME}

