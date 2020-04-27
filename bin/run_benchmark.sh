#!/bin/bash

set -e
set -o pipefail

# There are hooks within the FStar makefiles to make it easy to run a
# benchmarks of tests/micro-benchmarks, ulib and OCaml extraction of
# the FStar compiler itself.
#
# As a simple test, you can run the micro-benchmarks using GNU time to
# measure execution with:
#
#  $ make -C tests/micro-benchmarks BENCHMARK_CMD=time
#
# This will output .bench files for each of the benchmarks.
# (you can use other commands, but they should support a `-o FILE`
# option to output the results to a given file)
#
# More interestingly than 'time' we can use 'orun' and get more
# informative stats. This script automates the process of running with
# orun and summarizing the results.

help () {
cat <<EOF
$0: Benchmark F*

This script runs F* in a set of benchmarks and summarizes the results.
Simply calling it with no arguments will do a full clean build
and run a default set of benchmarks.

You need orun and jq installed to use this.

Options:

  -h
  --help                Display this help text.

  -o DIR
   --odir DIR           Write results into DIR instead of the default directory
                        (which is bench_results/YYYYMMDD_HHMMSS).

  -1
  --perfile             Do not summarize directories, print one line per file instead.

  -c
  --clean               Clean and rebuild F* before benchmarking.

  -j N                  Parallelize by passing '-j N' to 'make'. Use with caution,
                        since this will probably inflate execution times (but
                        should be OK for memory usage).

  -n
  --norun               Do not run any benchmark, simply collect and display
                        information from existing .bench files. This is useful,
                        for instance, to see per-file stats (with -1) without
                        having to run the benchmarks again.

  --custom DIR,NAME,RULE        Run a custom benchmark (advanced, see script).


You can also use environment variables to set wrappers for tasksetting
and/or setting FStar OTHERFLAGS, for example:

 $ BENCH_WRAP='taskset --cpu-list 3' BENCH_OTHERFLAGS='--admit_smt_queries true' $0

Will wrap calls to F* will 'taskset --cpu-list 3' and provide the
'--admit_smt_queries true' argument.

EOF
}

write_simple_summary() {
    IN=${1}
    AGG=${1}.summary
    IND=${1}.perfile

    # Sum everything and summarize into X.summary
    awk -F',' '
        BEGIN {total=0; user=0; sys=0; mem=0}
        BEGIN {printf "%-10s %10s %10s %10s %10s\n", "N_benches", "total", "user", "system", "mem(mb)"}
        NR>0 {total+=$2; user+=$3; sys+=$4; mem+=$5}
        END { printf "%-10d %10g %10g %10g %10d\n", NR-1, total, user, sys, mem/1000}' \
        < ${IN}.csv > ${AGG}
    echo "Wrote ${AGG}"

    # Place individual results into X.perfile, sorted by total time
    cat ${IN}.csv |
    tail -n+2 |
    sort -n -k 2 -t, -r |
    awk -F',' '
        BEGIN {printf "%-40s %10s %10s %10s %10s\n", "file", "total", "user", "system", "mem(kb)"}
        NR>0  {printf "%-40s %10g %10g %10g %10d\n", $1, $2, $3, $4, $5}' \
        > ${IND}
    echo "Wrote ${IND}"
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
    write_csv $1
    write_simple_summary $1
}

# Grabs all the .bench files in directory $1 and contatenates them
# into directory #2, after passing them through jq to get nice format
# and remove useless info
cat_benches_into () {
    if hash jq 2>/dev/null; then
        find "$1" -name '*.bench' -exec cat {} \; | jq -s ".[] | del(.ocaml)"> $2
    else
        echo "Unable to find jq to create csv and summary (https://stedolan.github.io/jq/)"
    fi
}

# Clean F* and rebuild
clean_slate () {
    make clean
    make -C src clean_boot
    make -C src clean
    git checkout -- src/ocaml-output
    rm -f src/.cache.boot/*.checked.lax

    # log the git state of the tree
    git log -n 1 2>&1 | tee -a ${BENCH_OUTDIR}/git_info.log
    git status -v -v 2>&1 | tee -a ${BENCH_OUTDIR}/git_info.log

    # build fstar compiler bootstrap
    T0=`date +'%Y%m%d_%H%M%S'`
    echo "Starting fstar compiler bootstrap ${T0}"
    make -j${JLEVEL} -C src ocaml-fstar-ocaml 2>&1 | tee ${BENCH_OUTDIR}/build_fstar.log
    T1=`date +'%Y%m%d_%H%M%S'`
    echo "Finished fstar compiler boostrap ${T1} (started at ${T0})"

    # verify ulib and install
    T0=`date +'%Y%m%d_%H%M%S'`
    echo "Starting fstarlib build ${T0}"
    make -j${JLEVEL} -C src .fstarlib 2>&1 | tee ${BENCH_OUTDIR}/build_fstarlib.log
    T1=`date +'%Y%m%d_%H%M%S'`
    echo "Finished fstar compiler boostrap ${T1} (started at ${T0})"

    ls -ltr ulib >> ${BENCH_OUTDIR}/build_fstarlib.log
}

bench_dir () {
    BENCH_DIR="$1"
    NAME="$2"
    RULE="$3"

    if $RUN; then
        # Remove old .bench files
        find "${BENCH_DIR}" -name '*.bench' -delete

        ${BENCH_WRAP} make -j${JLEVEL} -C "${BENCH_DIR}" "${RULE}" BENCHMARK_CMD=orun OTHERFLAGS="${BENCH_OTHERFLAGS}" 2>&1 | tee ${BENCH_OUTDIR}/${NAME}.log
    fi

    cat_benches_into "${BENCH_DIR}" "${BENCH_OUTDIR}/${NAME}.bench"
    write_csv_and_summary ${BENCH_OUTDIR}/${NAME}
}

# BENCH_OTHERFLAGS are passed to the benchmark commands when they execute,
#  we default to '--admit_smt_queries true' to exclude Z3 execution time from the benchmarks
BENCH_OTHERFLAGS=${BENCH_OTHERFLAGS-"--admit_smt_queries true"}

# BENCH_WRAP can be used to set up CPU affinity with taskset, for example:
#   BENCH_WRAP='taskset --cpu-list 4'
BENCH_WRAP=${BENCH_WRAP-}

# BENCH_OUTDIR is the location of the output directory
BENCH_OUTDIR="./bench_results/"`date +'%Y%m%d_%H%M%S'`

CLEAN=false
AUTO=true
RUN=true
JLEVEL=1

# First pass for options
OPTIONS=co:hnj:
LONGOPTS=clean,odir:,help,custom:,norun
PARSED=$(getopt --options=$OPTIONS --longoptions=$LONGOPTS --name "$0" -- "$@")

eval set -- "$PARSED"

while true; do
    case "$1" in
        -c|--clean)
            CLEAN=true
            shift
            ;;

        -o|--odir)
            BENCH_OUTDIR=$2
            shift 2
            ;;

        -h|--help)
            help
            exit 1
            ;;

        -n|--norun)
            RUN=false
            shift
            ;;

        -j)
            JLEVEL=$2
            shift 2
            ;;

        --custom)
            # Push to the tail, next pass will get it
            B1="$1"
            B2="$2"
            shift 2
            eval set -- "$@" "$B1" "$B2"
            ;;

        --)
            shift
            break
            ;;

        *)
            echo "bad arg: $1"
            exit 1
            ;;
    esac
done

check_for () {
    if ! hash "$1" 2>/dev/null; then
            echo "This script needs '$1' installed to work"
            if ! [ "x$2" = "x" ]; then
                echo
                echo "$2"
            fi
            exit 1
    fi
}

check_for jq "Try to install it via your package manager, or see https://stedolan.github.io/jq/"

check_for orun "\
To install a local pinned copy of orun do the following:
 $ git clone https://github.com/ocaml-bench/sandmark.git sandmark
 $ cd sandmark/orun
 $ opam install ."

# Second pass for options, only handles --custom which needs to run after the others
OPTIONS=
LONGOPTS=custom:
PARSED=$(getopt --options=$OPTIONS --longoptions=$LONGOPTS --name "$0" -- "$@")

CUSTOMS=

eval set -- "$PARSED"

while true; do
    case "$1" in
        --custom)
            CUSTOMS+=($2)
            AUTO=false
            shift 2
            ;;

        --)
            shift
            break
            ;;

        *)
            echo "bad arg: $1"
            exit 1
            ;;
    esac
done

if [[ $# -ne 0 ]]; then
    echo "Unexpected argument: '$1'"
    exit 0
fi

mkdir -p ${BENCH_OUTDIR}

if $CLEAN; then
    clean_slate
fi

for i in ${CUSTOMS[*]}; do
    DIR=$(echo "$i" | cut -d, -f1)
    NAME=$(echo "$i" | cut -d, -f2)
    RULE=$(echo "$i" | cut -d, -f3)
    bench_dir "$DIR" "$NAME" "$RULE"
done

# If not --custom, run the default set of benchmarks
if $AUTO; then
    bench_dir "tests/micro-benchmarks" "micro-benchmarks" "all"
    bench_dir "ulib/" "ulib" "benchmark"

    if $RUN; then make -C src clean_boot; fi
    bench_dir "src/" "ocaml_extract" "ocaml"
fi
