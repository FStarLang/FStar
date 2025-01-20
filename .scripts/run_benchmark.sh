#!/bin/bash

set -ue
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

# FIXME: recast those benchmarks

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

  --compare REV1,REV2   Run a benchmark on both of these F* revisions (commit
                        hashes or branches) and report a summary of each,
                        alongside a small more detailed comparison between
                        them. Your current worktree will not be modified,
                        the revisions will be checked out in fresh directories.

You can also use environment variables to set wrappers for tasksetting
and/or setting FStar OTHERFLAGS, for example:

 $ BENCH_WRAP='taskset --cpu-list 3' BENCH_OTHERFLAGS='--admit_smt_queries true' $0

Will wrap calls to F* will 'taskset --cpu-list 3' and provide the
'--admit_smt_queries true' argument.

EOF
}

function write_simple_summary() {
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

function write_csv() {
    IN=${1}
    OUT=${1}.csv

    FIELDS=('name', 'time_secs', 'user_time_secs', 'sys_time_secs', 'maxrss_kB', 'gc.allocated_words', 'gc.minor_words', 'gc.promoted_words', 'gc.major_words', 'gc.minor_collections', 'gc.major_collections', 'gc.heap_words', 'gc.heap_chunks', 'gc.top_heap_words', 'gc.compactions')

    HEADER=$(printf "%s" ${FIELDS[@]})
    JQ_ARGS=$(printf ".%s" ${FIELDS[@]})

    echo $HEADER > ${OUT}
    cat ${IN}.bench | jq -s -r ".[] | [$JQ_ARGS] | @csv" >> ${OUT}
}

function write_csv_and_summary() {
    write_csv $1
    write_simple_summary $1
}

# Grabs all the .bench files in directory $1 and contatenates them
# into directory #2, after passing them through jq to get nice format
# and remove useless info
function cat_benches_into () {
    if hash jq 2>/dev/null; then
        find "$1" -name '*.bench' -exec cat {} \; >$2
        cat $2 | jq -s ".[] | del(.ocaml)" >$2.pretty
    else
        echo "Unable to find jq to create csv and summary (https://stedolan.github.io/jq/)"
    fi
}

# Clean F* and rebuild
function clean_slate () {
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
    make -j${JLEVEL} dune-full-bootstrap 2>&1 | tee ${BENCH_OUTDIR}/build_fstar.log
    T1=`date +'%Y%m%d_%H%M%S'`
    echo "Finished fstar compiler boostrap ${T1} (started at ${T0})"

    # build library
    T0=`date +'%Y%m%d_%H%M%S'`
    echo "Starting library build ${T0}"
    make -j${JLEVEL} 2>&1 | tee ${BENCH_OUTDIR}/build_fstarlib.log
    T1=`date +'%Y%m%d_%H%M%S'`
    echo "Finished library build ${T1} (started at ${T0})"

    ls -ltr ulib >> ${BENCH_OUTDIR}/build_fstarlib.log
}

function bench_dir () {
    BENCH_DIR="$1"
    NAME="$2"
    RULE="$3"

    mkdir -p ${BENCH_OUTDIR}

    if $RUN; then
        # Remove old .bench files
        find "${BENCH_DIR}" -name '*.bench' -delete

        # We explicitly add -f since we have previously built F* and its library, we are re-checking here.
        ${BENCH_WRAP} make -j${JLEVEL} -C "${BENCH_DIR}" "${RULE}" BENCHMARK_CMD=orun OTHERFLAGS="${BENCH_OTHERFLAGS} -f" 2>&1 | tee ${BENCH_OUTDIR}/${NAME}.log
    fi

    cat_benches_into "${BENCH_DIR}" "${BENCH_OUTDIR}/${NAME}.bench"
    write_csv_and_summary ${BENCH_OUTDIR}/${NAME}
}

function run_bench_suite () {
  if $CLEAN; then
      clean_slate
  fi

  for i in ${CUSTOMS[*]}; do
      DIR=$(echo "$i" | cut -d, -f1)
      NAME=$(echo "$i" | cut -d, -f2)
      RULE=$(echo "$i" | cut -d, -f3)
      bench_dir "$DIR" "$NAME" "$RULE"

      return
  done

  if $AUTO; then
      bench_dir "tests/micro-benchmarks" "micro-benchmarks" "all"
      bench_dir "ulib/" "ulib" "benchmark"

      if $RUN; then make -C src clean_boot; fi
      bench_dir "src/" "ocaml_extract" "ocaml"
  fi
}

function compare_bench_output () {
    COMPARE_LDIR=$1
    COMPARE_RDIR=$2

    mkdir -p ${BENCH_OUTDIR}
    rm -rf ${BENCH_OUTDIR}/left
    rm -rf ${BENCH_OUTDIR}/right
    cp -r ${COMPARE_LDIR}/${BENCH_OUTDIR} ${BENCH_OUTDIR}/left
    cp -r ${COMPARE_RDIR}/${BENCH_OUTDIR} ${BENCH_OUTDIR}/right

    function line () {
        echo "======================================================================"
    }

    function compare_perfile () {
        K=$1
        L=$2
        R=$3

        # Get top 10 files on each side
        TOP_L=$(cat $L | tail -n+2 | sort -n -k$K -r | head -n 10 | awk '{print $1}')
        TOP_R=$(cat $R | tail -n+2 | sort -n -k$K -r | head -n 10 | awk '{print $1}')
        ALL="${TOP_L} ${TOP_R}"

        # Hack, build a regexp matching those files.
        REGEXP=$(echo ${ALL} | tr ' ' '|' | sed 's/|$//')

        # TODO: use mktemp
        # Grep for both top 10 on each side, building a table of position-name-value
        cat $L | tail -n+2 | sort -n -k$K -r | awk '{printf "%s\t%-40s\t%10s\n", NR, $1, $'$K'}' | grep -E ${REGEXP} >top2_l
        cat $R | tail -n+2 | sort -n -k$K -r | awk '{printf "%s\t%-40s\t%10s\n", NR, $1, $'$K'}' | grep -E ${REGEXP} >top2_r

        # Paste together
        paste top2_l top2_r
    }

    # TODO: allow to override with --custom
    (for tag in micro-benchmarks ulib ocaml_extract; do
        echo "For $tag"
        line
        echo
        echo "Summary for ${COMPARE_L}"
        cat ${BENCH_OUTDIR}/left/$tag.summary
        echo

        echo "Summary for ${COMPARE_R}" >&3
        cat ${BENCH_OUTDIR}/right/$tag.summary
        echo >&3

        echo "Per-file comparison, total time. Left is ${COMPARE_L}, right is ${COMPARE_R}"
        compare_perfile 2 ${BENCH_OUTDIR}/left/$tag.perfile ${BENCH_OUTDIR}/right/$tag.perfile
        echo >&3

        echo "Per-file comparison, memory. Left is ${COMPARE_L}, right is ${COMPARE_R}"
        compare_perfile 5 ${BENCH_OUTDIR}/left/$tag.perfile ${BENCH_OUTDIR}/right/$tag.perfile
        echo
    done) >&3
}

function clone_version_into_dir () {
    V=$1
    DIR=$2

    # It would be more elegant to just checkout a worktree instead of
    # cloning the whole repo (+ history). But that would require calling
    # the archive rule (since otherwise the build will fail to build
    # FStar_Version.ml and etc), and that's a whole thing, so let's just
    # clone for now. The --reference means we don't really take any
    # extra space anyway.
    git clone . ${DIR} || true

    # We allow to fail above since it may be already cloned. The next
    # reset will fail anyway if it's not the right repo.

    # New repo doesn't have any branches, parse $V into a commit
    V=$(git rev-parse ${V})

    pushd ${DIR}
    git reset --hard ${V}
    popd
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
COMPARE=false
JLEVEL=1

COMPARE_L=
COMPARE_R=

# First pass for options
OPTIONS=co:hnj:
LONGOPTS=clean,odir:,help,custom:,norun,compare:
PARSED=$(getopt --options=$OPTIONS --longoptions=$LONGOPTS --name "$0" -- "$@")

eval set -- "$PARSED"

while [ $# -gt 0 ]; do
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

        --compare)
            COMPARE=true
            COMPARE_L=$(echo $2 | cut -d, -f1)
            COMPARE_R=$(echo $2 | cut -d, -f2)
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
 $ git clone https://github.com/ocaml-bench/orun.git sandmark
 $ cd sandmark/orun
 $ opam install .
You may need to install libdw-dev via your package manager before."

# Second pass for options, only handles --custom which needs to run after the others
OPTIONS=
LONGOPTS=custom:
PARSED=$(getopt --options=$OPTIONS --longoptions=$LONGOPTS --name "$0" -- "$@")

CUSTOMS=

eval set -- "$PARSED"

while [ $# -gt 0 ]; do
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

# We output the summaries to this file
exec 3>${BENCH_OUTDIR}/output
# and to the console as well via this trick
tail -f ${BENCH_OUTDIR}/output &

TAILPID=$!
trap "kill $!" err exit

if $COMPARE; then

    COMPARE_LDIR=bench-subdir-${COMPARE_L}
    clone_version_into_dir ${COMPARE_L} ${COMPARE_LDIR}

    COMPARE_RDIR=bench-subdir-${COMPARE_R}
    clone_version_into_dir ${COMPARE_R} ${COMPARE_RDIR}

    pushd ${COMPARE_LDIR}
    if $RUN; then
      make -j${JLEVEL} ADMIT=1
    fi
    run_bench_suite
    popd

    pushd ${COMPARE_RDIR}
    if $RUN; then
      make -j${JLEVEL} ADMIT=1
    fi
    run_bench_suite
    popd

    compare_bench_output ${COMPARE_LDIR} ${COMPARE_RDIR}

    exit 0
fi

run_bench_suite
