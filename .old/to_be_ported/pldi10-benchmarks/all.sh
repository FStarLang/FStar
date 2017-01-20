#!/usr/bin/env bash

FINE_COMPILER="fstar.exe --silent"
OUTDIR=out
STANDALONE_TESTS="authac.f9 automaton.f9 iflow.f9"
APPS="health-web lookout fine-continue"
CONSEQ="11"

function clean(){
  rm -rf $OUTDIR
  rm -rf queries
  mkdir -p $OUTDIR
  mkdir -p queries
}

function set_config(){
    case $1 in
        "1")
            CONFIG_NAME="SOURCE CHECKING ONLY"
            FLAGS="--skip_translation"
            EXTRASRC="--prooflibvals $FINE_HOME/lib/prooflibvals.f9";;
        "2")
            CONFIG_NAME="DEREFINEMENT WITHOUT PROOFS"
            FLAGS=""
            EXTRASRC="--prooflibvals $FINE_HOME/lib/prooflibvals.f9";;
        "3")
            CONFIG_NAME="DCIL TYPE CHECKED WITHOUT PROOFS"
            FLAGS="--to_dcil"
            EXTRASRC="--prooflibvals $FINE_HOME/lib/prooflibvals.f9";;
        "4")
            CONFIG_NAME="PROOF EXTRACTION"
            FLAGS="--extract_proofs"
            EXTRASRC="--prooflibvals $FINE_HOME/lib/prooflibvals.f9";;
        "5")
            CONFIG_NAME="PROOFS TYPE CHECKED AT SOURCE"
            FLAGS="--noss --typecheck_proofs"
            EXTRASRC="--prooflibvals $FINE_HOME/lib/prooflibvals.f9";;
        "6")
            CONFIG_NAME="DCIL TYPECHECKED WITH PROOFS"
            FLAGS="--noss --typecheck_proofs --to_dcil"
            EXTRASRC="--prooflibvals $FINE_HOME/lib/prooflibvals.f9";;
        "7")
            rm -rf "dlls-$2"
            mkdir -p "dlls-$2"
            CONFIG_NAME="IL Generation without proofs"
            FLAGS="--to_dcil --genIL --odir dlls-$2"
            EXTRASRC="--prooflibvals $FINE_HOME/lib/prooflibvals.f9";;
        "8")
            rm -rf "pfdlls-$2"
            mkdir -p "pfdlls-$2"
            CONFIG_NAME="IL Generation with proofs"
            FLAGS="--typecheck_proofs --genIL --noss --writePrims --odir pfdlls-$2"
            EXTRASRC="--prooflibvals $FINE_HOME/lib/prooflibvals.f9";;
        "9")
            rm -rf "pfdlls-$2"
            mkdir -p "pfdlls-$2"
            CONFIG_NAME="FSTAR: Source checking with ghost refinements"
            FLAGS="--z3enc"
            EXTRASRC="";;
        "10")
            rm -rf "pfdlls-$2"
            mkdir -p "pfdlls-$2"
            CONFIG_NAME="FSTAR--genIL: whole compilation with target ignoring refinements"
            FLAGS="--genIL"
            EXTRASRC="";;
        "11")
            rm -rf "pfdlls-$2"
            mkdir -p "pfdlls-$2"
            CONFIG_NAME="FSTAR--rdcil: whole compilation with ghost refinements"
            FLAGS="--rdcil --genIL --odir out"
            EXTRASRC="";;
    esac
}

function run_test(){
    CONFIG_NUM=$1
    TEST_NAME=$2
    SRC_FILES=$3
    set_config $CONFIG_NUM $TEST_NAME
    OUT_FILE=$OUTDIR/"$TEST_NAME.result.$CONFIG_NUM"
    echo "$FINE_COMPILER $FLAGS $EXTRASRC $SRC_FILES" > $OUT_FILE
    $FINE_COMPILER $FLAGS $EXTRASRC $SRC_FILES >> $OUT_FILE 2>&1
}

function process_test_result(){
    prefix=$1
    testname=$2
    confnum=$3
    FILE="$prefix/$OUTDIR/$testname.result.$confnum"
    grep -q -v -i "Error" $FILE
    NOERR=$?
    grep -q "Verified module" $FILE
    CHECKED=$?
    if [ "$CHECKED" -eq "0" -a "$NOERR" -eq "0" ]; then
        echo "$testname ok"
    else
        echo "$testname ******FAILURE******"
    fi
    if [ "$confnum" -eq "7" ]; then
        tar cf "dlls-$testname.tar" "$prefix/dlls-$testname"
        ls -alh "dlls-$testname.tar"
    elif [ "$confnum" -eq "8" ]; then
        tar cf "pfdlls-$testname.tar" "$prefix/pfdlls-$testname"
        ls -alh "pfdlls-$testname.tar"
    fi
}

function archive() {
    NOW=`date '+%s'`
    DIRNAME="test-archive-$NOW"
    rm -rf $DIRNAME
    mkdir -p $DIRNAME
    cp -r $OUTDIR $DIRNAME/
    for APPDIR in $APPS; do
        mkdir -p $DIRNAME/$APPDIR
        cp -r $APPDIR/$OUTDIR $DIRNAME/$APPDIR
    done
    tar cvfz $DIRNAME.tgz $DIRNAME
}

clean

for TESTNAME in $STANDALONE_TESTS; do
    echo -n "Testing $TESTNAME; Config "
    for CONFNUM in $CONSEQ; do
        echo -n "$CONFNUM ... "
        run_test $CONFNUM $TESTNAME $TESTNAME
    done
    echo ""
done

for APPDIR in $APPS; do
    cd $APPDIR
    clean
#    FINE_HOME=../../../..
    SRC=`cat src.txt`
    echo -n "Testing $APPDIR; Config "
    for CONFNUM in $CONSEQ; do
        echo -n "$CONFNUM ... "
        run_test $CONFNUM $APPDIR "$SRC"
    done
    echo ""
    cd ..
done

for CONFNUM in $CONSEQ; do
    set_config $CONFNUM "dummy"
    echo ""
    echo "****CONFIGURATION: $CONFIG_NAME****"
    for TESTNAME in $STANDALONE_TESTS; do
        process_test_result "." $TESTNAME $CONFNUM
    done
    for TESTDIR in $APPS; do
        process_test_result $TESTDIR $TESTDIR $CONFNUM
    done
done

# archive
