#!/usr/bin/env bash

#set -x

target=$1
out_file=$2
threads=$3
branchname=$4

function export_home() {
    if command -v cygpath >/dev/null 2>&1; then
        export $1_HOME=$(cygpath -m "$2")
    else
        export $1_HOME="$2"
    fi
}

function fetch_vale() {
    if [ ! -d vale ]; then
        git clone https://github.com/project-everest/vale vale
    fi

    cd vale
    git fetch origin
    echo Switching to vale to fstar_ci
    git clean -fdx .
    git reset --hard origin/fstar_ci
    nuget restore tools/Vale/src/packages.config -PackagesDirectory tools/FsLexYacc
    cd ..
    export_home VALE "$(pwd)/vale"
}

# By default, HACL* master works against F* stable. Can also be overridden.
function fetch_hacl() {
    if [ ! -d hacl-star ]; then
        git clone https://github.com/mitls/hacl-star hacl-star
    fi

    cd hacl-star
    git fetch origin
    local ref=$(if [ -f ../.hacl_version ]; then cat ../.hacl_version | tr -d '\r\n'; else echo origin/master; fi)
    echo Switching to HACL $ref
    git reset --hard $ref
    git clean -fdx
    cd ..
    export_home HACL "$(pwd)/hacl-star"
    export_home EVERCRYPT "$(pwd)/hacl-star/providers"
}

# By default, kremlin master works against F* stable. Can also be overridden.
function fetch_kremlin() {
    if [ ! -d kremlin ]; then
        git clone https://github.com/FStarLang/kremlin kremlin
    fi

    cd kremlin
    git fetch origin
    local ref=$(if [ -f ../.kremlin_version ]; then cat ../.kremlin_version | tr -d '\r\n'; else echo origin/master; fi)
    echo Switching to KreMLin $ref
    git reset --hard $ref
    cd ..
    export_home KREMLIN "$(pwd)/kremlin"
}

function fetch_and_make_kremlin() {
    fetch_kremlin

    # Default build target is minimal, unless specified otherwise
    local localTarget
    if [[ $1 == "" ]]; then
        localTarget="minimal"
    else
        localTarget="$1"
    fi

    make -C kremlin -j $threads $localTarget ||
        (cd kremlin && git clean -fdx && make -j $threads $localTarget)
    OTHERFLAGS='--admit_smt_queries true' make -C kremlin/kremlib -j $threads
    export PATH="$(pwd)/kremlin:$PATH"
}

# By default, mitls-fstar master works against F* stable. Can also be overridden.
function fetch_mitls() {
    if [ ! -d mitls-fstar ]; then
        git clone https://github.com/mitls/mitls-fstar mitls-fstar
    fi
    cd mitls-fstar
    git fetch origin
    local ref=$(if [ -f ../.mitls_version ]; then cat ../.mitls_version | tr -d '\r\n'; else echo origin/master; fi)
    echo Switching to mitls-fstar $ref
    git reset --hard $ref
    git clean -fdx
    cd ..
    export_home MITLS "$(pwd)/mitls-fstar"
}

function refresh_fstar_hints() {
    if [ -f ".scripts/git_rm_stale_hints.sh" ]; then
        ./.scripts/git_rm_stale_hints.sh
    fi

    refresh_hints "git@github.com:FStarLang/FStar.git" "git ls-files src/ocaml-output/ | xargs git add" "regenerate hints + ocaml snapshot" "."
}

# Note: this performs an _approximate_ refresh of the hints, in the sense that
# since the hint refreshing job takes about 80 minutes, it's very likely someone
# merged to $CI_BRANCH in the meanwhile, which would invalidate some hints. So, we
# reset to origin/$CI_BRANCH, take in our hints, and push. This is short enough that
# the chances of someone merging in-between fetch and push are low.
function refresh_hints() {
    local remote=$1
    local extra="$2"
    local msg="$3"
    local hints_dir="$4"

    # Figure out the branch
    CI_BRANCH=${branchname##refs/heads/}
    echo "Current branch_name=$CI_BRANCH"

    # Add all the hints, even those not under version control
    find $hints_dir -iname '*.hints' -and -not -path '*/.*' -and -not -path '*/dependencies/*' | xargs git add

    # Without the eval, this was doing weird stuff such as,
    # when $2 = "git ls-files src/ocaml-output/ | xargs git add",
    # outputting the list of files to stdout
    eval "$extra"

    git commit --allow-empty -m "[CI] $msg"
    # Memorize that commit
    commit=$(git rev-parse HEAD)
    # Drop any other files that were modified as part of the build (e.g.
    # parse.fsi)
    git reset --hard HEAD
    # Move to whatever is the most recent master (that most likely changed in the
    # meantime)
    git fetch
    git checkout $CI_BRANCH
    git reset --hard origin/$CI_BRANCH
    # Silent, always-successful merge
    export GIT_MERGE_AUTOEDIT=no
    git merge $commit -Xtheirs
    # Push.
    git push $remote $CI_BRANCH
}

function build_fstar() {
    local localTarget=$1
    local timeout=960

    result_file="../result.txt"
    echo Failure >$result_file

    # $status_file is the name of a file that contains true if and
    # only if the F* regression suite failed, false otherwise
    status_file="../status.txt"
    echo false >$status_file

    ORANGE_FILE="../orange_file.txt"
    echo '' >$ORANGE_FILE

    if [[ -x /usr/bin/time ]]; then
        gnutime=/usr/bin/time
    else
        gnutime=""
    fi

    if [ ! -d ulib ]; then
        echo "I don't seem to be in the right directory, bailing"
        return
    fi

    if [[ $localTarget == "fstar-binary-build" ]]; then
        fetch_kremlin
        ./.scripts/process_build.sh && echo true >$status_file
    elif [[ $localTarget == "fstar-docs" ]]; then
        # First - get fstar built
        # Second - run fstar with the --doc flag
        make -C src/ocaml-output clean && make -C src/ocaml-output -j $threads && .ci/fsdoc.sh && echo true >$status_file
    else
        if [[ $localTarget == "uregressions-ulong" ]]; then
            export OTHERFLAGS="--record_hints $OTHERFLAGS"
        fi

        fetch_kremlin

        if ! make -C src -j $threads utest-prelude
        then
            echo Warm-up failed
            echo Failure >$result_file
        else
            export_home FSTAR "$(pwd)"

            fetch_vale &
            fetch_hacl &
            fetch_and_make_kremlin &
            fetch_mitls &
            {
                if [ ! -d hacl-star-old ]; then
                    git clone https://github.com/mitls/hacl-star hacl-star-old
                    cd hacl-star-old && git reset --hard 98755f79579a0c153140e8d9a186145beafacf8f
                fi
            } &
            wait

            # The commands above were executed in sub-shells and their EXPORTs are not
            # propagated to the current shell. Re-do.
            export_home HACL "$(pwd)/hacl-star"
            export_home KREMLIN "$(pwd)/kremlin"

            # Once F* is built, run its main regression suite, along with more relevant
            # tests.
            {
                $gnutime make -C src -j $threads -k $localTarget && echo true >$status_file
                echo Done building FStar
            } &

            {
                has_error="false"
                cd vale
                if [[ "$OS" == "Windows_NT" ]]; then
                    ## This hack for determining the success of a vale run is needed
                    ## because somehow scons is not returning the error code properly
                    { timeout $timeout ./run_scons.sh -j $threads --FSTAR-MY-VERSION --MIN_TEST |& tee vale_output ; } || has_error="true"

                    ## adds "min-test (Vale)" to the ORANGE_FILE
                    ##      if this string vvvv is present in vale_output
                    ! grep -qi 'scons: building terminated because of errors.' vale_output || has_error="true"
                else
                    timeout $timeout scons -j $threads --FSTAR-MY-VERSION --MIN_TEST || has_error="true"
                fi
                cd ..

                if [[ $has_error == "true" ]]; then
                    echo "Error - min-test (Vale)"
                    echo " - min-test (Vale)" >>$ORANGE_FILE
                fi
            } &

            {
                OTHERFLAGS='--warn_error -276 --use_hint_hashes' timeout $timeout make -C hacl-star/code/hash/ -j $threads Hacl.Impl.SHA2_256.fst-verify ||
                    {
                        echo "Error - Hacl.Impl.SHA2_256.fst-verify (HACL*)"
                        echo " - Hacl.Impl.SHA2_256.fst-verify (HACL*)" >>$ORANGE_FILE
                    }
            } &

            {
                OTHERFLAGS='--use_hint_hashes' timeout $timeout make -C hacl-star/secure_api -f Makefile.old -j $threads aead/Crypto.AEAD.Encrypt.fst-ver ||
                    {
                        echo "Error - Crypto.AEAD.Encrypt.fst-ver (HACL*)"
                        echo " - Crypto.AEAD.Encrypt.fst-ver (HACL*)" >>$ORANGE_FILE
                    }
            } &

            # We now run all (hardcoded) tests in mitls-fstar@master
            {
                OTHERFLAGS=--use_hint_hashes timeout $timeout make -C mitls-fstar/src/tls -j $threads StreamAE.fst-ver ||
                    {
                        echo "Error - StreamAE.fst-ver (mitls)"
                        echo " - StreamAE.fst-ver (mitls)" >>$ORANGE_FILE
                    }

                OTHERFLAGS=--use_hint_hashes timeout $timeout make -C mitls-fstar/src/tls -j $threads Pkg.fst-ver ||
                    {
                        echo "Error - Pkg.fst-ver (mitls verify)"
                        echo " - Pkg.fst-ver (mitls verify)" >>$ORANGE_FILE
                    }

                OTHERFLAGS="--use_hint_hashes --use_extracted_interfaces true" timeout $timeout make -C mitls-fstar/src/tls -j $threads Pkg.fst-ver ||
                    {
                        echo "Error - Pkg.fst-ver with --use_extracted_interfaces true (mitls verify)"
                        echo " - Pkg.fst-ver with --use_extracted_interfaces true (mitls verify)" >>$ORANGE_FILE
                    }
            } &

            # JP: doesn't work because it leads to uint128 being verified in the wrong Z3
            # context (?) meaning that some proof obligations fail
            # { cd kremlin/test && timeout 480 ../krml -warn-error @4 -static-header FStar -no-prefix \
            #     Test128 Test128.fst -verify -verbose -fnouint128 -tmpdir .output/Test128.out || \
            #   echo "test/Test128.test (KreMLin)" >> $ORANGE_FILE; } &

            # { cd kremlin/test && timeout 480 ../krml -warn-error @4 -add-include '"kremstr.h"' \
            #     main-Server.c -tmpdir .output/Server.out -no-prefix Server -verify \
            #     Server.fst -verbose || \
            #   echo "test/Server.test (KreMLin)" >> $ORANGE_FILE; } &
            wait

            # Make it an orange if there's a git diff. Note: FStar_Version.ml is in the
            # .gitignore.
            echo "Searching for a diff in src/ocaml-output"
            if ! git diff --exit-code --name-only src/ocaml-output; then
                echo "GIT DIFF: the files in the list above have a git diff"
                { echo " - snapshot-diff (F*)" >>$ORANGE_FILE; }
            fi

            # We should not generate hints when building on Windows
            if [[ $localTarget == "uregressions-ulong" && "$OS" != "Windows_NT" ]]; then
                refresh_fstar_hints
            fi
        fi
    fi

    if [[ $(cat $status_file) != "true" ]]; then
        echo "F* regression failed"
        echo Failure >$result_file
    elif [[ $(cat $ORANGE_FILE) != "" ]]; then
        echo "F* regression had breakages"
        echo Success with breakages $(cat $ORANGE_FILE) >$result_file
    else
        echo "F* regression succeeded"
        echo Success >$result_file
    fi
}

# Some environment variables we want
export OCAMLRUNPARAM=b
export OTHERFLAGS="--print_z3_statistics --use_hints --query_stats"
export MAKEFLAGS="$MAKEFLAGS -Otarget"

cd FStar
build_fstar $target
cd ..
