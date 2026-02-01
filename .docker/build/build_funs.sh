function export_home() {
    local home_path=""
    if command -v cygpath >/dev/null 2>&1; then
        home_path=$(cygpath -m "$2")
    else
        home_path="$2"
    fi

    export $1_HOME=$home_path

    # Update .bashrc file
    token=$1_HOME=
    if grep -q "$token" ~/.bashrc; then
        sed -i -E "s,$token.*,$token$home_path," ~/.bashrc
    else
        echo "export $1_HOME=$home_path" >> ~/.bashrc
    fi
}

# By default, karamel master works against F* stable. Can also be overridden.
function fetch_karamel() {
    local ref=$(jq -c -r '.RepoVersions["karamel_version"]' "$rootPath/.docker/build/config.json" )
    if [[ $ref == "null" ]]; then
        echo "Unable to find RepoVersions.karamel_version on $rootPath/.docker/build/config.json"
        return -1
    fi

    if [ ! -d karamel ]; then
        # If we just want origin/master, we can shallow clone. Otherwise no,
        # as we'll need to switch to some other branch/commit.
        if [ x"$ref" = x"origin/master" ]; then
            SHALLOW="--depth 1"
        else
            SHALLOW=""
        fi
        git clone ${SHALLOW} https://github.com/FStarLang/karamel karamel
    fi

    echo Switching to KaRaMeL $ref
    git -C karamel reset --hard $ref

    export_home KRML "$(pwd)/karamel"

    # Install the Karamel dependencies
    pushd $KRML_HOME
    OPAMYES=true .docker/build/install-other-deps.sh
    popd
}

function make_karamel_pre() {
    make -C karamel -j $threads minimal
}

function fstar_docs_build () {
    # First - get fstar built
    # Second - run fstar with the --doc flag
    OTHERFLAGS='--admit_smt_queries true' make -j $threads && \
        .ci/fsdoc.sh && \
        echo true >$status_file
}

function fstar_default_build () {
    if [[ -n "$CI_RECORD_HINTS" ]]; then
        export OTHERFLAGS="--record_hints $OTHERFLAGS"
    fi

    # Start fetching and building karamel while we build F*
    if [[ -z "$CI_NO_KARAMEL" ]] ; then
        export FSTAR_CI_TEST_KARAMEL=1
        export_home KRML "$(pwd)/karamel"
        (fetch_karamel ; make_karamel_pre) &
    fi

    # Build F* using dune (replaces old make ci-pre)
    echo "Building F* with dune..."
    
    # Stage 0: Bootstrap compiler
    dune build --root=stage0/dune -j $threads
    dune install --root=stage0/dune --prefix=stage0/out
    export FSTAR_EXE=$(pwd)/stage0/out/bin/fstar.exe
    
    # Extract, Stage 1, Stage 2
    dune build @extract-stage1 -j $threads
    dune build @stage1 -j $threads
    dune build @stage2 -j $threads
    
    if [ $? -ne 0 ]; then
        echo Build failed
        echo Failure >$result_file
        return 1
    fi

    export_home FSTAR "$(pwd)"

    wait # for fetches above

    # Run tests (replaces old make ci-post)
    echo "Running tests with dune..."
    $gnutime dune runtest -j $threads && echo true >$status_file
    echo Done building FStar

    if [ -z "${FSTAR_CI_NO_GITDIFF}" ]; then
        # Make it a hard failure if there's a git diff in the snapshot. First check for
        # extraneous files, then for a diff.
        echo "Searching for a diff in src/extracted"
        git status src/extracted # Print status for log

        # If there's any output, i.e. any file not in HEAD, fail
        if git ls-files --others --exclude-standard -- src/extracted | grep -q . ; then
            echo " *** GIT DIFF: there are extraneous files in the snapshot"
            echo false >$status_file
        fi

        # If there's a diff in existing files, fail
        if ! git diff --exit-code src/extracted ; then
            echo " *** GIT DIFF: the files in the list above have a git diff"
            echo false >$status_file
        fi
    fi
}


function build_fstar() {
    local localTarget=$1

    echo Failure >$result_file

    # $status_file is the name of a file that contains true if and
    # only if the F* regression suite failed, false otherwise
    echo false >$status_file

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

    if [[ $localTarget == "fstar-docs" ]]; then
        fstar_docs_build
    elif [[ $localTarget == "ci" ]]; then
        fstar_default_build
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
export V=1 # Make sure to get verbose output from makefiles
export OCAMLRUNPARAM=b
export MAKEFLAGS="$MAKEFLAGS -Otarget" # Group make output by target
