# Make sure to get verbose output from makefiles
export V=1

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
    if [ ! -d karamel ]; then
        git clone https://github.com/FStarLang/karamel karamel
    fi

    cd karamel
    git fetch origin
    local ref=$(jq -c -r '.RepoVersions["karamel_version"]' "$rootPath/.docker/build/config.json" )
    if [[ $ref == "null" ]]; then
        echo "Unale to find RepoVersions.karamel_version on $rootPath/.docker/build/config.json"
        return -1
    fi

    echo Switching to KaRaMeL $ref
    git reset --hard $ref
    cd ..
    export_home KRML "$(pwd)/karamel"

    # Install the Karamel dependencies
    pushd $KRML_HOME
    .docker/build/install-other-deps.sh
    popd
}

function make_karamel() {
    # Default build target is minimal, unless specified otherwise
    local localTarget
    if [[ $1 == "" ]]; then
        localTarget="minimal"
    else
        localTarget="$1"
    fi

    make -C karamel -j $threads $localTarget ||
        (cd karamel && git clean -fdx && make -j $threads $localTarget)
    OTHERFLAGS='--admit_smt_queries true' make -C karamel/krmllib -j $threads
    export PATH="$(pwd)/karamel:$PATH"
}

function fstar_docs_build () {
    # First - get fstar built
    # Second - run fstar with the --doc flag
    OTHERFLAGS='--admit_smt_queries true' make -j $threads && \
        .ci/fsdoc.sh && \
        echo true >$status_file
}

function fstar_default_build () {
    localTarget=$1

    if [[ $localTarget == "uregressions-ulong" ]]; then
        export OTHERFLAGS="--record_hints $OTHERFLAGS"
    fi

    # Start fetching while we build F*
    if [[ -z "$CI_NO_KARAMEL" ]] ; then
        fetch_karamel
    fi &

    # Build F*, along with fstarlib
    if ! make -j $threads ci-utest-prelude; then
        echo Warm-up failed
        echo Failure >$result_file
        return 1
    fi

    export_home FSTAR "$(pwd)"

    wait # for fetches above

    # Build karamel if enabled
    if [[ -z "$CI_NO_KARAMEL" ]] ; then
        # The commands above were executed in sub-shells and their EXPORTs are not
        # propagated to the current shell. Re-do.
        export_home KRML "$(pwd)/karamel"
        make_karamel
    fi

    # Once F* is built, run its main regression suite.
    $gnutime make -j $threads -k ci-$localTarget && echo true >$status_file
    echo Done building FStar

    # Make it a hard failure if there's a git diff. Note: FStar_Version.ml is in the
    # .gitignore.
    echo "Searching for a diff in ocaml/*/generated"
    if ! git diff --exit-code ocaml/*/generated ; then
        echo " *** GIT DIFF: the files in the list above have a git diff"
        echo false >$status_file
    fi

    # We should not generate hints when building on Windows
    if [[ $localTarget == "uregressions-ulong" && "$OS" != "Windows_NT" ]]; then
        .scripts/advance.sh refresh_fstar_hints || echo false >$status_file
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
    else
        fstar_default_build $target
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
export OTHERFLAGS="--use_hints --query_stats"
export MAKEFLAGS="$MAKEFLAGS -Otarget"
