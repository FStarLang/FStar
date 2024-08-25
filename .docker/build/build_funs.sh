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
        git clone --depth 1 https://github.com/FStarLang/karamel karamel
    fi

    cd karamel
    git fetch origin
    local ref=$(jq -c -r '.RepoVersions["karamel_version"]' "$rootPath/.docker/build/config.json" )
    if [[ $ref == "null" ]]; then
        echo "Unable to find RepoVersions.karamel_version on $rootPath/.docker/build/config.json"
        return -1
    fi

    echo Switching to KaRaMeL $ref
    git reset --hard $ref
    cd ..
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
        fetch_karamel
        make_karamel_pre
        export_home KRML "$(pwd)/karamel"
        export FSTAR_CI_TEST_KARAMEL=1
    fi &

    # Build F*, along with fstarlib
    if ! make -j $threads ci-pre; then
        echo Warm-up failed
        echo Failure >$result_file
        return 1
    fi

    # Clean temporary build files, not needed and saves
    # several hundred MB
    make clean-buildfiles || true

    export_home FSTAR "$(pwd)"

    wait # for fetches above

    # Once F* is built, run its main regression suite. This also runs the karamel
    # test (unless CI_NO_KARAMEL is set).
    $gnutime make -j $threads -k ci-post && echo true >$status_file
    echo Done building FStar

    if [ -z "${FSTAR_CI_NO_GITDIFF}" ]; then
        # Make it a hard failure if there's a git diff in the snapshot. First check for
        # extraneous files, then for a diff.
        echo "Searching for a diff in ocaml/*/generated"
        git status ocaml/*/generated # Print status for log

        # If there's any output, i.e. any file not in HEAD, fail
        if git ls-files --others --exclude-standard -- ocaml/*/generated | grep -q . ; then
            echo " *** GIT DIFF: there are extraneous files in the snapshot"
            echo false >$status_file
        fi

        # If there's a diff in existing files, fail
        if ! git diff --exit-code ocaml/*/generated ; then
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
