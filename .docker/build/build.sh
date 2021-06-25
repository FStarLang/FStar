#!/usr/bin/env bash

#set -x

set -e # abort on errors

target=$1
out_file=$2 # GM: This seems unused
threads=$3
branchname=$4

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

function fetch_vale() {
    if [[ ! -d vale ]]; then
        mkdir vale
    fi
    vale_version=$(<hacl-star/vale/.vale_version)
    vale_version=${vale_version%$'\r'}  # remove Windows carriage return, if it exists
    wget "https://github.com/project-everest/vale/releases/download/v${vale_version}/vale-release-${vale_version}.zip" -O vale/vale-release.zip
    rm -rf "vale/vale-release-${vale_version}"
    unzip -o vale/vale-release.zip -d vale
    rm -rf "vale/bin"
    mv "vale/vale-release-${vale_version}/bin" vale/
    chmod +x vale/bin/*.exe
    export_home VALE "$(pwd)/vale"
}

# By default, HACL* master works against F* stable. Can also be overridden.
function fetch_hacl() {
    if [ ! -d hacl-star ]; then
        git clone https://github.com/mitls/hacl-star hacl-star
    fi

    cd hacl-star
    git fetch origin
    local ref=$(jq -c -r '.RepoVersions["hacl_version"]' "$rootPath/.docker/build/config.json" )
    if [[ $ref == "" || $ref == "null" ]]; then
        echo "Unable to find RepoVersions.hacl_version on $rootPath/.docker/build/config.json"
        return -1
    fi

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
    local ref=$(jq -c -r '.RepoVersions["kremlin_version"]' "$rootPath/.docker/build/config.json" )
    if [[ $ref == "null" ]]; then
        echo "Unale to find RepoVersions.kremlin_version on $rootPath/.docker/build/config.json"
        return -1
    fi

    echo Switching to KreMLin $ref
    git reset --hard $ref
    cd ..
    export_home KREMLIN "$(pwd)/kremlin"
}

function make_kremlin() {
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

# By default, QuackyDucky master works against F* stable. Can also be overridden.
function fetch_qd() {
    if [ ! -d qd ]; then
        git clone https://github.com/project-everest/quackyducky qd
    fi

    cd qd
    git fetch origin
    local ref=$(jq -c -r '.RepoVersions["qd_version"]' "$rootPath/.docker/build/config.json" )
    if [[ $ref == "" || $ref == "null" ]]; then
        echo "Unable to find RepoVersions.qd_version on $rootPath/.docker/build/config.json"
        return -1
    fi

    echo Switching to QuackyDucky $ref
    git reset --hard $ref
    cd ..
    export_home QD "$(pwd)/qd"
}

function make_qd() {
    # Default build target is minimal, unless specified otherwise
    local localTarget
    if [[ $1 == "" ]]; then
        localTarget="quackyducky"
    else
        localTarget="$1"
    fi

    make -C qd -j $threads $localTarget ||
        (cd qd && git clean -fdx && make -j $threads $localTarget)
}


# By default, mitls-fstar master works against F* stable. Can also be overridden.
function fetch_mitls() {
    if [ ! -d mitls-fstar ]; then
        git clone https://github.com/mitls/mitls-fstar mitls-fstar
    fi
    cd mitls-fstar
    git fetch origin
    local ref=$(jq -c -r '.RepoVersions["mitls_version"]' "$rootPath/.docker/build/config.json" )
    if [[ $ref == "" || $ref == "null" ]]; then
        echo "Unable to find RepoVersions.mitls_version on $rootPath/.docker/build/config.json"
        return -1
    fi

    echo Switching to mitls-fstar $ref
    git reset --hard $ref
    git clean -fdx
    cd ..
    export_home MITLS "$(pwd)/mitls-fstar"
}

# Update the version number in version.txt and fstar.opam

function update_version_number () {
    # version suffix string
    local dev='~dev'

    # Read the latest version number
    last_version_number=$(sed 's!'"$dev"'!!' < version.txt)

    # If the only diffs are the snapshot hints and/or CI scripts,
    # then we don't need to
    # update the version number.  This check will fail if the version
    # number does not correspond to any existing release.  This is
    # sound, since if the version number is not a tag, it means that
    # it has already been updated since the latest release, so there
    # were more than just *.hints diffs, so we can update the version
    # number again.  Please mind the initial 'v' introducing the
    # version tag
    if git diff --exit-code v$last_version_number..HEAD -- ':(exclude)*.hints' ':(exclude).docker' ':(exclude).ci' ':(exclude).scripts' ; then
	echo "No diffs since latest release other than hints and/or CI scripts"
	return 0
    fi

    # Create a new version number.  Fail if it is identical to the
    # last version number. In other words, this task should be run at
    # most once a day.
    this_date=$(date '+%Y.%m.%d')
    version_number="$this_date""$dev"
    [[ $version_number != $last_version_number ]]

    # Update it in version.txt
    echo $version_number > version.txt

    # Update it in fstar.opam
    sed -i 's!^version:.*$!version: "'$version_number'"!' fstar.opam

    # Commit the new version number. This is guaranteed to be a
    # nonempty change, since version numbers were tested to be
    # different
    git add -u version.txt fstar.opam
    git commit -m "[CI] bump version number to $version_number"
}

function refresh_fstar_hints() {
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

    # Record the latest commit
    last_commit=$(git rev-parse HEAD)
    
    # Add all the hints, even those not under version control
    find $hints_dir/doc -iname '*.hints' | xargs git add
    find $hints_dir/examples -iname '*.hints' | xargs git add
    find $hints_dir/ulib -iname '*.hints' | xargs git add

    # Without the eval, this was doing weird stuff such as,
    # when $2 = "git ls-files src/ocaml-output/ | xargs git add",
    # outputting the list of files to stdout
    eval "$extra"

    # Commit only if changes were staged.
    # From: https://stackoverflow.com/a/2659808
    if ! git diff-index --quiet --cached HEAD -- ; then
	git commit -m "[CI] $msg"
    else
	echo "Hints/snapshot update: no diff"
    fi

    # Update the version number in version.txt and fstar.opam, and if
    # so, commit. Do this only for the master branch.
    if [[ $CI_BRANCH = master ]] ; then
	update_version_number
    fi

    # Memorize the latest commit (which might have been a version number update)
    commit=$(git rev-parse HEAD)

    # If nothing has been committed (neither hints nor version number), then exit.
    if [[ $commit = $last_commit ]] ; then
       echo "Nothing has been committed"
       return 0
    fi

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

    # Check if build hints branch exist on remote and remove it if it exists
    exist=$(git branch -a | egrep 'remotes/origin/BuildHints-'$CI_BRANCH | wc -l)
    if [ $exist == 1 ]; then
        git push $remote :BuildHints-$CI_BRANCH
    fi

    # Push.
    git checkout -b BuildHints-$CI_BRANCH
    git push $remote BuildHints-$CI_BRANCH
}

function fstar_binary_build () {
    fetch_kremlin
    ./.scripts/process_build.sh && echo true >$status_file
}

function fstar_docs_build () {
    # First - get fstar built
    # Second - run fstar with the --doc flag
    make -C src/ocaml-output clean && \
        make -C src/ocaml-output -j $threads && \
        .ci/fsdoc.sh && \
        echo true >$status_file
}

function fstar_default_build () {
    localTarget=$1

    if [[ $localTarget == "uregressions-ulong" ]]; then
        export OTHERFLAGS="--record_hints $OTHERFLAGS"
    fi

    # Start fetching while we build F*
    fetch_kremlin &
    fetch_hacl &
    fetch_qd &
    fetch_mitls &

    # Build F*, along with fstarlib
    if ! make -C src -j $threads utest-prelude; then
        echo Warm-up failed
        echo Failure >$result_file
        return 1
    fi

    export_home FSTAR "$(pwd)"

    wait # for fetches above

    # The commands above were executed in sub-shells and their EXPORTs are not
    # propagated to the current shell. Re-do.
    export_home HACL "$(pwd)/hacl-star"
    export_home EVERCRYPT "$(pwd)/hacl-star/providers"
    export_home KREMLIN "$(pwd)/kremlin"
    export_home QD "$(pwd)/qd"

    # Fetch and build subprojects for orange tests
    make_kremlin &
    make_qd &
    wait

    # fetch_vale depends on fetch_hacl for the hacl-star/vale/.vale_version file
    fetch_vale

    # Once F* is built, run its main regression suite, along with more relevant
    # tests.
    {
        $gnutime make -C src -j $threads -k $localTarget && echo true >$status_file
        echo Done building FStar
    } &

    {
        OTHERFLAGS='--warn_error -276 --use_hint_hashes' \
        NOOPENSSLCHECK=1 make -C hacl-star -j $threads min-test ||
            {
                echo "Error - Hacl.Hash.MD.fst.checked (HACL*)"
                echo " - min-test (HACL*)" >>$ORANGE_FILE
            }
    } &

    # The LowParse test suite is now in project-everest/everparse
    {
        $gnutime make -C qd -j $threads -k lowparse-fstar-test || {
            echo "Error - LowParse"
            echo " - min-test (LowParse)" >>$ORANGE_FILE
        }
    } &

    # We now run all (hardcoded) tests in mitls-fstar@master
    {
        # First regenerate dependencies and parsers (maybe not
        # really needed for now, since any test of this set
        # already does this; but it will become necessary if
        # we later decide to perform these tests in parallel,
        # to avoid races.)
        make -C mitls-fstar/src/tls refresh-depend

        OTHERFLAGS=--use_hint_hashes make -C mitls-fstar/src/tls -j $threads StreamAE.fst-ver ||
            {
                echo "Error - StreamAE.fst-ver (mitls)"
                echo " - StreamAE.fst-ver (mitls)" >>$ORANGE_FILE
            }

        OTHERFLAGS=--use_hint_hashes make -C mitls-fstar/src/tls -j $threads Pkg.fst-ver ||
            {
                echo "Error - Pkg.fst-ver (mitls verify)"
                echo " - Pkg.fst-ver (mitls verify)" >>$ORANGE_FILE
            }
    } &

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
        refresh_fstar_hints || echo false >$status_file
    fi
}


function build_fstar() {
    local localTarget=$1

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
        fstar_binary_build
    elif [[ $localTarget == "fstar-docs" ]]; then
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

cd FStar
rootPath=$(pwd)
build_fstar $target
cd ..
