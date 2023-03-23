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

function git_add_fstar_snapshot () {
    if ! git diff-index --quiet --cached HEAD -- ocaml/*/generated ; then
        git ls-files ocaml/*/generated | xargs git add
    fi
}

function refresh_fstar_hints() {
    [[ -n "$DZOMO_GITHUB_TOKEN" ]] &&
    refresh_hints "https://$DZOMO_GITHUB_TOKEN@github.com/FStarLang/FStar.git" "git_add_fstar_snapshot" "regenerate hints + ocaml snapshot" "."
}

# Do we need to update the version number and publish a release?
function is_release_branch () {
    [[ "$1" = master || "$1" = _release ]]
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

    # Identify the committer
    git config --global user.name "Dzomo, the Everest Yak"
    git config --global user.email "everbld@microsoft.com"

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
    if is_release_branch $CI_BRANCH ; then
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

    # Publish a release
    if is_release_branch $CI_BRANCH ; then
        # Make and test a release
        FSTAR_HOME= KRML_HOME= GH_TOKEN=$DZOMO_GITHUB_TOKEN CI_BRANCH=$CI_BRANCH .scripts/process_build.sh
    fi
}

function fstar_binary_build () {
    fetch_karamel
    ./.scripts/process_build.sh && echo true >$status_file
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
        echo "GIT DIFF: the files in the list above have a git diff"
        echo false >$status_file
    fi

    # We should not generate hints when building on Windows
    if [[ $localTarget == "uregressions-ulong" && "$OS" != "Windows_NT" ]]; then
        refresh_fstar_hints || echo false >$status_file
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
