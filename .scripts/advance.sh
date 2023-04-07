#!/usr/bin/env bash

# This script refreshes hints and the F* snapshot, and updates the
# version number from version.txt and opam

set -e
set -x

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

    # Create a pull request
    $gh pr create --base "$CI_BRANCH" --title "Advance to $(cat version.txt)" --fill
}

release () {
        # Make and test a release
        FSTAR_HOME= KRML_HOME= GH_TOKEN=$DZOMO_GITHUB_TOKEN CI_BRANCH=$CI_BRANCH .scripts/process_build.sh
}

build_and_refresh () {
    OTHERFLAGS='--record_hints' make -j "$CI_THREADS" ci-uregressions-ulong
    refresh_fstar_hints
}

build_refresh_and_release () {
    build_and_refresh
    if is_release_branch $CI_BRANCH ; then
        release
    fi
}

# Switch back to the F* root directory (which we assume is the parent
# of the directory where this script lives
cd $(cd `dirname $0`/.. && pwd)

# Figure out the branch
CI_BRANCH=$(git rev-parse --abbrev-ref HEAD)
echo "Current branch_name=$CI_BRANCH"

# How many threads do we need?
if [[ -z "$CI_THREADS" ]] ; then
    CI_THREADS=24
fi

# We need a GitHub token
if [[ -z "$DZOMO_GITHUB_TOKEN" ]] ; then
    echo "Please provide a GitHub token into the DZOMO_GITHUB_TOKEN environment variable"
    exit 1
fi

gh="env GH_TOKEN=$DZOMO_GITHUB_TOKEN gh -R FStarLang/FStar"

case "$1" in
    (refresh_fstar_hints)
        refresh_fstar_hints
        ;;
    (build_refresh_and_release)
        build_refresh_and_release
        ;;
    (build_and_refresh)
        build_and_refresh
        ;;
    (*)
        echo "What do you want to do? (refresh_fstar_hints | build_refresh_and_release | build_and_refresh)"
        exit 1
esac
