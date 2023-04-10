#!/usr/bin/env bash

# This script is called by the release.yml GitHub Actions workflow
# via .docker/release.Dockerfile, to create a tag when creating a new release

# Sorry, everyone
if (( ${BASH_VERSION%%.*} < 4 )); then
  echo "This script requires Bash >= 4. On OSX, try: brew install bash"
  exit 1
fi

# Any error is fatal.
set -e
set -o pipefail

set -x

git_org=FStarLang
git_remote=

# Check if the user has provided a GitHub authentication token
[[ -n $GH_TOKEN ]]

# Detect the F* directory and enter it
FSTAR_HOST_HOME=$(cd `dirname $0`/.. && pwd)
[[ -n $FSTAR_HOST_HOME ]]
pushd "$FSTAR_HOST_HOME"

# Make sure we are starting in the right place (F* repository)
if ! [[ -d ulib ]]; then
  echo "This script is intended to be run from the root of the F* repository"
  exit 1
fi

# Figure out the branch
CI_BRANCH=$(git rev-parse --abbrev-ref HEAD)
echo "Current branch_name=$CI_BRANCH"

# Fail if the state is dirty
# NOTE: --ignore-cr-at-eol is a recent option,
# so we should ignore it if it is not there
git diff --staged --exit-code --ignore-cr-at-eol || git diff --staged --exit-code
git diff --exit-code --ignore-cr-at-eol || git diff --exit-code

# Detect the F* version number
git fetch --tags $git_remote
if [[ -n $FSTAR_VERSION ]] ; then
    # It is provided by the user
    my_tag="$FSTAR_VERSION"
elif my_tag=$(git describe --tags --exact-match) ; then
    # It is the tag of the current commit
    # Check that there is only one tag
    [[ $(echo $my_tag | wc -w) -eq 1 ]]
else
    # Read the tag from version.txt, but stripping away the ~dev
    # marker.  version.txt is assumed to have been updated by
    # update_version_number in .docker/build/build.sh . Please mind
    # the 'v' introducing the tag.
    dev='~dev'
    my_tag=v$(sed 's!'"$dev"'!!' < version.txt)
fi

# Check if the commit pointed to by that tag (if any) points to the current commit
this_commit=$(git rev-parse HEAD)
rm -f .need_to_push_tag
if tagged_commit=$(git show-ref --tags --hash "$my_tag") && [[ -n $tagged_commit ]] ; then
    [[ $tagged_commit = $this_commit ]]
else
    # the tag does not exist, but check that it does not correspond to
    # an existing branch
    # so we can apply it
    # and we will need to push it before pushing the release
    if test_ref=$(git show-ref "$my_tag") ; then
        [[ -z "$test_ref" ]]
    fi
    echo "Checking whether new tags are allowed"
    [[ -z "$FSTAR_NO_NEW_TAG" ]]
    touch .need_to_push_tag
    git tag "$my_tag"
fi

# Overwrite the version number. We need to strip the initial v. Note:
# this version number will not be committed, because, if a user
# compiles from master, then they should have a dev version number,
# but the version number used at compilation time will be read from
# version.txt
CURRENT_VERSION=$(echo $my_tag | sed 's!^v!!')
echo $CURRENT_VERSION > version.txt

# Exit the F* directory
popd
