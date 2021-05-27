#!/bin/bash
set -e
set -x

git_org=tahina-pro
git_remote=tahina-pro

# Check if the user has provided a GitHub authentication token
[[ -n $SATS_TOKEN ]]

# Detect the F* directory and enter it
fstar_home=$(cd `dirname $0`/.. && pwd)
pushd "$fstar_home"

# Fail if the state is dirty
git diff --staged --exit-code
git diff --exit-code

# Detect the F* version number
if [[ -n $FSTAR_VERSION ]] ; then
    # It is provided by the user
    my_tag="$FSTAR_VERSION"
elif my_tag=$(git describe --exact-match) ; then
    # It is the tag of the current commit
    # Check that there is only one tag
    [[ $(echo $my_tag | wc -w) -eq 1 ]]
else
    # Generate a new tag under the vYYYY.MM.DD format
    my_tag=$(date '+v%Y.%m.%d')
fi

# Check if the commit pointed to by that tag (if any) points to the current commit
this_commit=$(git show --no-patch --format=%h)
git_push_tag_cmd=true
if tagged_commit=$(git show --no-patch --format=%h $my_tag) ; then
    [[ $tagged_commit = $this_commit ]]
else
    # the tag does not exist, so we can apply it
    # and we will need to push it before pushing the release
    git_push_tag_cmd="git push $git_remote $my_tag"
    git tag "$my_tag"
fi

# Overwrite the version number. We need to strip the initial v. Note:
# this version number will not be committed, because, if a user
# compiles from master, then they should have a dev version number,
# but the version number used at compilation time will be read from
# version.txt
my_version=$(echo $my_tag | sed 's!^v!!')
echo $my_version > version.txt

# Exit the F* directory
popd

# Build the package
docker build -t fstar-package -f "$fstar_home/.docker/package.Dockerfile" "$fstar_home"

# Extract the package from the image
mkdir release
docker container create --name container-fstar-package fstar-package
docker cp container-fstar-package:/home/test/fstar.tar.gz release/fstar.tar.gz
docker cp container-fstar-package:/home/test/version_platform.txt release/fstar.tar.gz
docker container rm container-fstar-package
docker image rm -f fstar-package

# Rename the package to its intended name with version and platform
package_name=$(cat version_platform.txt)
mv release/fstar.tar.gz release/$package_name

# Clear the version number and push the tag, since everything has worked well so far
pushd "$fstar_home"
git checkout version.txt
$git_push_tag_cmd
popd

# Publish the release
docker build -t fstar-release \
       --build_arg SATS_FILE=$package_name \
       --build-arg SATS_TAG=$my_tag \
       --build-arg SATS_COMMITISH=$this_commit \
       --build-arg SATS_TOKEN=$SATS_TOKEN \
       --build-arg SATS_SLUG=$git_org/FStar \
       -f "$fstar_home/.docker/release.Dockerfile" \
       release
docker image rm -f fstar-release

# Final cleanup
rm -rf release
