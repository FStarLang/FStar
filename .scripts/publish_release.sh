#!/usr/bin/env bash

# This script is called by the release.yml GitHub Actions workflow
# for Linux (via .docker/release.Dockerfile) and Mac

set -e
set -x

# We need two FSTAR_HOMEs in this script: one for the host (from where
# we build F*) and one for the package (from where we test the
# obtained binary). FSTAR_HOST_HOME is the former.
if [[ -z "$FSTAR_HOST_HOME" ]] ; then
  FSTAR_HOST_HOME=$(cd `dirname $0`/.. && pwd)
fi
pushd "$FSTAR_HOST_HOME"

echo "*** Rename package ***"
dev='~dev'
CURRENT_VERSION=$(cat version.txt | sed 's!'"$dev"'!!' | sed 's!'"\r"'$!!')
my_tag="v$CURRENT_VERSION"
if [[ -z $OS ]] ; then
    OS=$(uname)
fi
if echo $OS | grep -i '^cygwin' ; then
    OS=Windows_NT
fi
if [[ $OS = Windows_NT ]] ; then
    ext=.zip
else
    ext=.tar.gz
fi
TYPE="_${OS}_$(uname -m)"
PACKAGE_NAME=fstar_$CURRENT_VERSION$TYPE
BUILD_PACKAGE_FILENAME=$PACKAGE_NAME$ext
BUILD_PACKAGE="$FSTAR_HOST_HOME/src/ocaml-output/$BUILD_PACKAGE_FILENAME"
rm -rf "$BUILD_PACKAGE" src/ocaml-output/fstar
mv "$FSTAR_HOST_HOME/src/ocaml-output/fstar$ext" "$BUILD_PACKAGE"

# Clear the version number, since everything has worked well so far
# Not necessary if we are not in a git clone
# (e.g. the working copy was downloaded with the GitHub REST API,
# or from a source archive)
git checkout version.txt || true

# Publish the release with the GitHub CLI
if [[ -z "$git_org" ]] ; then
    git_org=FStarLang
fi
gh="gh -R $git_org/FStar"
if [[ -n "$CI_BRANCH" ]] ; then
    branchname="$CI_BRANCH"
else
    branchname=master
fi

# push the tag if needed
if [[ -f .need_to_push_tag ]] ; then
    git push "https://$GH_TOKEN@github.com/$git_org/FStar.git" $my_tag
fi

function upload_archive () {
    archive="$1"
    if ! $gh release view $my_tag ; then
        [[ -f .need_to_push_tag ]]
        $gh release create --prerelease --generate-notes --target $branchname $my_tag $archive
    else
        $gh release upload $my_tag $archive
    fi
}

upload_archive $BUILD_PACKAGE
rm -rf $BUILD_PACKAGE
rm -f .need_to_push_tag

popd
