# This file is to be included at the end of release scripts, to push
# the release


# Clear the version number, since everything has worked well so far
pushd "$FSTAR_HOST_HOME"
git checkout version.txt

# Publish the release with the GitHub CLI
gh="gh -R $git_org/FStar"
branchname=master

function upload_archive () {
    archive="$1"
    if ! $gh release view $my_tag ; then
        $gh release create --prerelease --generate-notes --target $branchname $my_tag $archive
    else
        $gh release upload $my_tag $archive
    fi
}

upload_archive $BUILD_PACKAGE
rm -rf release
popd
