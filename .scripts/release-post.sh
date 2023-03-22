# This file is to be included at the end of release scripts, to push
# the release


# Clear the version number, since everything has worked well so far
pushd "$FSTAR_HOST_HOME"
git checkout version.txt

# Publish the release with the GitHub CLI
gh="gh -R $git_org/FStar"
if [[ -n "$CI_BRANCH" ]] ; then
    branchname="$CI_BRANCH"
else
    branchname=master
fi

# push the tag if needed
if $need_to_push_tag ; then
    git push "https://$GH_TOKEN@github.com/$git_org/FStar.git" $my_tag
fi

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

# If we are running from CI, open a pull request
if [[ -n "$CI_BRANCH" ]] ; then
    $gh pr create --base "$CI_BRANCH" --title "Release $my_tag" --fill
fi

popd
