# Clear the version number and push the tag, since everything has worked well so far
pushd "$FSTAR_HOST_HOME"
git checkout version.txt
$git_push_tag_cmd
popd

# Publish the release
docker build -t fstar-release \
       --build-arg SATS_FILE=$BUILD_PACKAGE \
       --build-arg SATS_TAG=$my_tag \
       --build-arg SATS_COMMITISH=$this_commit \
       --build-arg SATS_TOKEN=$SATS_TOKEN \
       --build-arg SATS_SLUG=$git_org/FStar \
       -f "$FSTAR_HOST_HOME/.docker/release.Dockerfile" \
       release
docker image rm -f fstar-release

# Final cleanup
rm -rf release
