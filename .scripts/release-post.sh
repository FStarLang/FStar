# This file is to be included at the end of release scripts, to push
# the release


# Clear the version number, since everything has worked well so far
pushd "$FSTAR_HOST_HOME"
git checkout version.txt

# Publish the release
docker build -t fstar-release \
       --build-arg SATS_FILE=$BUILD_PACKAGE \
       --build-arg SATS_TAG=$my_tag \
       --build-arg SATS_COMMITISH=$this_commit \
       --build-arg SATS_TOKEN=$SATS_TOKEN \
       --build-arg SATS_SLUG=$git_org/FStar \
       -f ".docker/release.Dockerfile" \
       release
docker image rm -f fstar-release
rm -rf release
popd
