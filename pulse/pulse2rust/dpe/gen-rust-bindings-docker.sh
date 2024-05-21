#!/usr/bin/env bash
set -e
set -x

# chdir to the current directory
unset CDPATH
cd "$( dirname "${BASH_SOURCE[0]}" )"

if  [[ -z "$PULSE_HOME" ]] ; then
    # assume share/pulse/examples/dice/common/hacl-rust
    PULSE_HOME=$(realpath $(pwd)/../../)
fi

# regenerate EverCrypt*.h
./gen-evercrypt-h.sh

# generate EverCrypt*.rs in a Docker image
DOCKER_IMAGE_NAME=haclrustbindingsimg"$$"
echo $DOCKER_IMAGE_NAME
docker build -t $DOCKER_IMAGE_NAME -f rust.Dockerfile .

DPE_OUTPUT_DIR=$PULSE_HOME/pulse2rust/dpe/src/generated

# copy everCrypt.rs from the Docker image
DOCKER_CONTAINER_NAME=haclrustbindingscont"$$"
docker create --name $DOCKER_CONTAINER_NAME $DOCKER_IMAGE_NAME
docker cp $DOCKER_CONTAINER_NAME:/usr/src/hacl/evercrypt_gen.rs $DPE_OUTPUT_DIR/
docker cp $DOCKER_CONTAINER_NAME:/usr/src/hacl/l0core_gen.rs $DPE_OUTPUT_DIR/
docker rm $DOCKER_CONTAINER_NAME
