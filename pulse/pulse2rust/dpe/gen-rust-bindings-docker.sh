#!/usr/bin/env bash

#
# Creates rust bindings for external dependencies of DPE
#   using docker
#

set -e
set -x

# chdir to the current directory
unset CDPATH
cd "$( dirname "${BASH_SOURCE[0]}" )"

if  [[ -z "$PULSE_HOME" ]] ; then
    PULSE_HOME=$(realpath $(pwd)/../../)
fi

# regenerate EverCrypt*.h and L0Core.h
./gen-external-h.sh

# generate evercrypt_gen.rs and l0core_gen in a Docker image
DOCKER_IMAGE_NAME=haclrustbindingsimg"$$"
echo $DOCKER_IMAGE_NAME
docker build -t $DOCKER_IMAGE_NAME -f rust.Dockerfile .

DPE_OUTPUT_DIR=$PULSE_HOME/pulse2rust/dpe/src/generated

# copy evercrypt_gen.rs and l0core_gen.rs from the Docker image
DOCKER_CONTAINER_NAME=haclrustbindingscont"$$"
docker create --name $DOCKER_CONTAINER_NAME $DOCKER_IMAGE_NAME
docker cp $DOCKER_CONTAINER_NAME:/usr/src/hacl/evercrypt_gen.rs $DPE_OUTPUT_DIR/
docker cp $DOCKER_CONTAINER_NAME:/usr/src/hacl/l0core_gen.rs $DPE_OUTPUT_DIR/
docker rm $DOCKER_CONTAINER_NAME
