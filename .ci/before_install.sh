#!/usr/bin/env bash

echo -e "\e[31m=== Running $0 ===\e[0m"

set -e

if [[ "$TRAVIS_OS_NAME" == "osx" ]]; then
  brew update;
fi

if [[ "$TRAVIS_OS_NAME" == "linux" ]]; then
  sudo add-apt-repository --yes ppa:avsm/ppa;
  sudo add-apt-repository --yes ppa:ubuntu-toolchain-r/test;
  sudo add-apt-repository --yes ppa:0k53d-karl-f830m/openssl;
  sudo apt-get -qq update;
fi
