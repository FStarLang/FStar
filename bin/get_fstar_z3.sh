#!/usr/bin/env bash
set -euo pipefail

kernel="$(uname -s)"
case "$kernel" in
  CYGWIN*) kernel=Windows ;;
esac

arch="$(uname -m)"
case "$arch" in
  arm64) arch=aarch64 ;;
esac

declare -A release_url
release_url["Linux-x86_64-4.8.5"]="https://github.com/Z3Prover/z3/releases/download/Z3-4.8.5/z3-4.8.5-x64-ubuntu-16.04.zip"
release_url["Darwin-x86_64-4.8.5"]="https://github.com/Z3Prover/z3/releases/download/Z3-4.8.5/z3-4.8.5-x64-osx-10.14.2.zip"
release_url["Windows-x86_64-4.8.5"]="https://github.com/Z3Prover/z3/releases/download/Z3-4.8.5/z3-4.8.5-x64-win.zip"
release_url["Linux-x86_64-4.13.3"]="https://github.com/Z3Prover/z3/releases/download/z3-4.13.3/z3-4.13.3-x64-glibc-2.35.zip"
release_url["Linux-aarch64-4.13.3"]="https://github.com/Z3Prover/z3/releases/download/z3-4.13.3/z3-4.13.3-arm64-glibc-2.34.zip"
release_url["Darwin-x86_64-4.13.3"]="https://github.com/Z3Prover/z3/releases/download/z3-4.13.3/z3-4.13.3-x64-osx-13.7.zip"
release_url["Darwin-aarch64-4.13.3"]="https://github.com/Z3Prover/z3/releases/download/z3-4.13.3/z3-4.13.3-arm64-osx-13.7.zip"
release_url["Windows-x86_64-4.13.3"]="https://github.com/Z3Prover/z3/releases/download/z3-4.13.3/z3-4.13.3-x64-win.zip"

trap "exit 1" HUP INT PIPE QUIT TERM
cleanup() {
  if [ -n "${tmp_dir:-}" ]; then
    rm -rf "$tmp_dir"
  fi
}
trap "cleanup" EXIT

download_z3() {
  local url="$1"
  local version="$2"
  local destination_file_name="$3"

  if [ -z "${tmp_dir:-}" ]; then
    tmp_dir="$(mktemp -d --tmpdir get_fstar_z3.XXXXXXX)"
  fi

  echo ">>> Downloading Z3 $version from $url ..."
  local base_name="$(basename "$url")"

  local z3_path="${base_name%.zip}/bin/z3"
  if [ "$kernel" = Windows ]; then z3_path="$z3_path.exe"; fi

  pushd "$tmp_dir"
  curl -L "$url" -o "$base_name"
  unzip "$base_name" "$z3_path"
  popd

  install -m0755 "$tmp_dir/$z3_path" "$destination_file_name"
  echo ">>> Installed Z3 $version to $destination_file_name"
}

dest_dir="$1"
if [ -z "$dest_dir" ]; then
  echo "Usage: get_fstar_z3.sh destination/directory/bin"
  exit 1
fi

mkdir -p "$dest_dir"

for z3_ver in 4.8.5 4.13.3; do
  key="$kernel-$arch-$z3_ver"
  url="${release_url[$key]:-}"

  if [[ "$key" == "Darwin-aarch64-4.8.5" ]]; then
    # NOTE: The is no ARM build of Z3 4.8.5 in the releases page, but
    # the x64 build works fine in MacOS using Rosetta, so we can just download
    # that. However make sure to print out a message to let the user know.
    echo ">>> NOTE! This script will install an x64 version of Z3 4.8.5."
    echo ">>> Make sure Rosetta 2 is installed in your system so it can be run."
    url="${release_url["Darwin-x86_64-4.8.5"]}"
  fi

  destination_file_name="$dest_dir/z3-$z3_ver"
  if [[ "$kernel" = Windows ]]; then destination_file_name="$destination_file_name.exe"; fi

  if [[ -f "$destination_file_name" ]]; then
    echo ">>> Z3 $z3_ver already downloaded to $destination_file_name"
  elif [[ -z "$url" ]]; then
    echo ">>> Z3 $z3_ver not available for this architecture, skipping..."
  else
    download_z3 "$url" "$z3_ver" "$destination_file_name"
  fi
done
