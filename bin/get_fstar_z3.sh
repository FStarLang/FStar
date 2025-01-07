#!/usr/bin/env bash
set -euo pipefail

full_install=false

kernel="$(uname -s)"
case "$kernel" in
  CYGWIN*) kernel=Windows ;;
esac

arch="$(uname -m)"
case "$arch" in
  arm64) arch=aarch64 ;;
esac

release_url=(
  "Linux-x86_64-4.8.5":"https://github.com/Z3Prover/z3/releases/download/Z3-4.8.5/z3-4.8.5-x64-ubuntu-16.04.zip"
  "Darwin-x86_64-4.8.5":"https://github.com/Z3Prover/z3/releases/download/Z3-4.8.5/z3-4.8.5-x64-osx-10.14.2.zip"
  "Windows-x86_64-4.8.5":"https://github.com/Z3Prover/z3/releases/download/Z3-4.8.5/z3-4.8.5-x64-win.zip"
  "Linux-x86_64-4.13.3":"https://github.com/Z3Prover/z3/releases/download/z3-4.13.3/z3-4.13.3-x64-glibc-2.35.zip"
  "Linux-aarch64-4.13.3":"https://github.com/Z3Prover/z3/releases/download/z3-4.13.3/z3-4.13.3-arm64-glibc-2.34.zip"
  "Darwin-x86_64-4.13.3":"https://github.com/Z3Prover/z3/releases/download/z3-4.13.3/z3-4.13.3-x64-osx-13.7.zip"
  "Darwin-aarch64-4.13.3":"https://github.com/Z3Prover/z3/releases/download/z3-4.13.3/z3-4.13.3-arm64-osx-13.7.zip"
  "Windows-x86_64-4.13.3":"https://github.com/Z3Prover/z3/releases/download/z3-4.13.3/z3-4.13.3-x64-win.zip"
)

get_url() {
  local key elem
  key="$1"

  for elem in "${release_url[@]}"; do
    if [ "${elem%%:*}" = "$key" ]; then
      echo -n "${elem#*:}"
      break
    fi
  done
}

trap "exit 1" HUP INT PIPE QUIT TERM
cleanup() {
  if [ -n "${tmp_dir:-}" ]; then
    rm -rf "$tmp_dir"
  fi
}
trap "cleanup" EXIT

download_z3() {
  local url version destination_file_name base_name z3_path
  url="$1"
  version="$2"
  destination_file_name="$3"

  if [ -z "${tmp_dir:-}" ]; then
    tmp_dir="$(mktemp -d --tmpdir get_fstar_z3.XXXXXXX)"
  fi

  echo ">>> Downloading Z3 $version from $url ..."
  base_name="$(basename "$url")"

  z3_path="${base_name%.zip}/bin/z3"
  if [ "$kernel" = Windows ]; then z3_path="$z3_path.exe"; fi

  pushd "$tmp_dir"
  curl -L "$url" -o "$base_name"

  unzip "$base_name" "$z3_path"
  popd
  install -m0755 "$tmp_dir/$z3_path" "$destination_file_name"
  echo ">>> Installed Z3 $version to $destination_file_name"
}

full_install_z3() {
  local url version dest_dir base_name

  url="$1"
  version="$2"
  dest_dir="$3"

  mkdir -p "$dest_dir/z3-$version"
  pushd "$dest_dir/z3-$version"

  echo ">>> Downloading Z3 $version from $url ..."
  base_name="$(basename "$url")"
  curl -L "$url" -o "$base_name"

  unzip "$base_name"
  mv "${base_name%.zip}"/* .
  rmdir "${base_name%.zip}"
  rm "$base_name"
  popd
}

if [ "$1" == "--full" ]; then
  # Passing --full xyz/ will create a tree like
  #  xyz/z3-4.8.5/bin/z3
  #  xyz/z3-4.13.3/bin/z3
  # (plus all other files in each package). This is used
  # for our binary packages which include Z3.
  full_install=true;
  shift;
fi

dest_dir="$1"
if [ -z "$dest_dir" ]; then
  echo "Usage: get_fstar_z3.sh destination/directory/bin"
  exit 1
fi

mkdir -p "$dest_dir"

for z3_ver in 4.8.5 4.13.3; do
  destination_file_name="$dest_dir/z3-$z3_ver"
  if [ "$kernel" = Windows ]; then destination_file_name="$destination_file_name.exe"; fi

  if [ -f "$destination_file_name" ]; then
    echo ">>> Z3 $z3_ver already downloaded to $destination_file_name"
  else
    key="$kernel-$arch-$z3_ver"

    case "$key" in
      Linux-aarch64-4.8.5)
        echo ">>> Z3 4.8.5 is not available for aarch64, downloading x86_64 version.  You need to install qemu-user (and shared libraries) to execute it."
        key="$kernel-x86_64-$z3_ver"
        ;;
      Darwin-aarch64-4.8.5)
        echo ">>> Z3 4.8.5 is not available for aarch64, downloading x86_64 version.  You need to install Rosetta 2 to execute it."
        key="$kernel-x86_64-$z3_ver"
        ;;
    esac

    url="$(get_url "$key")"

    if [ -z "$url" ]; then
      echo ">>> Z3 $z3_ver not available for this architecture, skipping..."
    elif $full_install; then
      full_install_z3 "$url" "$z3_ver" "$dest_dir"
    else
      download_z3 "$url" "$z3_ver" "$destination_file_name"
    fi
  fi
done
