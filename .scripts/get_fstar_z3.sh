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
  # ^ normalize macOS arm64 to Linux's aarch64
esac

get_url() {
  local version="$1" z3_arch os_pattern

  case "$arch" in
    x86_64)  z3_arch="x64" ;;
    aarch64) z3_arch="arm64" ;;
    *)       z3_arch="$arch" ;;
  esac

  case "$kernel" in
    Linux)   os_pattern="(glibc|ubuntu)" ;;
    Darwin)  os_pattern="osx" ;;
    Windows) os_pattern="win" ;;
    *)       return ;;
  esac

  local tag url
  for tag in "z3-$version" "Z3-$version"; do
    url=$(curl -s "https://api.github.com/repos/Z3Prover/z3/releases/tags/$tag" \
      | grep -oP '"browser_download_url":\s*"\K[^"]+' \
      | grep -E "z3-${version}-${z3_arch}-${os_pattern}[^/]*\.zip$" \
      | tail -1)
    if [ -n "$url" ]; then
      echo -n "$url"
      return
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

  pushd "$tmp_dir" > /dev/null
  curl -s -L "$url" -o "$base_name"

  unzip -q "$base_name" "$z3_path"
  popd > /dev/null
  install -m0755 "$tmp_dir/$z3_path" "$destination_file_name"
  echo ">>> Installed Z3 $version to $destination_file_name"
}

full_install_z3() {
  local url version dest_dir base_name

  url="$1"
  version="$2"
  dest_dir="$3"

  mkdir -p "$dest_dir/z3-$version"
  pushd "$dest_dir/z3-$version" > /dev/null

  echo ">>> Downloading Z3 $version from $url ..."
  base_name="$(basename "$url")"
  curl -s -L "$url" -o "$base_name"

  unzip -q "$base_name"
  mv "${base_name%.zip}"/* .
  rmdir "${base_name%.zip}"
  rm "$base_name"
  popd > /dev/null
}

usage() {
  echo "Usage: get_fstar_z3.sh destination/directory/bin [--full] [--arch <x86_64|aarch64>] [--kernel <Linux|Darwin|Windows>]"
  exit 1
}

dest_dir_set=false
while [ $# -ge 1 ]; do
  case "$1" in
    --arch)
      shift
      if [ $# -lt 1 ]; then usage; fi
      arch="$1"
      ;;
    --kernel)
      shift
      if [ $# -lt 1 ]; then usage; fi
      kernel="$1"
      ;;
    --full)
      # Passing --full xyz/ will create a tree like
      #  xyz/z3-4.8.5/bin/z3
      #  xyz/z3-4.13.3/bin/z3
      # (plus all other files in each package). This is used
      # for our binary packages which include Z3.
      full_install=true;
      ;;
    --*)
      usage
      ;;
    --)
      if $dest_dir_set; then usage; fi
      shift
      if [ $# -lt 1 ]; then usage; fi
      dest_dir="$1"
      dest_dir_set=true
      ;;
    *)
      if $dest_dir_set; then usage; fi
      dest_dir="$1"
      dest_dir_set=true
      ;;
  esac
  shift
done

if [ "$dest_dir_set" == "false" ]; then
  usage
fi

mkdir -p "$dest_dir"

for z3_ver in 4.13.3 4.15.3 4.16.0; do
  destination_file_name="$dest_dir/z3-$z3_ver"
  if [ "$kernel" = Windows ]; then destination_file_name="$destination_file_name.exe"; fi

  if [ -f "$destination_file_name" ]; then
    echo ">>> Z3 $z3_ver already downloaded to $destination_file_name"
  else
    url="$(get_url "$z3_ver")"

    if [ -z "$url" ]; then
      echo ">>> Z3 $z3_ver not available for this architecture, skipping..."
    elif $full_install; then
      full_install_z3 "$url" "$z3_ver" "$dest_dir"
    else
      download_z3 "$url" "$z3_ver" "$destination_file_name"
    fi
  fi
done
