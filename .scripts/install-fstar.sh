#!/usr/bin/env bash

# Install F* locally from GitHub releases.
#
# Supports two sources:
#   - Official releases from FStarLang/FStar
#   - Nightly builds (master branch) from FStarLang/FStar-nightly
#
# Can be run directly or via curl:
#   curl -fsSL https://raw.githubusercontent.com/FStarLang/FStar/master/.scripts/install-fstar.sh | bash -s -- --nightly

main() {

set -euo pipefail

RELEASE_REPO=FStarLang/FStar
NIGHTLY_REPO=FStarLang/FStar-nightly

usage() {
  cat <<'EOF'
Usage: install-fstar.sh [OPTIONS]

Install F* locally from GitHub releases.

Source (pick one):
  --release            Install from official releases (default)
  --nightly            Install a nightly build (master branch)

Version:
  --version VER        Install a specific version instead of the latest.
                         For releases: a tag, e.g. v2026.03.24
                         For nightlies: a date, e.g. 2026-03-31

Destination:
  --dest DIR           Install F* into DIR (default: ~/.local/fstar)
  --link-dir DIR       Create symlinks to F* binaries in DIR (default: ~/.local/bin)
  --no-link            Don't create symlinks

Other:
  --list               List available versions and exit
  -v, --verbose        Show detailed output
  -h, --help           Show this help

Examples:
  install-fstar.sh                                    # latest release
  install-fstar.sh --nightly                          # latest nightly (master)
  install-fstar.sh --release --version v2025.12.15    # specific release
  install-fstar.sh --nightly --version 2026-03-30     # specific nightly date
  install-fstar.sh --dest ~/my-fstar --no-link        # custom location
  install-fstar.sh --list                             # list available versions
  install-fstar.sh --nightly --list                   # list nightly versions

Via curl:
  curl -fsSL <url>/install-fstar.sh | bash -s -- --nightly
EOF
}

# Defaults
SOURCE=release
VERSION=latest
DEST="$HOME/.local/fstar"
LINK_DIR="$HOME/.local/bin"
DO_LINK=true
VERBOSE=false
LIST=false

# Parse arguments
while [[ $# -gt 0 ]]; do
  case "$1" in
    --release)        SOURCE=release; shift ;;
    --nightly)        SOURCE=nightly; shift ;;
    --version)
      if [[ $# -lt 2 ]]; then echo "Error: --version requires an argument" >&2; exit 1; fi
      VERSION="$2"; shift 2 ;;
    --dest)
      if [[ $# -lt 2 ]]; then echo "Error: --dest requires an argument" >&2; exit 1; fi
      DEST="$2"; shift 2 ;;
    --link-dir)
      if [[ $# -lt 2 ]]; then echo "Error: --link-dir requires an argument" >&2; exit 1; fi
      LINK_DIR="$2"; shift 2 ;;
    --no-link)        DO_LINK=false; shift ;;
    --list)           LIST=true; shift ;;
    -v|--verbose)     VERBOSE=true; shift ;;
    -h|--help)        usage; exit 0 ;;
    *)                echo "Error: unknown option: $1" >&2; usage >&2; exit 1 ;;
  esac
done

if $VERBOSE; then
  set -x
fi

# --- Helper: curl for GitHub API ---

gh_curl() {
  local -a headers=(
    -H "Accept: application/vnd.github+json"
    -H "X-GitHub-Api-Version: 2022-11-28"
  )
  curl -sL "${headers[@]}" "$@"
}

# --- Lightweight JSON helpers (no jq dependency) ---
# These work for GitHub API responses where field values are simple strings.

# Extract the first value of a JSON string field from stdin.
json_field() {
  grep -o "\"$1\"[[:space:]]*:[[:space:]]*\"[^\"]*\"" | head -1 | sed 's/.*:[[:space:]]*"//;s/"$//' || true
}

# Extract all values of a JSON string field from stdin.
json_fields() {
  grep -o "\"$1\"[[:space:]]*:[[:space:]]*\"[^\"]*\"" | sed 's/.*:[[:space:]]*"//;s/"$//' || true
}

# --- List mode ---

list_versions() {
  local repo
  case "$SOURCE" in
    release)        repo="$RELEASE_REPO" ;;
    nightly)        repo="$NIGHTLY_REPO" ;;
  esac

  echo "Available versions ($SOURCE):"
  echo ""
  # Fetch up to 3 pages of releases
  for page in 1 2 3; do
    local json tags count
    json=$(gh_curl "https://api.github.com/repos/$repo/releases?per_page=30&page=$page")
    tags=$(echo "$json" | json_fields "tag_name")
    case "$SOURCE" in
      nightly)        tags=$(echo "$tags" | grep "^nightly-" || true) ;;
    esac
    if [[ -z "$tags" ]]; then
      break
    fi
    echo "$tags"
    count=$(echo "$json" | grep -c '"tag_name"' || true)
    if [[ "$count" -lt 30 ]]; then
      break
    fi
  done
}

if $LIST; then
  list_versions
  exit 0
fi

# --- Check required tools ---

for tool in curl tar; do
  if ! command -v "$tool" &>/dev/null; then
    echo "Error: '$tool' is required but not found." >&2
    exit 1
  fi
done

# --- Detect OS and architecture ---

kernel="$(uname -s)"
case "$kernel" in
  CYGWIN*|MINGW*|MSYS*) kernel=Windows_NT ;;
esac

arch="$(uname -m)"

# --- Construct download URL ---
#
# When a specific version is given, we construct the URL directly from the
# known naming scheme, avoiding GitHub API calls (which are rate-limited).
# The API is only needed for --version latest (to discover the latest tag)
# and for --list.

# Build the asset filename for a given tag.
asset_filename() {
  local tag="$1"
  local ext="tar.gz"
  [[ "$kernel" == "Windows_NT" ]] && ext="zip"

  case "$SOURCE" in
    release)
      # e.g. fstar-v2026.04.17-Linux-x86_64.tar.gz
      echo "fstar-${tag}-${kernel}-${arch}.${ext}"
      ;;
    nightly)
      # e.g. fstar-Linux-x86_64.tar.gz  (no version in filename)
      echo "fstar-${kernel}-${arch}.${ext}"
      ;;
  esac
}

# Build the full download URL for a given tag.
asset_url() {
  local tag="$1"
  local repo filename
  case "$SOURCE" in
    release)  repo="$RELEASE_REPO" ;;
    nightly)  repo="$NIGHTLY_REPO" ;;
  esac
  filename=$(asset_filename "$tag")
  echo "https://github.com/${repo}/releases/download/${tag}/${filename}"
}

resolve_tag_and_url() {
  if [[ "$VERSION" != "latest" ]]; then
    # Construct the tag and URL directly — no API call needed.
    case "$SOURCE" in
      release)  TAG="$VERSION" ;;
      nightly)  TAG="nightly-$VERSION" ;;
    esac
    ASSET_URL=$(asset_url "$TAG")
  else
    # We need the API only for "latest".
    local release_json repo
    case "$SOURCE" in
      release)  repo="$RELEASE_REPO" ;;
      nightly)  repo="$NIGHTLY_REPO" ;;
    esac
    release_json=$(gh_curl "https://api.github.com/repos/$repo/releases/latest")
    TAG=$(echo "$release_json" | json_field "tag_name")
    if [[ -z "$TAG" ]]; then
      echo "Error: could not find the latest release." >&2
      local msg
      msg=$(echo "$release_json" | json_field "message")
      if [[ -n "$msg" ]]; then
        echo "GitHub API: $msg" >&2
      fi
      exit 1
    fi
    ASSET_URL=$(asset_url "$TAG")
  fi
}

echo "Looking for F* $SOURCE${VERSION:+ ($VERSION)}..."

TAG=""
ASSET_URL=""
resolve_tag_and_url

echo "Found: $TAG"

ASSET_NAME=$(basename "$ASSET_URL")
echo "Downloading $ASSET_NAME..."

# --- Download ---

WORKDIR=$(mktemp -d)
trap 'rm -rf "$WORKDIR"' EXIT

curl -#L "$ASSET_URL" -o "$WORKDIR/$ASSET_NAME"

# --- Remove previous installation ---

if [[ -e "$DEST" ]]; then
  echo "Removing previous installation at $DEST..."
  rm -rf "$DEST"
fi
mkdir -p "$DEST"

# --- Extract ---

echo "Extracting to $DEST..."

case "$ASSET_NAME" in
  *.tar.gz|*.tgz)
    # Both release and nightly tarballs have ./fstar/{bin,lib,...} structure;
    # strip the leading ./ and fstar/ components.
    tar xzf "$WORKDIR/$ASSET_NAME" --strip-components=2 -C "$DEST"
    ;;
  *.zip)
    if ! command -v unzip &>/dev/null; then
      echo "Error: 'unzip' is required to extract $ASSET_NAME but not found." >&2
      exit 1
    fi
    unzip -qo "$WORKDIR/$ASSET_NAME" -d "$WORKDIR/extract"
    if [[ -d "$WORKDIR/extract/fstar" ]]; then
      mv "$WORKDIR/extract/fstar"/* "$DEST/"
    else
      mv "$WORKDIR/extract"/* "$DEST/"
    fi
    ;;
  *)
    echo "Error: unknown archive format: $ASSET_NAME" >&2
    exit 1
    ;;
esac

# Sanity check
if [[ ! -x "$DEST/bin/fstar.exe" ]]; then
  echo "Warning: $DEST/bin/fstar.exe not found or not executable." >&2
  echo "Contents of $DEST:" >&2
  ls -la "$DEST" >&2
fi

echo "Installed F* ($TAG) to $DEST"

# --- Create symlinks ---

if $DO_LINK; then
  mkdir -p "$LINK_DIR"
  for bin in "$DEST/bin/"*; do
    [[ -f "$bin" ]] || continue
    name=$(basename "$bin")
    ln -sf "$(realpath "$bin")" "$LINK_DIR/$name"
    echo "  Linked $LINK_DIR/$name -> $bin"
  done
  if ! echo "$PATH" | tr ':' '\n' | grep -qxF "$LINK_DIR"; then
    echo ""
    echo "Note: $LINK_DIR is not in your PATH."
    echo "Add it with: export PATH=\"$LINK_DIR:\$PATH\""
  fi
fi

echo ""
echo "Done! F* $TAG is ready."
if ! $DO_LINK; then
  echo "Add $DEST/bin to your PATH, or re-run without --no-link to create symlinks."
fi

} # end of main()

main "$@"
