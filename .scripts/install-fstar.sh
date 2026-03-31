#!/usr/bin/env bash

# Install F* locally from GitHub releases.
#
# Supports three sources:
#   - Official releases from FStarLang/FStar
#   - Nightly builds (master branch) from FStarLang/FStar-nightly
#   - Nightly builds (fstar2 branch) from FStarLang/FStar-nightly
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
  --nightly-fstar2     Install a nightly build (fstar2 branch)

Version:
  --version VER        Install a specific version instead of the latest.
                         For releases: a tag, e.g. v2026.03.24
                         For nightlies: a date, e.g. 2026-03-31

Destination:
  --dest DIR           Install F* into DIR (default: ~/.local/fstar)
  --link-dir DIR       Create symlinks to F* binaries in DIR (default: ~/bin)
  --no-link            Don't create symlinks

Other:
  --list               List available versions and exit
  -v, --verbose        Show detailed output
  -h, --help           Show this help

Examples:
  install-fstar.sh                                    # latest release
  install-fstar.sh --nightly                          # latest nightly (master)
  install-fstar.sh --nightly-fstar2                   # latest nightly (fstar2)
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
LINK_DIR="$HOME/bin"
DO_LINK=true
VERBOSE=false
LIST=false

# Parse arguments
while [[ $# -gt 0 ]]; do
  case "$1" in
    --release)        SOURCE=release; shift ;;
    --nightly)        SOURCE=nightly; shift ;;
    --nightly-fstar2) SOURCE=nightly-fstar2; shift ;;
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

# --- Helper: authenticated curl for GitHub API ---

gh_curl() {
  local -a headers=(
    -H "Accept: application/vnd.github+json"
    -H "X-GitHub-Api-Version: 2022-11-28"
  )
  local token=""
  if [[ -n "${GITHUB_TOKEN:-}" ]]; then
    token="$GITHUB_TOKEN"
  elif command -v gh &>/dev/null; then
    token=$(gh auth token 2>/dev/null || true)
  fi
  if [[ -n "$token" ]]; then
    headers+=(-H "Authorization: Bearer $token")
  fi
  curl -sL "${headers[@]}" "$@"
}

# --- List mode ---

list_versions() {
  local repo jq_filter
  case "$SOURCE" in
    release)
      repo="$RELEASE_REPO"
      jq_filter='.[] | .tag_name'
      ;;
    nightly)
      repo="$NIGHTLY_REPO"
      jq_filter='.[] | select(.tag_name | startswith("nightly-") and (startswith("nightly-fstar2") | not)) | .tag_name'
      ;;
    nightly-fstar2)
      repo="$NIGHTLY_REPO"
      jq_filter='.[] | select(.tag_name | startswith("nightly-fstar2-")) | .tag_name'
      ;;
  esac

  echo "Available versions ($SOURCE):"
  echo ""
  # Fetch up to 3 pages of releases
  for page in 1 2 3; do
    local json tags count
    json=$(gh_curl "https://api.github.com/repos/$repo/releases?per_page=30&page=$page")
    tags=$(echo "$json" | jq -r "$jq_filter")
    if [[ -z "$tags" ]]; then
      break
    fi
    echo "$tags"
    count=$(echo "$json" | jq 'length')
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

for tool in curl jq tar; do
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

# --- Resolve the release ---

resolve_release() {
  local release_json=""

  case "$SOURCE" in
    release)
      if [[ "$VERSION" == "latest" ]]; then
        release_json=$(gh_curl "https://api.github.com/repos/$RELEASE_REPO/releases/latest")
      else
        release_json=$(gh_curl "https://api.github.com/repos/$RELEASE_REPO/releases/tags/$VERSION")
      fi
      ;;
    nightly)
      if [[ "$VERSION" == "latest" ]]; then
        release_json=$(gh_curl "https://api.github.com/repos/$NIGHTLY_REPO/releases/latest")
        # The "latest" release on the nightly repo could be a fstar2 release.
        # Verify it's actually a master nightly, otherwise search.
        local tag
        tag=$(echo "$release_json" | jq -r '.tag_name // empty')
        if [[ "$tag" == nightly-fstar2-* ]]; then
          echo "Latest release is fstar2; searching for latest master nightly..." >&2
          release_json=""
        fi
      fi
      if [[ -z "$release_json" ]] || [[ "$VERSION" != "latest" ]]; then
        if [[ "$VERSION" == "latest" ]]; then
          # Search through releases for the latest master nightly
          local releases_json
          releases_json=$(gh_curl "https://api.github.com/repos/$NIGHTLY_REPO/releases?per_page=30")
          release_json=$(echo "$releases_json" | jq '
            [.[] | select(.tag_name | startswith("nightly-") and (startswith("nightly-fstar2") | not))]
            | first')
        else
          local tag="nightly-$VERSION"
          release_json=$(gh_curl "https://api.github.com/repos/$NIGHTLY_REPO/releases/tags/$tag")
        fi
      fi
      ;;
    nightly-fstar2)
      if [[ "$VERSION" == "latest" ]]; then
        # Search through releases for the latest fstar2 nightly
        local releases_json
        releases_json=$(gh_curl "https://api.github.com/repos/$NIGHTLY_REPO/releases?per_page=30")
        release_json=$(echo "$releases_json" | jq '
          [.[] | select(.tag_name | startswith("nightly-fstar2-"))]
          | first')
      else
        local tag="nightly-fstar2-$VERSION"
        release_json=$(gh_curl "https://api.github.com/repos/$NIGHTLY_REPO/releases/tags/$tag")
      fi
      ;;
  esac

  echo "$release_json"
}

echo "Looking for F* $SOURCE${VERSION:+ ($VERSION)}..."

RELEASE_JSON=$(resolve_release)

TAG=$(echo "$RELEASE_JSON" | jq -r '.tag_name // empty')
if [[ -z "$TAG" ]]; then
  echo "Error: could not find a matching release." >&2
  msg=$(echo "$RELEASE_JSON" | jq -r '.message // empty')
  if [[ -n "$msg" ]]; then
    echo "GitHub API: $msg" >&2
  fi
  exit 1
fi

echo "Found: $TAG"

# --- Find the matching asset ---

ASSET_URL=$(echo "$RELEASE_JSON" | jq -r \
  --arg kernel "$kernel" --arg arch "$arch" \
  '.assets[]
   | select(.name | (contains($kernel) and contains($arch)) )
   | .browser_download_url')

if [[ -z "$ASSET_URL" ]]; then
  echo "Error: no matching binary asset for $kernel/$arch." >&2
  echo "Available assets:" >&2
  echo "$RELEASE_JSON" | jq -r '.assets[].name' >&2
  exit 1
fi

ASSET_NAME=$(basename "$ASSET_URL")
echo "Downloading $ASSET_NAME..."

# --- Download ---

TMPDIR=$(mktemp -d)
trap 'rm -rf "$TMPDIR"' EXIT

curl -#L "$ASSET_URL" -o "$TMPDIR/$ASSET_NAME"

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
    tar xzf "$TMPDIR/$ASSET_NAME" --strip-components=2 -C "$DEST"
    ;;
  *.zip)
    unzip -qo "$TMPDIR/$ASSET_NAME" -d "$TMPDIR/extract"
    if [[ -d "$TMPDIR/extract/fstar" ]]; then
      mv "$TMPDIR/extract/fstar"/* "$DEST/"
    else
      mv "$TMPDIR/extract"/* "$DEST/"
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
  if ! echo "$PATH" | tr ':' '\n' | grep -qx "$LINK_DIR"; then
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
