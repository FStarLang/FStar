#!/bin/bash

set -ue

extract_mod () {
  local mod="$1"
  local file="$2"
  sed -n "s/^module *$mod *= \([A-Z].*\) *$/&/p" "$file"
}

list_mods () {
  local file="$1"
  # add a KEEP comment to prevent this script from removing the line
  grep -v KEEP "$file" | sed -n 's/^module *\([^ ]*\) *= *[A-Z].*/\1/p' | sort | uniq
}

count () {
  local mod="$1"
  local file="$2"
  # Note: captures uses of `M.xxx`, or `let open M ` or `open M `
  grep "\<$mod\.\|open $mod\>" "$file" | wc -l
}

used1 () {
  local mod="$1"
  local file="$2"
  # echo "Checking for 'module $mod' in $file";
  N=$(count "$mod" "$file");
  [ "$N" -ne 0 ]
}

used () {
  local mod="$1"
  local file="$2"

  if used1 "$mod" "$file"; then
    return 0;
  fi

  # If we were NOT looking at an interface, we're done and the module
  # was indeed not used.
  if ! [[ "$file" =~ .fsti ]]; then
    # echo not fsti
    return 1;
  fi
  # echo is fsti

  # We have an interface where the module was not used, try to see if
  # it it's used in the implementation.
  fst=${file%i}

  if ! [ -e "$fst" ]; then
    # echo fst not next to fsti, finding
    # If the fst was not next to the fsti, try to find it.
    # Try to find the fst, it may not be next to the fsti. The ideal thing
    # would be asking F* to find it in the include path, of course.
    fst=$(find . -type f -name "$(basename "$fst")")
    # echo fst=$fst
  fi

  if ! [ -e "$fst" ]; then
    # echo "did not find an implementation for $file" >&2;
    return 1 # not used
  fi

  if used1 "$mod" "$fst"; then
    # whoops, used in fst, warn!
    if false; then
      echo "WARNING: module $mod defined in $file and not used there, but used in $fst. Please move the alias to the fst." >&2
    else
      # Automatically move this line
      line=$(extract_mod "$mod" "$file")
      if [ -z "$line" ]; then
        echo "error: couldn't extract module line?"
        echo "line=$line"
        return 0 # claim used, be safe
      fi
      if grep -q "^$line$" "$fst"; then
        # Same line already in the fst, skip adding and say OK to remove
        return 1
      fi
      # Find the first module definition or open and inject the line
      # before it. If none are there, put it after the `module` header.
      # fun fact: LINENO is bash variable
      LINE=$(sed -n '/^module *[A-Z].*=\|^open/{=;q}' "$fst")
      if [ -z "$LINE" ]; then
        LINE=$(sed -n '/^module /{=;q}' "$fst")
        LINE=$((LINE+1))
      fi
      sed -i "$LINE i $line" "$fst"
    fi
    return 1
  fi

  # echo seems unused in $fst
  return 1
}

remove () {
  local mod="$1"
  local file="$2"
  # echo "Removing 'module $mod' from $file"
  sed -i "/^module $mod\>/d" $file
}

for file; do
  for mod in $(list_mods "$file"); do
    if ! used "$mod" "$file"; then
      remove "$mod" "$file"
    fi
  done
done
