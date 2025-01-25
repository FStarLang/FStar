#!/bin/bash

# Running ./winwrap.sh cmd args will make replace any cygwin paths in
# the args before calling cmd. E.g. /cygdrive/c/foo/bar -> c:/foo/bar
#
# If none of the arguments are of that shape, this script should be
# fully transparent, passing arguments to $cmd in exactly the same shape
# even if they contain spaces, etc.

cmd=$1
shift

args=()

for arg; do
	arg=$(echo "$arg" | sed 's,^/cygdrive/\(.\)/,\1:/,')
	args+=("$arg")
done

exec $cmd "${args[@]}"
