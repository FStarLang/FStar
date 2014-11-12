#! /bin/sh
if [ -n "$BASH" ]; then (set -o igncr) 2>/dev/null && set -o igncr; fi # REQUIRED

oasis setup -setup-update dynamic
