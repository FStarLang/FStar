#! /bin/bash
                                               # this comment is required
if [ -n "$BASH" ]; then                        # ------------------------
  (set -o igncr) 2>/dev/null && set -o igncr;  # ------------------------
fi                                             # ------------------------

mydir=$(pwd)

case "$(uname)" in
    *CYGWIN*)
        mydir=$(cygpath -d "${mydir}")
        ;;

    *)
        ;;
esac

export FSTAR_HOME="${mydir}"
export PATH="${mydir}/bin:${PATH}"
