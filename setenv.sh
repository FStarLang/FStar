#! /bin/bash

mydir=$(pwd)
mydir=$(realpath "${mydir}")

case "$(uname)" in
    *CYGWIN*)
        mydir=$(cygpath -d "${mydir}")
        ;;

    *)
        ;;
esac

export FSTAR_HOME="${mydir}"
export PATH="${mydir}/bin:${PATH}"
