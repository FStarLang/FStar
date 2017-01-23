#!/usr/bin/env bash

rm -rf *tar
rm -rf dlls-*
rm -rf out/ queries/
rm -rf *~
rm -rf pfdlls-*
(cd health-web; make clean)
(cd lookout; make clean)
(cd fine-continue; make clean)
