# Parallel quicksort extracted to OCaml 5

This directory contains the build infrastructure to extract the Quicksort.Task file to OCaml, and build it with OCaml 5.1.1 and domainslib.

```shell
opam switch create 5.1.1
opam install --switch=5.1.1 domainslib
make
```

Note: the Makefile here will not do anything if a 5.1.1 switch
is not installed. Our CI does not test this directory.
