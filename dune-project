(lang dune 3.15)
(name fstar)
(using menhir 2.1)
(package
 (name fstar)
 (synopsis "F* Compiler")
 (depends
  (ocaml (>= 4.14.0))
  dune
  batteries
  zarith
  stdint
  yojson
  memtrace
  menhirLib
  menhir
  mtime
  pprint
  sedlex
  ppxlib
  process
  ppx_deriving
  ppx_deriving_yojson))
