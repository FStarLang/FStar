type sys =
| Windows
| Posix

let system =
 if Sys.win32 || Sys.cygwin then
     Windows
 else
     Posix

let exe name =
  if Sys.unix then
    name
  else
    name^".exe"

let is_fstar_compiler_using_ocaml = true
