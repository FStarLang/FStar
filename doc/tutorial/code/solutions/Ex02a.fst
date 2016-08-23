module Ex02a
//can-read-write-types

type filename = string

val canWrite : filename -> Tot bool
let canWrite (f:filename) =
  match f with 
    | "demo/tempfile" -> true
    | _ -> false

val canRead : filename -> Tot bool
let canRead (f:filename) =
  canWrite f               (* writeable files are also readable *)
  || f="demo/README"       (* and so is this file *)
