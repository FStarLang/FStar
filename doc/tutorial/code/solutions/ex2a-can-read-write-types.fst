module FileName
  type filename = string

module ACLs
  open FileName

  val canWrite : filename -> Tot bool
  let canWrite (f:filename) = 
    match f with 
      | "C:/temp/tempfile" -> true
      | _ -> false

  val canRead : filename -> Tot bool
  let canRead (f:filename) = 
    canWrite f               (* writeable files are also readable *)
    || f="C:/public/README"  (* and so is this file *)
