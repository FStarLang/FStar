// BEGIN: ACLs
module ACLs
  type filename = string

  (* canWrite is a function specifying whether or not a file f can be written *)
  let canWrite (f:filename) = 
    match f with 
      | "C:/temp/tempfile" -> true
      | _ -> false

  (* canRead is also a function ... *)
  let canRead (f:filename) = 
    canWrite f               (* writeable files are also readable *)
    || f="C:/public/README"  (* and so is this file *)
// END: ACLs

// BEGIN: SystemIO
module System.IO
  open ACLs
  assume val read:   f:filename{canRead f}  -> string
  assume val write:  f:filename{canWrite f} -> string -> unit
// END: SystemIO

// BEGIN: UntrustedClientCode
module UntrustedClientCode
  open ACLs
  open System.IO
  let passwd  = "C:/etc/password"
  let readme  = "C:/public/README"
  let tmp     = "C:/temp/tempfile"
// END: UntrustedClientCode

// BEGIN: SafeReadWriteTypes
  val safeRead : filename -> string
  val safeWrite : filename -> string -> unit
// END: SafeReadWriteTypes
// BEGIN: SafeReadWrite
  let safeRead f = if ACLs.canRead f then System.IO.read f else "unreadable"
  let safeWrite f s = if ACLs.canWrite f then System.IO.write f s else ()
// END: SafeReadWrite

  let doitSafe () =
    let v1 = safeRead tmp in
    let v2 = safeRead readme in
    let v3 = safeRead passwd in (* v3 = unreadable *)
    safeWrite tmp "hello!";
    safeWrite passwd "junk"; (* contents of passwd are now unaffected *)
    ()
