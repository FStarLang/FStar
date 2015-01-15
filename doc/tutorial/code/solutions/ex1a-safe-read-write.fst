module FileName
  type filename = string

module ACLs
  open FileName

  (* canWrite is a function specifying whether or not a file f can be written *)
  let canWrite (f:filename) = 
    match f with 
      | "C:/temp/tempfile" -> true
      | _ -> false

  (* canRead is also a function ... *)
  let canRead (f:filename) = 
    canWrite f               (* writeable files are also readable *)
    || f="C:/public/README"  (* and so is this file *)

module System.IO
  open ACLs
  open FileName
  assume val read  : f:filename{canRead f}  -> string
  assume val write : f:filename{canWrite f} -> string -> unit
// END: SystemIO

module UntrustedClientCode
  open System.IO
  open FileName
  let passwd  = "C:/etc/password"
  let readme  = "C:/public/README"
  let tmp     = "C:/temp/tempfile"

  let staticChecking () =
    let v1 = read tmp in
    let v2 = read readme in
    (* let v3 = read passwd in -- invalid read, fails type-checking *)
    write tmp "hello!"
    (* ; write passwd "junk" -- invalid write , fails type-checking *)

  exception InvalidRead
  val checkedRead : filename -> string
  let checkedRead f =
    if ACLs.canRead f then System.IO.read f else raise InvalidRead

  val checkedWrite : filename -> string -> unit
// BEGIN: CheckedWrite
  exception InvalidWrite
  let checkedWrite f s =
    if ACLs.canWrite f then System.IO.write f s else raise InvalidWrite
// END: CheckedWrite

  let dynamicChecking () =
    let v1 = checkedRead tmp in
    let v2 = checkedRead readme in
    let v3 = checkedRead passwd in (* this raises exception *)
    checkedWrite tmp "hello!";
    checkedWrite passwd "junk" (* this raises exception *)
