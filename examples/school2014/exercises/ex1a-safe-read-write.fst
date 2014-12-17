module ACLs
  type filename = string

  (* canWrite is a function specifying whether or not a file f can be written *)
  let canWrite f = 
    match f with 
      | "C:/temp/tempfile" -> true
      | _ -> false

  (* canRead is also a function ... *)
  let canRead f = 
    canWrite f               (* writeable files are also readable *)
    || f="C:/public/README"  (* and so is this file *)

module System.IO
  open ACLs
  assume val read:   f:filename{canRead f}  -> string
  assume val write:  f:filename{canWrite f} -> string -> unit

module UntrustedClientCode
  open System.IO
  let passwd  = "C:/etc/password"
  let readme  = "C:/public/README"
  let tmp     = "C:/temp/tempfile"

  let safeRead f = read f       (* Exercise: make safeRead safe! *)
  let safeWrite f s = write f s (* Exercise: make safeWrite safe! *)

  let doitSafe () =
    let v1 = safeRead tmp in
    let v2 = safeRead readme in
    let v3 = safeRead passwd in (* your safeRead should do something safe here *)
    safeWrite tmp "hello!";
    safeWrite passwd "junk"; (* your safeWrite should do something safe here *)
    ()
