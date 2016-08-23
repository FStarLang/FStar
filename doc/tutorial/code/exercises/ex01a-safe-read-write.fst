module Ex01a






// BEGIN: ACLs
type filename = string

(* canWrite is a function specifying whether or not a file f can be written *)
let canWrite (f:filename) = 
  match f with 
    | "demo/tempfile" -> true
    | _ -> false

(* canRead is also a function ... *)
let canRead (f:filename) = 
  canWrite f               (* writeable files are also readable *)
  || f="demo/README"       (* and so is this file *)
// END: ACLs

// BEGIN: FileIO
assume val read  : f:filename{canRead f}  -> string
assume val write : f:filename{canWrite f} -> string -> unit
// END: FileIO


// BEGIN: UntrustedClientCode
let passwd  = "demo/password"
let readme  = "demo/README"
let tmp     = "demo/tempfile"
// END: UntrustedClientCode

// BEGIN: StaticChecking
val staticChecking : unit -> unit
let staticChecking () =
  let v1 = read tmp in
  let v2 = read readme in
  (* let v3 = read passwd in -- invalid read, fails type-checking *)
  write tmp "hello!"
  (* ; write passwd "junk" -- invalid write , fails type-checking *)
// END: StaticChecking

// BEGIN: CheckedRead
exception InvalidRead
val checkedRead : filename -> string
let checkedRead f =
  if canRead f then read f else raise InvalidRead
// END: CheckedRead

// BEGIN: CheckedWriteType
assume val checkedWrite : filename -> string -> unit
// END: CheckedWriteType

// BEGIN: DynamicChecking
let dynamicChecking () =
  let v1 = checkedRead tmp in
  let v2 = checkedRead readme in
  let v3 = checkedRead passwd in (* this raises exception *)
  checkedWrite tmp "hello!";
  checkedWrite passwd "junk" (* this raises exception *)
// END: DynamicChecking
