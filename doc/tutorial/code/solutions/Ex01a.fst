module Ex01a

open FStar.Exn
open FStar.All
//safe-read-write

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

val read  : f:filename{canRead f}  -> ML string
let read f  = FStar.IO.print_string ("Dummy read of file " ^ f ^ "\n"); f

val write : f:filename{canWrite f} -> string -> ML unit
let write f s = FStar.IO.print_string ("Dummy write of string " ^ s ^ " to file " ^ f ^ "\n")

let passwd  = "demo/password"
let readme  = "demo/README"
let tmp     = "demo/tempfile"

val staticChecking : unit -> ML unit
let staticChecking () =
  let v1 = read tmp in
  let v2 = read readme in
  (* let v3 = read passwd in -- invalid read, fails type-checking *)
  write tmp "hello!"
  (* ; write passwd "junk" -- invalid write , fails type-checking *)

exception InvalidRead
val checkedRead : filename -> ML string
let checkedRead f =
  if canRead f then read f else raise InvalidRead


val checkedWrite : filename -> string -> ML unit
// BEGIN: CheckedWrite

exception InvalidWrite
let checkedWrite f s =
  if canWrite f then write f s else raise InvalidWrite
// END: CheckedWrite


let dynamicChecking () =
  let v1 = checkedRead tmp in
  let v2 = checkedRead readme in
  let v3 = checkedRead passwd in (* this raises exception *)
  checkedWrite tmp "hello!";
  checkedWrite passwd "junk" (* this raises exception *)

let main = staticChecking (); dynamicChecking ()
