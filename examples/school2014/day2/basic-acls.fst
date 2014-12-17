module ACLs
open String
open List

logic type CanRead : string -> Type   // read access permission
logic type CanWrite: string -> Type   // write access permission

(* two dangerous primitives *)

val read:   file:string{CanRead file} -> string
val delete: file:string{CanWrite file} -> unit

let read file   = assert(CanRead file);  "data" 
let delete file = assert(CanWrite file)  (* ... *)

(* some sample files, one of them writable *)

let pwd    = "C:/etc/password"
let readme = "C:/public/README"
let tmp    = "C:/temp/tempfile"

assume WritableTmp: CanWrite tmp

(* sample policy: writable files are also readable *)

assume WritableReadable: forall x. CanWrite x ==> CanRead x

(* sample dynamic validation function *)
(* "all files in the public directory are readable" *)

assume val publicfile: f:string -> Tot bool
assume ReadablePublic: forall f. publicfile f ==> CanRead f 

let test() = 
  delete tmp;             (* ok *)
//delete pwd;             (* type error *)
  let v1 = read tmp in    (* ok, using Policu1st logical rule *)
//let v2 = read readme in (* type error *)
  let v3 =                (* ok, but may fail dynamically *) 
    if publicfile readme 
    then read readme 
    else failwith "access denied" in
  () 

(* can we use cryptographic evidence instead of local policies? *)
