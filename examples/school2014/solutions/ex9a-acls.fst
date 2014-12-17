module ACLs
open String
open List

logic type CanRead : string -> Type   // read access permission
logic type CanWrite: string -> Type   // write access permission
logic type PublicFile: string -> Type // some file attribute

(* sample policy: writable files are also readable *)

assume Policy: forall x. CanWrite x ==> CanRead x

(* two dangerous primitives *)

val read: file:string{CanRead file} -> string
val delete: file:string{CanWrite file} -> unit

let read file = assert(CanRead file); "data"
let delete file = assert(CanWrite file)

(* some sample files, one of them writable *)

let pwd = "C:/etc/password"
let readme = "C:/public/README"
let tmp = "C:/temp/tempfile"

assume WritableTmp: CanWrite tmp

(* sample dynamic validation function *)
(* "all files in the public directory are readable" *)

val publicfile: f:string -> u:unit{ PublicFile f } //CF can we omit u: ?

let publicfile f = 
  if f = "C:/public/README" then assume (PublicFile f)
  else failwith "not a public file"

assume ReadablePublic: forall x. PublicFile x ==> CanRead x //NS: ==> is implication

let test() = 
  delete tmp; (* ok *)
//delete pwd; (* type error *)
  let v1 = read tmp in (* ok, using 1st logical rule *)
//let v2 = read readme in (* type error *)
  publicfile readme;
  let v3 = read readme in (* ok *)   //CF this should succeed
  () 

(* some higher-order code *)

val rc: file:string{CanRead(file)} -> unit -> string  

let rc file : unit -> string = fun () -> read file

val test_higher_order: unit -> unit
let test_higher_order() =
  let reader = 
    (publicfile readme; (fun () -> read readme)) in
//let v4 = read readme in (* type error *)
  let v5 = reader () in   (* ok *)
  ()

(* using dynamic ACLs in some database *)

type entry = 
  | Readable of x:string{CanRead x}
  | Writable of x:string{CanWrite x}
  | Nothing

type db = list (string * entry)
assume val acls: db
assume val insert: db -> string -> entry -> unit

val safe_read: string -> string
let safe_read file = 
  match List.assoc file acls with
  | Some(Readable file) -> read file 
  | Some(Writable file) -> read file 
  | _ -> failwith "unreadable"

val readable: file:string -> u:unit{ CanRead(file) }

let readable file = 
  match List.assoc file acls with
  | Some(Readable f) -> if file = f then () else failwith "unreadable"
  | Some(Writable f) -> if file = f then () else failwith "unreasable"
  | _ -> failwith "unreadable"


let test_acls() = 
  insert acls tmp (Writable(tmp)); (* ok *)
//insert acls tmp (Readable(pwd)); (* type error *)
  insert acls pwd (Nothing);       (* ok *)
  let v6 = safe_read pwd in           (* fails dynamically *)
  let v7 = readable tmp; read tmp in  (* ok *)
  ()
