module Ex9a
open FStar.String
open FStar.List

type canRead : string -> Type0 // read access permission
type canWrite : string -> Type0   // write access permission
type publicFile : string -> Type0 // some file attribute

(* sample policy: writable files are also readable *)

assume Policy: forall x. canWrite x ==> canRead x

(* two dangerous primitives *)

val read: file:string{canRead file} -> string
val delete: file:string{canWrite file} -> unit

let read file = assert(canRead file); "data"
let delete file = assert(canWrite file)

(* some sample files, one of them writable *)

let pwd = "C:/etc/password"
let readme = "C:/public/README"
let tmp = "C:/temp/tempfile"

assume WritableTmp: canWrite tmp

(* sample dynamic validation function *)
(* "all files in the public directory are readable" *)

val publicfile: f:string -> u:unit{ publicFile f } //CF can we omit u: ?

let publicfile f = 
  if f = "C:/public/README" then assume (publicFile f)
  else failwith "not a public file"

assume ReadablePublic: forall x. publicFile x ==> canRead x //NS: ==> is implication

let test() = 
  delete tmp; (* ok *)
//delete pwd; (* type error *)
  let v1 = read tmp in (* ok, using 1st logical rule *)
//let v2 = read readme in (* type error *)
  publicfile readme;
  let v3 = read readme in (* ok *)   //CF this should succeed
  () 

(* some higher-order code *)

val rc: file:string{canRead(file)} -> unit -> string  

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
  | Readable of x:string{canRead x}
  | Writable of x:string{canWrite x}
  | Nothing

type db = list (string * entry)
assume val acls: db
assume val insert: db -> string -> entry -> unit

val safe_read: string -> string
let safe_read file = 
  match List.Tot.assoc file acls with
  | Some(Readable file) -> read file 
  | Some(Writable file) -> read file 
  | _ -> failwith "unreadable"

val readable: file:string -> u:unit{ canRead(file) }

let readable file = 
  match List.Tot.assoc file acls with
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
