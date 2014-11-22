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

(*
let read file = 
  expect(CanRead(file));
  printf "Reading file %s...\n" file; "data"
let delete file = 
  expect(CanWrite(file));
  printf "Deleting file %s...\n" file
 *)

//CF what kind of printing do we have? 

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

assume ReadablePublic: forall x. PublicFile x -> CanRead x

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

let test_higher_order() =
  let reader: unit -> string = 
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

// let acls: (string,entry) Db.t = Db.create()

val safe_read: string -> string
let safe_read file = 
  match List.assoc file acls with
  | Some(Readable file) -> read file 
  | Some(Writable file) -> read file 
  | _ -> failwith "unreadable"

val readable: file:string -> u:unit{ CanRead(file) }

let readable file = 
  match List.assoc file acls with
  | Some(Readable f) when (f = file) -> ()
  | Some(Writable f) when (f = file) -> () 
  | _ -> failwith "unreadable"


let test_acls() = 
  insert acls tmp (Writable(tmp)); (* ok *)
//insert acls tmp (Readable(pwd)); (* type error *)
  insert acls pwd (Nothing);       (* ok *)
  let v6 = safe_read pwd in           (* fails dynamically *)
  let v7 = readable tmp; read tmp in  (* ok *)
  ()

(*

(* concat *)

type t = file:string{ CanRead(file) }
val fold_left: ('a -> 'b -> 'a) -> 'a -> 'b list -> 'a 
val append: string -> t -> string

val merge: (file:string{ CanRead(file) }) list -> string

(* merge *)

type t = string

let rec fold_left f (a:t) xs = match xs with
  | x::xs -> fold_left f (f a x) xs
  | [] -> a
let append (a:string) (file:t) = (* a^ *) read file 
let merge sources = 
  let f: (string -> t -> string) -> string -> t list -> string = fold_left in
    f append "" sources
 *)
