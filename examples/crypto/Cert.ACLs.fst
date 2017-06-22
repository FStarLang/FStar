module Cert.ACLs
open FStar.All
open FStar.String
open FStar.List.Tot

type file = string

let canWrite = function
  | "C:/temp/tempfile" -> true
  | _ -> false

let publicFile = function 
  | "C:/public/README" -> true
  | _ -> false
  
let canRead (f:file) = 
  canWrite f           (* 1. writeable files are also readable *)
  || publicFile f      (* 2. public files are readable *)
  || f="C:/acls2.fst"  (* and so is this file *)

(* two dangerous primitives *)
assume val read:   file:string{canRead file} -> string
assume val delete: file:string{canWrite file} -> unit

(* some sample files, one of them writable *)
let pwd    = "C:/etc/password"
let readme = "C:/public/README"
let tmp    = "C:/temp/tempfile"

let test () = 
  delete tmp; (* ok *)
//delete pwd; (* type error *)
  let v1 = read tmp in    (* ok, rule 1. *)
  let v2 = read readme in (* ok, rule 2. *)
  () 

(* some higher-order code *)
val rc: file -> ML (unit -> string)
let rc file = 
  if canRead file 
  then (fun () -> read file)
  else failwith "Can't read"
