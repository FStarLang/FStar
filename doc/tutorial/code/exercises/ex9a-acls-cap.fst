module ACLs
open String
open List
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


module SHA1 
open Array

type bytes = seq byte (* concrete byte arrays *) 
type text  = bytes    (* a type abbreviation, for clarity *)

type nbytes (n:nat) = 
  b:bytes{length b == n} (* fixed-length bytes *)

(* we rely on some external crypto library implementing HMAC-SHA1 *)

let keysize = 16 
let macsize = 20  

type key = nbytes keysize
type tag = nbytes macsize

assume val sample: n:nat -> nbytes n
assume val sha1: key -> text -> Tot tag 


(* to verify, we simply recompute & compare *) 

val sha1verify: key -> text -> tag -> Tot bool
let sha1verify k txt tag = (sha1 k txt = tag)


module MAC 
open Array
open SHA1
open ST

(* ---- specification *)

(* we attach an authenticated properties to each key, 
   used as a pre-condition for MACing and 
   a postcondition of MAC verification *)

opaque type key_prop : key -> text -> Type
type pkey (p:(text -> Type)) = k:key{key_prop k == p}

val keygen: p:(text -> Type) -> pkey p
val mac:    k:key -> t:text{key_prop k t} -> tag
val verify: k:key -> t:text -> tag -> b:bool{b ==> key_prop k t}




(* ---- implementation *)

let keygen (p: (text -> Type)) = 
  let k = sample keysize in
  assume (key_prop k == p);
  k

(* to model authentication, we log all genuine calls 
   to MACs; the ideal implementation below uses the 
   log to correct errors. *)

type entry = 
  | Entry : k:key 
         -> t:text{key_prop k t}
         -> m:tag
         -> entry

let log = ST.alloc (list entry) [] 

let mac k t = 
  let m = sha1 k t in
  log := Entry k t m :: !log;
  m

let verify k text tag =
  let verified = sha1verify k text tag in 
  let found =
    is_Some 
      (List.find 
        (fun (Entry k' text' tag') -> k=k' && text=text')
        !log) in 

  (* plain, concrete implementation (ignoring the log) *) 
//verified           

  (* ideal, error-correcting implementation *) 
  verified && found  

  (* error-detecting implementation for the INT-CMA game *)
//(if verified && not found then win := Some(k,text,tag)); 
//verified


(* to be used with mac.fst and acls2.fst *)

module Cap (* capabilities *) 
open Array
open ACLs
open MAC 

assume val utf8: s:string  -> Tot (seq byte) 

assume UTF8_inj: 
  forall s0 s1.{:pattern (utf8 s0); (utf8 s1)}
    equal (utf8 s0) (utf8 s1) ==> s0==s1

opaque logic type CapRead (msg:seq byte) =
    (forall f. msg = utf8 f ==> ACLs.canRead f)

let k = keygen CapRead

val issue: f:file{ canRead f } -> SHA1.tag 
val redeem: f:file -> m:SHA1.tag -> u:unit{ canRead f }

let issue f = failwith "Implement this function"
let redeem f t = failwith "Implement this function"
