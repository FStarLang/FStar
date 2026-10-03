module FStarC.HashTable

(* Mutable hash tables over any key type with [deq] and [hashable] instances.

   Each key type gets its own instance of OCaml's [Hashtbl.Make], applied to
   the key's [(=?)] and [hash] (doc/ref/custard.md, section 133).  The table
   type is indexed by the two dictionaries, so the dictionaries the type
   checker resolves at a use decide which instance the table belongs to.

   Every operation spells out [hashtbl_make (hashed k)] rather than going
   through a helper, because Custard recognizes a functor instance only by an
   application of the functor itself or by an unapplied top-level name. *)

open FStarC.Effect
open FStarC.Class.Deq
open FStarC.Class.Hashable

[@@custard_extern "int"]
private assume new type ocaml_int : Type0

[@@custard_extern "Z.to_int"]
private assume val to_ocaml_int (x:int) : ocaml_int

[@@custard_extern "Z.of_int"]
private assume val of_ocaml_int (x:ocaml_int) : int

(* Hashtbl.HashedType *)
noeq type hashed_type = {
  t: Type0;
  equal: t -> t -> ML bool;
  hash: t -> ML hash_code;
}

(* Hashtbl.S with type key = k, restricted to what is used. *)
noeq type hashtbl_s (k:Type0) = {
  t: Type0 -> Type0;
  create: #a:Type0 -> ocaml_int -> ML (t a);
  clear: #a:Type0 -> t a -> ML unit;
  copy: #a:Type0 -> t a -> ML (t a);
  remove: #a:Type0 -> t a -> k -> ML unit;
  find_opt: #a:Type0 -> t a -> k -> ML (option a);
  replace: #a:Type0 -> t a -> k -> a -> ML unit;
  mem: #a:Type0 -> t a -> k -> ML bool;
  iter: #a:Type0 -> (k -> a -> ML unit) -> t a -> ML unit;
  fold: #a:Type0 -> #b:Type0 -> (k -> a -> b -> ML b) -> t a -> b -> ML b;
  length: #a:Type0 -> t a -> ML ocaml_int;
}

[@@custard_functor "Hashtbl.Make"]
assume val hashtbl_make (h:hashed_type) : hashtbl_s h.t

(* The methods are named rather than wrapped in lambdas, so that the
   functor's argument reduces to the same key whether a dictionary is still
   the instance's name or already the record it unfolds to (section 133.5).
   Not [inline_for_extraction], for the same reason: the argument has to stay
   the application [hashed k], in types and bodies alike. *)
let hashed (k:Type0) {| d: deq k |} {| h: hashable k |} : hashed_type =
  { t = k; equal = (=?) #k #d; hash = hash #k #h }

inline_for_extraction
let t (k:Type0) {| deq k |} {| hashable k |} (v:Type0) : Type0 =
  (hashtbl_make (hashed k)).t v

(* The operations are [inline_for_extraction] so that each use names the
   dictionaries exactly as the use's types do. *)

inline_for_extraction
let create (#k:Type0) {| deq k |} {| hashable k |} (#v:Type0) (n:int) : ML (t k v) =
  (hashtbl_make (hashed k)).create (to_ocaml_int n)

inline_for_extraction
let clear (#k:Type0) {| deq k |} {| hashable k |} (#v:Type0) (m:t k v) : ML unit =
  (hashtbl_make (hashed k)).clear m

inline_for_extraction
let copy (#k:Type0) {| deq k |} {| hashable k |} (#v:Type0) (m:t k v) : ML (t k v) =
  (hashtbl_make (hashed k)).copy m

(* Replaces the current binding of the key, if any. *)
inline_for_extraction
let add (#k:Type0) {| deq k |} {| hashable k |} (#v:Type0) (m:t k v) (key:k) (value:v) : ML unit =
  (hashtbl_make (hashed k)).replace m key value

inline_for_extraction
let remove (#k:Type0) {| deq k |} {| hashable k |} (#v:Type0) (m:t k v) (key:k) : ML unit =
  (hashtbl_make (hashed k)).remove m key

inline_for_extraction
let try_find (#k:Type0) {| deq k |} {| hashable k |} (#v:Type0) (m:t k v) (key:k) : ML (option v) =
  (hashtbl_make (hashed k)).find_opt m key

inline_for_extraction
let mem (#k:Type0) {| deq k |} {| hashable k |} (#v:Type0) (m:t k v) (key:k) : ML bool =
  (hashtbl_make (hashed k)).mem m key

inline_for_extraction
let iter (#k:Type0) {| deq k |} {| hashable k |} (#v:Type0)
  (m:t k v) (f:k -> v -> ML unit) : ML unit =
  (hashtbl_make (hashed k)).iter f m

inline_for_extraction
let fold (#k:Type0) {| deq k |} {| hashable k |} (#v #a:Type0)
  (m:t k v) (f:k -> v -> a -> ML a) (init:a) : ML a =
  (hashtbl_make (hashed k)).fold f m init

inline_for_extraction
let size (#k:Type0) {| deq k |} {| hashable k |} (#v:Type0) (m:t k v) : ML int =
  of_ocaml_int ((hashtbl_make (hashed k)).length m)

inline_for_extraction
let of_list (#k:Type0) {| deq k |} {| hashable k |} (#v:Type0) (l:list (k & v)) : ML (t k v) =
  let m = create (FStarC.List.length l) in
  FStarC.List.iter (fun (key, value) -> add m key value) l;
  m

inline_for_extraction
let keys (#k:Type0) {| deq k |} {| hashable k |} (#v:Type0) (m:t k v) : ML (list k) =
  fold m (fun key _ acc -> key :: acc) []
