module FunctorClass
open FStar.All
open FStar.IO
open FStar.Attributes

(* A table type indexed by type-class dictionaries over an OCaml functor
   (section 133.5).  The generic operations are specialized on the
   dictionaries, so inside them a dictionary is the record it unfolds to,
   while the types their callers write name the instance.  Both must denote
   the same functor instance, or the OCaml does not typecheck. *)

[@@custard_extern "int"]
assume new type ocaml_int : Type0

[@@custard_extern "Z.to_int"]
assume val to_ocaml_int (x:int) : ocaml_int

[@@custard_extern "Z.of_int"]
assume val of_ocaml_int (x:ocaml_int) : int

[@@custard_extern "Hashtbl.hash"]
assume val poly_hash (#a:Type0) (x:a) : ocaml_int

class deq (a:Type) = { (=?) : a -> a -> ML bool }
class hashable (a:Type) = { hash : a -> ML ocaml_int }

instance deq_string : deq string = { (=?) = (fun x y -> x = y) }
instance hashable_string : hashable string = { hash = (fun x -> poly_hash x) }
instance deq_int : deq int = { (=?) = (fun x y -> x = y) }
instance hashable_int : hashable int = { hash = (fun x -> poly_hash (x % 7)) }

noeq type hashed_type = { t: Type0; equal: t -> t -> ML bool; hash: t -> ML ocaml_int }

noeq type hashtbl_s (k:Type0) = {
  t: Type0 -> Type0;
  create: #a:Type0 -> ocaml_int -> ML (t a);
  replace: #a:Type0 -> t a -> k -> a -> ML unit;
  find_opt: #a:Type0 -> t a -> k -> ML (option a);
  length: #a:Type0 -> t a -> ML ocaml_int;
}

[@@custard_functor "Hashtbl.Make"]
assume val hashtbl_make (h:hashed_type) : hashtbl_s h.t

(* The methods are named, not wrapped in lambdas: the key is reduced only
   weakly, so a dictionary inside a lambda would stay as it was written. *)
let hashed (k:Type0) {| d: deq k |} {| h: hashable k |} : hashed_type =
  { t = k; equal = (=?) #k #d; hash = hash #k #h }

inline_for_extraction
let t (k:Type0) {| deq k |} {| hashable k |} (v:Type0) : Type0 =
  (hashtbl_make (hashed k)).t v

let create (#k:Type0) {| deq k |} {| hashable k |} (#v:Type0) (n:int) : ML (t k v) =
  (hashtbl_make (hashed k)).create (to_ocaml_int n)

let add (#k:Type0) {| deq k |} {| hashable k |} (#v:Type0) (m:t k v) (x:k) (y:v) : ML unit =
  (hashtbl_make (hashed k)).replace m x y

let try_find (#k:Type0) {| deq k |} {| hashable k |} (#v:Type0) (m:t k v) (x:k) : ML (option v) =
  (hashtbl_make (hashed k)).find_opt m x

let size (#k:Type0) {| deq k |} {| hashable k |} (#v:Type0) (m:t k v) : ML int =
  of_ocaml_int ((hashtbl_make (hashed k)).length m)

(* A monomorphic wrapper over the generic table. *)
inline_for_extraction
let smap (v:Type0) : Type0 = t string v
let smap_create (#v:Type0) (n:int) : ML (smap v) = create n
let smap_add (#v:Type0) (m:smap v) (x:string) (y:v) : ML unit = add m x y
let smap_find (#v:Type0) (m:smap v) (x:string) : ML (option v) = try_find m x

(* A key type that is an abbreviation: the functor argument mentions [name],
   not [string], until it is normalized, and the table must still be the same
   OCaml module as [smap]'s. *)
let name = string
let name_create (#v:Type0) (n:int) : ML (t name v) = create n

let show_opt (o:option string) : string =
  match o with
  | None -> "none"
  | Some s -> s

let main () : ML unit =
  let m : smap int = smap_create 10 in
  smap_add m "a" 1; smap_add m "b" 2; smap_add m "a" 3;
  (match try_find m "a" with
   | Some n -> print_string (string_of_int n)
   | None -> print_string "none");
  print_string "\n";
  let im : t int string = create 10 in
  add im 5 "five"; add im 12 "twelve";
  print_string (show_opt (try_find im 5)); print_string "\n";
  print_string (show_opt (try_find im 12)); print_string "\n";
  print_string (show_opt (try_find im 19)); print_string "\n";
  print_string (string_of_int (size im + size m)); print_string "\n";
  let nm = name_create 10 in
  add nm "x" 7;
  (match smap_find nm "x" with
   | Some n -> print_string (string_of_int n)
   | None -> print_string "none");
  print_string "\n"
