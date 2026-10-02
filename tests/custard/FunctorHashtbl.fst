module FunctorHashtbl
open FStar.All
open FStar.IO
open FStar.Attributes

(* Instantiating an OCaml functor (section 133).  An OCaml signature is an F*
   record type, and a functor is an [assume val] from one such record to
   another, tagged with the OCaml path it denotes.  Only the members the
   program uses need to be listed. *)

[@@custard_extern "int"]
assume new type ocaml_int : Type0

[@@custard_extern "Z.to_int"]
assume val to_ocaml_int (x:int) : ocaml_int

[@@custard_extern "Z.of_int"]
assume val of_ocaml_int (x:ocaml_int) : int

(* [Hashtbl.find] raises OCaml's own exception. *)
[@@custard_extern "Not_found"]
exception Not_found

[@@custard_extern "Hashtbl.hash"]
assume val poly_hash (#a:Type0) (x:a) : ocaml_int

(* Hashtbl.HashedType *)
noeq type hashed_type = {
  t: Type0;
  equal: t -> t -> bool;
  hash: t -> ocaml_int;
}

(* Hashtbl.S, restricted to what is used here.  The index is the sharing
   constraint [with type key = k]. *)
noeq type hashtbl_s (k:Type0) = {
  t: Type0 -> Type0;
  create: #a:Type0 -> ocaml_int -> ML (t a);
  replace: #a:Type0 -> t a -> k -> a -> ML unit;
  find_opt: #a:Type0 -> t a -> k -> ML (option a);
  find: #a:Type0 -> t a -> k -> ML a;
  length: #a:Type0 -> t a -> ML ocaml_int;
}

[@@custard_functor "Hashtbl.Make"]
assume val hashtbl_make (h:hashed_type) : hashtbl_s h.t

let string_tbl = hashtbl_make {
  t = string;
  equal = (fun (x y:string) -> x = y);
  hash = (fun (x:string) -> poly_hash (String.strlen x));
}

(* Generic code over any instance: the signature record stores a type, so it
   is compile-time only and this is specialized per instance. *)
let count_new (#k:Type0) (m:hashtbl_s k) (tbl:m.t int) (xs:list k) : ML int =
  let rec go (xs:list k) (n:int) : ML int =
    match xs with
    | [] -> n
    | x :: xs ->
      (match m.find_opt tbl x with
       | Some _ -> go xs n
       | None -> m.replace tbl x 1; go xs (n + 1)) in
  go xs 0

let show_opt (o:option int) : string =
  match o with
  | None -> "none"
  | Some n -> string_of_int n

let main () : ML unit =
  let tbl : string_tbl.t int = string_tbl.create (to_ocaml_int 16) in
  string_tbl.replace tbl "one" 1;
  string_tbl.replace tbl "two" 2;
  string_tbl.replace tbl "one" 11;
  print_string (show_opt (string_tbl.find_opt tbl "one")); print_string "\n";
  print_string (show_opt (string_tbl.find_opt tbl "three")); print_string "\n";
  let n = count_new string_tbl tbl ["two"; "three"; "four"; "three"] in
  print_string (string_of_int n); print_string "\n";
  print_string (string_of_int (of_ocaml_int (string_tbl.length tbl))); print_string "\n";
  print_string (try string_of_int (string_tbl.find tbl "five") with
                | Not_found -> "not found"
                | e -> raise e);
  print_string "\n"
