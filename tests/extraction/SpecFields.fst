module SpecFields

(* An implicit field of type [squash P] carries no computational content, so
   extraction drops it -- from the constructor's ML type, from the record's
   field list, and from every pattern that matches on it.  Each of those three
   used to be walked in parallel with a binder list that still had the field in
   it, so this module crashed extraction with
   [Invalid_argument "List.combine: list lengths differ"] and, once that was
   fixed, with ["Field name not found: SpecFields.st.m_ok"]. *)

noeq
type st (x:nat{x > 0}) = {
  m : int;
  d : int;
  #m_ok : squash (m == x);
  #d_ok : squash (d > 0);
}

let mk (x:nat{x > 0}) : st x = { m = x; d = 1 }

let get (x:nat{x > 0}) (s:st x) : int = s.m + s.d

let destruct (x:nat{x > 0}) (s:st x) : int =
  match s with
  | { m; d } -> m - d

(* The same, for a non-record inductive: a spec argument in the middle of a
   constructor's arguments must not shift the ones that follow it. *)
noeq
type t =
  | A : y:int -> squash (y > 0) -> z:int -> t
  | B : t

let proj (v:t) : int =
  match v with
  | A y _ z -> y + z
  | B -> 0

let main () : FStar.All.ML unit =
  FStar.IO.print_string (Prims.string_of_int (get 3 (mk 3)));
  FStar.IO.print_string (Prims.string_of_int (destruct 3 (mk 3)));
  FStar.IO.print_string (Prims.string_of_int (proj (A 1 () 2)));
  FStar.IO.print_newline ()

let _ : unit = main ()
