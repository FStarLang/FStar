module Realized

open FStar.Pervasives

(* Section 8.2: [FStar.Pervasives.dtuple3] is realized by hand-written OCaml,
   where it is a one-constructor *variant*.  Custard's record recovery
   (section 5.5) must leave it alone, its match must stay a match rather than
   becoming a field read, and its higher-kinded parameters must still be
   written -- the realization's arity is three however few of them Custard can
   name. *)
type triple = dtuple3 int (fun _ -> bool) (fun _ _ -> string)

let mk (n:int) : triple = (| n, true, "ok" |)

let snd_of (d:triple) : bool =
  match d with
  | (| _, b, _ |) -> b

(* Section 5.1: a [GTot] function's result is erased once the signature is
   *instantiated*.  [gmagic]'s declared result is the variable [a], which says
   nothing; at this call site it is a [squash], and the call has to disappear
   -- nothing realizes it. *)
assume val gmagic (#a:Type) (_:unit) : GTot a

let checked (x:int) (_:squash (x >= 0)) : int = x

let main () : FStar.All.ML unit =
  let d = mk (checked 3 (gmagic ())) in
  FStar.IO.print_string ((if snd_of d then "yes" else "no") ^ "\n")
