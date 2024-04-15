module Higher

open FStar.Tactics.Typeclasses

noeq
type code =
  | Eq : int -> int -> code
  | ForallInt : (int -> code) -> code

let rec interp (c : code) : prop =
  match c with
  | Eq x y -> x == y
  | ForallInt p -> forall (x:int). interp (p x)

class codeable (p : prop) = {
  code_of : code;
  pf : squash (interp code_of <==> p);
}

instance codeable_eq (x y : int) : codeable (x == y) = {
  code_of = Eq x y;
  pf = ();
}

instance codeable_forall
  (p : int -> prop)
  (d : (x:int) -> codeable (p x))
: codeable (forall (x:int). p x) = {
  code_of = ForallInt (fun x -> code_of #(p x) #(d x));
  pf = ();
}

let encode (p : prop) {| codeable p |} : code = code_of #p

let test0 = encode (1 == 1)
let _ = assert (test0 == Eq 1 1)

(* This example only works if the typeclass tactic introduces arrows,
as there is an intermediate goal for the `d` of `codeable_forall` *)
let test1 = encode (forall (x:int). x == x)
let _ = assert_norm (test1 == ForallInt (fun x -> Eq x x))
