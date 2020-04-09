module Bug310

(* a is rewritten to 'a
  'a is rewritten to 'a1 *)
type capture (a:Type) 'a = 'a * a

////////////////////////////////////////////////////////////////////////////////

(* rewritten to struct1 *)
let struct = 1
(* rewritten to struct11 *)
let struct1 = 2

////////////////////////////////////////////////////////////////////////////////

(* Extracted as:

  let test =
    let x = 0 in
    let x1 = 2 in
    x, x1
 *)
let test =
  let x = 0 in
  [@inline_let] let y = x in
  let x = 2 in
  (y, x)

////////////////////////////////////////////////////////////////////////////////

(* This one is due to an eta expanded magic.
   It has several ingredients *)

(* 1. Type type of `r` is not prenex quantified
      so `a:Type` is extracted as unit and `f:Obj.t -> Obj.t` *)
val r: unit -> a:Type -> f:(a -> a) -> int
let r _ _ _ = 0

(* 2. We're going partially apply `g` below *)
val g: int -> int -> int
let g _ _ = 0

(* [g a] has type [int -> int] but it has to be coerced to [Obj.t -> Obj.t]
   It gets eta-expanded to (fun uu_XX -> magic (g a) uu_XX))
   without any capture *)
val ko: int -> int
let ko a =
  let a = a in
  r () int (g a)

////////////////////////////////////////////////////////////////////////////////

//both field names are ocaml keywords
//They are extracted as
// - [struct1] (since it cannot clash with [struct1] above)
// - [constraint1]
type record_t = {
  struct : int;
  constraint: bool
}
