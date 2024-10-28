module Bug2895

// let rec not used
#set-options "--warn_error -328"

(* Recursive functions must be literals, but the annotated type
can be an _abbreviation_ of an arrow type, as in the examples that
follow. See issue #2895. *)

type foo (t:Type) = t -> bool
val f : foo string
let rec f (u : string) : bool = false
let test = f "123"

(* From the issue *)
type comparator_for (t:Type) = t -> t -> bool
val univ_eq : comparator_for int
let rec univ_eq (u1 u2 : int) : bool = false

(* A more involved variant, that could fail to extract due to coercions.
*)

type cmpres #t (x y : t) = bool
type comparator_for' (t:Type) = x:t -> y:t -> cmpres x y

let string_eq : comparator_for' string = fun x y -> x = y
let bool_eq : comparator_for' bool = fun x y -> x = y

type sb = | S of string | B of bool
val sb_eq : comparator_for' sb

(* The body of this function gets a coercion, as the branches
are of seemingly different types (due to the refinement). Extraction
must make sure to push that coercion in, or we otherwise define
an ocaml let rec where the body is an Obj.magic call (and not
a literal fun), which fails to compile. *)
let rec sb_eq (sb1 sb2 : sb) : cmpres sb1 sb2 =
  match sb1, sb2 with
  | S s1, S s2 -> string_eq s1 s2
  | B b1, B b2 -> bool_eq b1 b2
  | _ -> false
