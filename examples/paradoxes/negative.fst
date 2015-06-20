module Negative

(* Example showing why we need the positivity check on inductives *)

(* this fails as it should:

type a =
  | C : (a -> Tot a) -> a

negative.fst(4,4-4,5) : Error
Constructor "C" fails the strict positivity check;
the constructed type occurs "a" occurs to the left of a pure function type

 *)

(* but if we allowed it ... *)

assume type a
assume val c : (a -> Tot a) -> Tot a
assume val invert_a : a -> Tot (a -> Tot a)

val bad : a -> Tot a
let bad a = let f = invert_a a in f a

val loop : a
let loop = bad (c bad)

(* ... we would be in big trouble

$ ../../bin/fstar.exe negative.fst --codegen OCaml --verify
OCaml: Negative
Gen Code: Negative
Verified module: Prims
Verified module: Negative
all verification conditions discharged successfully

$ echo "type a = C of (a -> a)" > Tmp.ml
$ echo "let c f = C f" >> Tmp.ml
$ echo "let invert_a x = let C f = x in f" >> Tmp.ml
$ cat Tmp.ml Negative.ml > Neg.ml
$ ocaml -init Neg.ml
        OCaml version 4.02.1

^CInterrupted.

The reduction sequence looks like this:

bad (c bad) ->                           (unfold)
let f = invert_a (c bad) in f (c bad) -> (match)
let f = bad in f (c bad) ->              (let)
bad (c bad)

Intuition:
- bad (c bad) is like a self-application,
  and c is there to make this type-check
- bad takes (c bad) as argument, removes the c and applies the
  remaining bad to (c bad), tying the knot
- c and invert_a establish a bijection between (a -> Tot a) and a:
  invert_a (c x) = x  and   c (invert_a (C f)) = C f
  and a has enough elements to make this impossible: loop, C (fun _ -> loop),...
 *)
