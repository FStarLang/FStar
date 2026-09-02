module Bug4521

(* `new` makes the SMT encoder emit a `constructor_distinct` axiom, fixing a
   fresh `Term_constr_id` for the declared symbol.  It used to be accepted on
   *any* `assume val`, including ones whose result type is not a sort.  Since
   the primitive types have inversion axioms phrased over `Term_constr_id`,
   that made the context inconsistent:

     assume new type b : int -> bool

   fixes an id for `b x : bool`, contradicting `bool_inversion`.

   The axiom is now emitted only when the declaration really does introduce a
   type constructor, and `new` on anything else is ignored with a warning. *)
#set-options "--warn_error -363"

assume new type b : int -> bool
assume new type i : int -> int
assume new type s : int -> string
assume new type u : int -> unit

[@@expect_failure [19]] let bad_b (x:int) : squash (b x == true) = ()
[@@expect_failure [19]] let bad_i (x:int) : squash (i x == 0)    = ()
[@@expect_failure [19]] let bad_s (x:int) : squash (s x == "")   = ()

(* This one *is* provable, and soundly so: `unit` is a singleton. *)
let ok_u (x:int) : squash (u x == ()) = ()

(* `prop` is not a sort either, so `p` is not a type constructor. *)
assume new type p : int -> prop
[@@expect_failure [19]] let bad_p (x:int) : squash (p x == True) = ()

(* A genuine type constructor declared `new` is distinct from all others, as it
   has always been. *)
assume new type t : Type0
let neq () : Lemma (~(t == int)) = ()

(* Without `new` there is no such axiom -- see Bug4521Abs.fsti for why it cannot
   be inferred -- but the type is still rigid and can still head a match
   scrutinee's type, which does not need `new`. *)
assume type t' : Type0
[@@expect_failure [19]] let neq' () : Lemma (~(t' == int)) = ()
let rigid (x : t') : t' = x

(* And an abstract type from an interface is not distinct from anything. *)
open Bug4521Abs
[@@expect_failure [19]] let bad_abs () : Lemma False = foo_eq_int ()
