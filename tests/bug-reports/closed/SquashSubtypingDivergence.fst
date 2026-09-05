(*
   A lemma whose postcondition is a machine-integer fact used to make the
   typechecker diverge (allocation failure during minor GC, ~30GB and rising).

   Since a `Lemma post` is checked by relating `squash body_prop` to
   `squash post` by *subtyping*, the [squash <: squash] rule in
   FStarC.TypeChecker.Rel is what keeps this cheap: it makes [squash]
   transparent and relates the two propositions by implication.  That rule used
   to be disabled whenever either proposition mentioned *any* unification
   variable, and here the [#a:eqtype] of the left-hand [=] was still open, so
   the problem fell through to the [Tm_app] congruence rule instead.  Congruence
   then asked whether [pow2 2 - 1] and [FStar.UInt.logand c mask_2bit] are
   syntactically equal after full delta-unfolding, and unfolding
   [logand]/[to_vec]/[from_vec] at width 64 blows up exponentially.

   Reduced from GC.Lib.Header in FStarLang/pulse-verified-gc.
*)
module SquashSubtypingDivergence

open FStar.UInt

private let mask_2bit : uint_t 64 = logor #64 1 2

private let logor_1_2_eq_3 () : Lemma (logor #64 1 2 = 3) =
  logor_disjoint #64 2 1 1; logor_commutative #64 1 2

private let c_eq_c_and_mask2 (c: uint_t 64{c < 4}) : Lemma (logand #64 c mask_2bit = c) =
  logor_1_2_eq_3 (); logand_mask #64 c 2;
  assert_norm (pow2 2 = 4); assert_norm (pow2 2 - 1 = 3)

(* The same shape, but with a postcondition that does not follow: this must
   fail with an ordinary error rather than exhaust memory. *)
[@@expect_failure [19]]
private let unprovable (c: uint_t 64{c < 4}) : Lemma (logand #64 c mask_2bit = c) =
  assert (pow2 2 - 1 = 3)

(* And [introduce _ ==> _] must keep going through congruence: the two holes
   are explicit arguments of [FStar.Classical.Sugar.implies_intro] and only
   unification can solve them. *)
assume val p : int -> prop
assume val q : int -> prop
assume val lem (x:int) : Lemma (requires p x) (ensures q x)

private let introduce_still_works () : Lemma (forall (x:int). p x ==> q x) =
  introduce forall (x:int). p x ==> q x
  with introduce _ ==> _
  with lem x
