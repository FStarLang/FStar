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

(* An implicit argument of a *user-defined* function, on the other hand, must
   keep vetoing the rule: it need not be determined by anything around it, and
   congruence against the expected type is the only thing that can solve it.

   Here [#c] of [proj2_of_3] is open in the type of [f]'s binder, because the
   list is empty and [#c] occurs nowhere else.  Checking [f]'s body relates
   [pf]'s type to the type [mk] expects, and that congruence is what commits
   [#c].  When the [squash <: squash] rule fired here instead, [#c] survived
   into [f]'s type as a spurious generalized [#_: Type] binder, and every call
   site of [f] then failed with "Failed to resolve implicit argument".

   Reduced from [ASN1.Syntax.asn1_any_oid] in project-everest/everparse. *)
module L = FStar.List.Tot

private let proj2_of_3 (#a #b : Type) (#c : a -> b -> Type)
                       (x : dtuple3 a (fun _ -> b) c) : a & b =
  let (| x1, x2, _ |) = x in (x1, x2)

assume val r : int -> string -> Type0
private let item_k : Type = a:int & b:string & r a b
private let id_dec : Type = int & string
private let wf (li : list id_dec) : prop = L.length li >= 0

assume val mk (prefix : list item_k)
              (pf : squash (wf (L.map proj2_of_3 prefix))) : int

private let f (pf : squash (wf (L.map proj2_of_3 []))) : int = mk [] pf

private let f_is_applicable = f ()
