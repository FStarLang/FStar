(*
   [FStar.Classical.move_requires] applied to a lemma with no [requires].

   A [requires P] is elaborated to a trailing implicit [#(_: squash P)] binder,
   but the binder is omitted altogether when [P] is [True].  So a lemma written
   with only an [ensures] has one binder *fewer* than [move_requires] expects,
   and the arity mismatch has to be bridged by eta-expansion.  Eta-expansion
   used to bind the expected type's trailing [squash ?p x] binder verbatim,
   leaving [?p] unconstrained and reporting Error 66 on [move_requires]'s [#p].
   Binding [squash True] instead - [requires True] is the weakest precondition,
   so it is the most general choice - lets [?p := True] fall out of the ordinary
   check.

   Reduced from GC.Spec.Coalesce in FStarLang/pulse-verified-gc.
*)
module MoveRequiresNoPrecondition

assume val p : int -> prop
assume val q : int -> prop

(* No [requires]: the lemma has one binder fewer than [move_requires] expects. *)
private let no_precondition () : Lemma (forall (x:int). p x ==> q x) =
  let aux (x:int) : Lemma (p x ==> q x) = admit () in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

(* With a [requires]: the arities line up, and this always worked. *)
private let with_precondition () : Lemma (forall (x:int). p x ==> q x) =
  let aux (x:int) : Lemma (requires p x) (ensures q x) = admit () in
  FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

(* A concrete (non-uvar) expected precondition must still be left alone: using
   [e] at a stronger precondition than it demands is sound. *)
assume val r : int -> prop
private let stronger_precondition (aux: (x:int -> Lemma (requires p x) (ensures q x)))
  : x:int -> Lemma (requires p x /\ r x) (ensures q x)
  = aux
