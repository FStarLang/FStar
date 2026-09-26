module Bug4487

(* FStarLang/FStar#4487: [U.term_eq] compared computation types by effect
   and result type only, ignoring their pre- and postconditions, so the VC
   simplifier rewrote [p ==> q] and [p <==> q] to [True] for [p], [q] that
   differ only in the postcondition of an arrow, proving [False]. Since
   #4515, a computation type has only a result type, and the postcondition
   is a refinement of it, which [term_eq] compares. *)

[@@expect_failure [19]]
let imp = assert_norm ( (forall (f: (unit -> Lemma False)). False)
                    ==> (forall (f: (unit -> Lemma True)). False) )

(* Both directions of the [<==>] are sent to the SMT solver. *)
[@@expect_failure [19; 19]]
let iff = assert_norm ( (forall (f: (unit -> Lemma False)). False)
                   <==> (forall (f: (unit -> Lemma True)). False) )

let ta : Type0 = unit -> Lemma True
let tb : Type0 = unit -> Lemma False

(* [tb] is empty ... *)
let step (f: tb) : Lemma False = f ()
let lhs () : Lemma (forall (f: tb). False) = FStar.Classical.forall_intro step

(* ... and [ta] is not, so these are false. *)
[@@expect_failure [19]]
let bridge () : Lemma ((forall (f: tb). False) ==> (forall (f: ta). False))
  = assert_norm ((forall (f: tb). False) ==> (forall (f: ta). False))

[@@expect_failure [19; 19]]
let bridge_iff () : Lemma ((forall (f: tb). False) <==> (forall (f: ta). False))
  = assert_norm ((forall (f: tb). False) <==> (forall (f: ta). False))

let elim (g: ta) : Lemma (requires forall (f: ta). False) (ensures False) = ()

(* The rest of the issue's proof of [False], with [bridge] as a hypothesis. *)
let bad (bridge: squash ((forall (f: tb). False) ==> (forall (f: ta). False)))
  : Lemma False =
  lhs ();
  elim (fun () -> ())

(* Controls from the issue: arrows differing in their effect are not equal
   ... *)
let tc : Type0 = unit -> Ghost unit (requires True) (ensures fun _ -> True)

[@@expect_failure [19]]
let bridge_effect () : Lemma ((forall (f: tb). False) ==> (forall (f: tc). False))
  = assert_norm ((forall (f: tb). False) ==> (forall (f: tc). False))

(* ... and an implication between the same arrow type holds. *)
let tb' : Type0 = unit -> Lemma False

let bridge_same () : Lemma ((forall (f: tb). False) ==> (forall (f: tb'). False))
  = assert_norm ((forall (f: tb). False) ==> (forall (f: tb'). False))
