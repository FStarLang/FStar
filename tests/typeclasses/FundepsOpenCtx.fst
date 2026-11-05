module FundepsOpenCtx

(* Typeclass goals in a context with free uvars. Here [ec : vec int ?u] is a
   binder of the signature, so every goal below has an open context. The
   [has_rep] goal is open only at its fundep position and determines [?u];
   the [can_approx] goal can only be solved after that. This must work
   regardless of the order of the conjuncts. *)

[@@FStar.Tactics.Typeclasses.fundeps [1]]
class can_approx (c m : Type) = { approx : c -> m -> prop }

[@@FStar.Tactics.Typeclasses.fundeps [1]]
class has_rep (p r : Type) = { rep : p -> r -> prop }

noeq type vec (a:Type) (n:nat) = | V : (f:(i:nat{i < n} -> a)) -> vec a n
assume val arr (n:nat) : Type0

instance vec_approx (a:Type) (n:nat) : can_approx (vec a n) (vec bool n) = { approx = (fun _ _ -> True) }
instance arr_rep (n:nat) : has_rep (arr n) (vec int n) = { rep = (fun _ _ -> True) }

let (%~) (#c #m:Type) {| can_approx c m |} (x:c) (y:m) : prop = approx x y
let ( |~> ) (#p #r:Type) {| has_rep p r |} (x:p) (y:r) : prop = rep x y

val f1 (#n:nat) (c:arr n) (#ec:vec int _) (rc:vec bool n)
  : Lemma (requires ec %~ rc /\ c |~> ec) (ensures True)
let f1 c rc = ()

val f2 (#n:nat) (c:arr n) (#ec:vec int _) (rc:vec bool n)
  : Lemma (requires c |~> ec /\ ec %~ rc) (ensures True)
let f2 c rc = ()

val f3 (#n #k:nat) (a:arr k) (c:arr n) (#ea:vec int _) (#ec:vec int _) (ra:vec bool k) (rc:vec bool n)
  : Lemma (requires ea %~ ra /\ ec %~ rc /\ a |~> ea /\ c |~> ec) (ensures True)
let f3 a c ra rc = ()
