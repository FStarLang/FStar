module Pulse.Lib.Coinduction

open Steel.DisposableInvariant
open Steel.Memory

type pred a = (a -> slprop)

let implies #a (p q: pred a) = (forall x. slimp (p x) (q x))

let mono #a (f: pred a -> pred a) =
    (forall p q x. (forall y. slimp (p y) (q y)) ==> slimp (f p x) (f q x))

let mono_fun a = (f: (pred a -> pred a){mono f})

let gfp #a (f: pred a -> pred a): pred a
= (fun x -> (h_exists (fun p -> h_and (p x) (pure (implies p (f p))))))
// x -> (exists (p:slprop). p x /\ p ==> f p)

// Knaster-Tarski theorem
val gfp_is_fixed_point (#a: Type) (f: mono_fun a):
    Lemma (forall x. equiv (gfp f x) (f (gfp f) x))

val gfp_is_largest_fp (#a: Type) (f: mono_fun a) (p: pred a):
    Lemma (requires forall x. equiv (p x) (f p x))
          (ensures forall x. (slimp (p x) (gfp f x)))

val gfp_is_fixed_point_eq (#a: Type) (f: mono_fun a):
    Lemma (forall x. gfp f x == f (gfp f) x)

// one can prove that any element satisfying p also satisfies gfp f
// as long as f preserves p (p ==> f p)
val coinduction (#a: Type) (f: mono_fun a) (p: pred a):
    Lemma (requires implies p (f p))
    (ensures implies p (gfp f))

noeq
type rec_def (a: Type) =
| Star: rec_def a -> rec_def a -> rec_def a
| And: rec_def a -> rec_def a -> rec_def a
| Or: rec_def a -> rec_def a -> rec_def a
| Wand: (a -> slprop) -> rec_def a -> rec_def a // prevents contravariant recursion
| RecursiveCall: (a -> a) -> rec_def a
| SLProp: (a -> slprop) -> rec_def a
| Exists: t:Type0 -> (t -> rec_def a) -> rec_def a
| Forall: t:Type0 -> (t -> rec_def a) -> rec_def a

let rec interp_rec #a (r: rec_def a) (delta: pred a): pred a
= fun x -> (
    match r with
    | Star r1 r2 -> star (interp_rec r1 delta x) (interp_rec r2 delta x)
    | And r1 r2 -> h_and (interp_rec r1 delta x) (interp_rec r2 delta x)
    | Or r1 r2 -> h_or (interp_rec r1 delta x) (interp_rec r2 delta x)
    | Wand f r' -> wand (f x) (interp_rec r' delta x)
    | RecursiveCall f -> delta (f x)
    | SLProp f -> f x
    | Exists ty f -> h_exists (fun y -> interp_rec (f y) delta x)
    | Forall ty f -> h_forall (fun y -> interp_rec (f y) delta x)
)

val interp_rec_mono (#a: Type) (r: rec_def a):
    Lemma (mono (interp_rec r))

let coinduct (#a: Type) (r: rec_def a): pred a
= gfp (interp_rec r)

val interp_rec_fold_unfold (#a: Type) (r: rec_def a):
    Lemma (forall x. coinduct r x == interp_rec r (coinduct r) x)

val coinduction_principle (#a: Type) (r: rec_def a) (p: pred a):
    Lemma (requires implies p (interp_rec r p))
    (ensures implies p (coinduct r))

module R = Steel.Reference
open Steel.FractionalPermission

noeq
type cell (a: Type0) = {
    v: a;
    next: R.ref (cell a)
}

#set-options "--print_universes"

// stream(x) = exists v. x |-> v ** stream(v)
let rec_stream a //(f: nat -> ref int) =
: rec_def (R.ref (cell a))
= Exists _ (fun v -> Star (SLProp (fun x -> R.pts_to_sl x full_perm v))
    (RecursiveCall (fun _ -> v.next)))

// stream(x) = exists v. x -> v ** stream(v.next)

//let coinduct (#a: Type) (r: rec_def a): pred a
let stream a: pred (R.ref (cell a)) = coinduct (rec_stream a)

let interp_rec_exists_def ty f x delta
: Lemma (interp_rec (Exists ty f) delta x == h_exists (fun y -> interp_rec (f y) delta x))
= assert_norm (interp_rec (Exists ty f) delta x == h_exists (fun y -> interp_rec (f y) delta x))

let interp_rec_fold_unfold_stream (a: Type) (r: rec_def a) (x:R.ref(cell a)) :
    Lemma (stream a x == h_exists (fun v -> R.pts_to_sl x full_perm v `star` stream a (v.next)))
= 
    calc (==) {
        stream a x;
        == { interp_rec_fold_unfold (rec_stream a) }
        interp_rec (rec_stream a) (stream a) x;
        == { }
         interp_rec (Exists _ (fun v -> Star (SLProp (fun x -> R.pts_to_sl x full_perm v))
        (RecursiveCall (fun _ -> v.next)))) (stream a) x;
        == { _ by (Tactics.compute ()) }
        h_exists (fun v -> R.pts_to_sl x full_perm v `star` stream a (v.next));
    }