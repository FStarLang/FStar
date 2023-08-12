module Pulse.Lib.Coinduction

open Steel.Memory

#push-options "--print_universes"

unfold
let inner_gfp #a (f: pred a -> pred a) (x: a) (p: pred a)
= h_and (p x) (pure (implies p (f p)))

let h_and_equiv (p q: slprop) (m:mem)
  : Lemma ((interp p m /\ interp q m) <==> interp (h_and p q) m)
= elim_h_and p q m; intro_h_and p q m

let inner_gfp_equiv
#a (f: pred a -> pred a) (x: a) (p: pred a) m
: Lemma (
    interp (inner_gfp f x p) m 
    <==> interp (p x) m /\ implies p (f p)
)
= h_and_equiv (p x) (pure (implies p (f p))) m;
  pure_interp (implies p (f p)) m

let gfp_sat_aux #a (f: pred a -> pred a) m x:
Lemma ((exists p. interp (p x) m /\ implies p (f p) ) <==> interp (gfp f x) m)
= introduce forall p. ((interp (p x) m /\ implies p (f p)) ==> interp (gfp f x) m) with (
    inner_gfp_equiv f x p m;
    intro_h_exists p (
        fun p -> h_and (p x) (pure (implies p (f p)))
    ) m
);
introduce interp (gfp f x) m ==> (exists p. interp (p x) m /\ implies p (f p) )
with _. (
    elim_h_exists (
        fun p -> h_and (p x) (pure (implies p (f p)))
    ) m;
    introduce forall p.
    (
        interp (inner_gfp f x p) m ==> (interp (p x) m /\ implies p (f p) )
    )
    with (
        inner_gfp_equiv f x p m
    )
)

let gfp_sat #a (f: pred a -> pred a):
Lemma (forall m x. (exists p. interp (p x) m /\ implies p (f p) ) <==> interp (gfp f x) m)
=  introduce forall m x. ((exists p. interp (p x) m /\ implies p (f p) ) <==> interp (gfp f x) m)
with (gfp_sat_aux f m x)

let set_D #a (f: pred a -> pred a) (p: pred a)
= (implies p (f p))


let in_D_implies_than_u #a (f: mono_fun a) p
: Lemma (requires set_D f p)
    (ensures implies p (gfp f))
= gfp_sat f

let lemma_D_aux #a (f: mono_fun a) p
: Lemma (requires set_D f p)
        (ensures implies p (f (gfp f)))
= 
let u = gfp f in
  in_D_implies_than_u f p;
  assert (implies (f p) (f u))

let lemma_D #a (f: mono_fun a)
: Lemma (forall p. set_D f p ==> implies p (f (gfp f)))
=
introduce forall p. (set_D f p ==> implies p (f (gfp f)))
with (
    introduce set_D f p ==> implies p (f (gfp f))
    with _. lemma_D_aux f p)

let gfp_implies_than_itself
    #a (f: mono_fun a)
: Lemma// (implies (gfp f) (f (gfp f)))
    (forall m x. interp (gfp f x) m ==> interp (f (gfp f) x) m)
= gfp_sat f; lemma_D f

let lemma_u_in_D #a (f: mono_fun a)
: Lemma (set_D f (gfp f))
= gfp_implies_than_itself f 

// Knaster-Tarski theorem
let gfp_is_fixed_point #a (f: mono_fun a)
    //Lemma (equivalent (gfp f) (f (gfp f)))
= gfp_implies_than_itself f; in_D_implies_than_u f (f (gfp f))

let gfp_is_largest_fp #a (f: mono_fun a) p
//:
//Lemma (requires equivalent p (f p))
//(ensures implies p (gfp f))
= gfp_sat f

let gfp_is_fixed_point_eq #a (f: mono_fun a):
    Lemma (forall x. gfp f x == f (gfp f) x)
= introduce forall x. (gfp f x == f (gfp f) x)
with (
    gfp_is_fixed_point f;
    //reveal_equiv (gfp f x) (f (gfp f) x);
    slprop_extensionality (gfp f x) (f (gfp f) x)
)

let coinduction #a (f: mono_fun a) (p: pred a):
    Lemma (requires implies p (f p))
    (ensures implies p (gfp f))
= gfp_sat f

let interp_rec_forall_def ty f x delta
: Lemma (interp_rec (Forall ty f) delta x == h_forall (fun y -> interp_rec (f y) delta x))
= assert_norm (interp_rec (Forall ty f) delta x == h_forall (fun y -> interp_rec (f y) delta x))

let interp_rec_exists_def ty f x delta
: Lemma (interp_rec (Exists ty f) delta x == h_exists (fun y -> interp_rec (f y) delta x))
= assert_norm (interp_rec (Exists ty f) delta x == h_exists (fun y -> interp_rec (f y) delta x))

let h_and_equiv_forall (p q: slprop):
    Lemma (forall m. interp (h_and p q) m <==> (interp p m /\ interp q m))
= introduce forall m. interp (h_and p q) m <==> (interp p m /\ interp q m)
  with h_and_equiv p q m

let h_or_equiv_forall (p q: slprop):
    Lemma (forall m. interp (h_or p q) m <==> (interp p m \/ interp q m))
= introduce forall m. (interp (h_or p q) m <==> (interp p m \/ interp q m))
with (
    elim_h_or p q m;
    intro_h_or_left p q m;
    intro_h_or_right p q m
)

let h_exists_equiv_forall p:
    Lemma (forall m. interp (h_exists p) m <==> (exists x. interp (p x) m))
= introduce forall m. (interp (h_exists p) m <==> (exists x. interp (p x) m))
  with (
    elim_h_exists p m;
    introduce forall w. (interp (p w) m ==> interp (h_exists p) m)
    with intro_h_exists w p m
  )

let h_forall_equiv p m:
    Lemma (interp (h_forall p) m <==> (forall x. interp (p x) m))
= intro_h_forall p m; 
  introduce forall x. (interp (h_forall p) m ==> interp (p x) m)
  with elim_h_forall p m x

let h_forall_equiv_forall p:
    Lemma (forall m. interp (h_forall p) m <==> (forall x. interp (p x) m))
= introduce forall m. (interp (h_forall p) m <==> (forall x. interp (p x) m))
  with h_forall_equiv p m

let star_equiv_forall p q:
    Lemma (forall m.
  (interp (p `star` q) m <==>
  (exists (mp: mem) (mq: mem) . disjoint mp mq /\ interp p mp /\ interp q mq /\ join mp mq == m)))
= introduce forall m.
    (interp (p `star` q) m <==>
    (exists (mp: mem) (mq: mem) . disjoint mp mq /\ interp p mp /\ interp q mq /\ join mp mq == m))
  with interp_star p q m

let wand_equiv_forall p q:
    Lemma (forall m.
    (interp (p `wand` q) m <==>
    (forall mp.
        disjoint m mp /\
        interp p mp ==>
        interp q (join m mp))))
= introduce forall m.
    (interp (p `wand` q) m <==>
    (forall mp.
        disjoint m mp /\ interp p mp ==> interp q (join m mp)))
with (
    intro_wand p q m;
    introduce forall m1. ((interp (wand p q) m /\ m `disjoint` m1 /\ interp p m1)
    ==> interp q (join m m1))
    with (
        elim_wand p q m m1
    )
)

let rec interp_rec_mono_aux #a (r: rec_def a) (p q: pred a) (x: a):
    Lemma (requires forall x. slimp (p x) (q x))
        (ensures slimp (interp_rec r p x) (interp_rec r q x))
= match r with
| And r1 r2 ->
    h_and_equiv_forall (interp_rec r1 p x) (interp_rec r2 p x);
    h_and_equiv_forall (interp_rec r1 q x) (interp_rec r2 q x);
    interp_rec_mono_aux r1 p q x;
    interp_rec_mono_aux r2 p q x
| Or r1 r2 ->
    h_or_equiv_forall (interp_rec r1 p x) (interp_rec r2 p x);
    h_or_equiv_forall (interp_rec r1 q x) (interp_rec r2 q x);
    interp_rec_mono_aux r1 p q x;
    interp_rec_mono_aux r2 p q x
| Forall ty fr ->
    introduce forall y. (slimp (interp_rec (fr y) p x) (interp_rec (fr y) q x))
        with (interp_rec_mono_aux (fr y) p q x);
    interp_rec_forall_def ty fr x p;
    interp_rec_forall_def ty fr x q;
    h_forall_equiv_forall (fun y -> interp_rec (fr y) p x);
    h_forall_equiv_forall (fun y -> interp_rec (fr y) q x)
| Exists ty fr ->
    introduce forall y. (slimp (interp_rec (fr y) p x) (interp_rec (fr y) q x))
        with (interp_rec_mono_aux (fr y) p q x);
    interp_rec_exists_def ty fr x p;
    interp_rec_exists_def ty fr x q;
    h_exists_equiv_forall (fun y -> interp_rec (fr y) p x);
    h_exists_equiv_forall (fun y -> interp_rec (fr y) q x)
| SLProp _ -> ()
| RecursiveCall f -> ()
| Star r1 r2 -> 
    star_equiv_forall (interp_rec r1 p x) (interp_rec r2 p x);
    star_equiv_forall (interp_rec r1 q x) (interp_rec r2 q x);
    interp_rec_mono_aux r1 p q x;
    interp_rec_mono_aux r2 p q x
| Wand f r' ->
    wand_equiv_forall (f x) (interp_rec r' p x);
    wand_equiv_forall (f x) (interp_rec r' q x);
    interp_rec_mono_aux r' p q x

let interp_rec_mono #a (r: rec_def a):
    Lemma (mono (interp_rec r))
= introduce forall p q x.
  ((forall x. slimp (p x) (q x)) ==> slimp (interp_rec r p x) (interp_rec r q x))
  with (
    introduce (forall x. slimp (p x) (q x)) ==> slimp (interp_rec r p x) (interp_rec r q x)
    with _. interp_rec_mono_aux r p q x
  )

let interp_rec_fold_unfold #a (p: rec_def a):
    Lemma (forall x. gfp (interp_rec p) x == interp_rec p (gfp (interp_rec p)) x)
= interp_rec_mono p; gfp_is_fixed_point_eq (interp_rec p)

let coinduction_principle (#a: Type) (r: rec_def a) (p: pred a)
= interp_rec_mono r; coinduction (interp_rec r) p