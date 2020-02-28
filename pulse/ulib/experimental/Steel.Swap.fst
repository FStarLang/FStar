module Steel.Swap

open Steel.Permissions
open Steel.Memory
open Steel.Actions

open Steel.Effect
open Steel.SteelT.Basics

module Mem = Steel.Memory
module Act = Steel.Actions

type reference (a:Type0) = reference a (fun _ _ -> True)
type readable_perm = p:perm{readable p}

let pts_to_ref (#a:Type0) (r:reference a) (p:readable_perm) (x:a) = pts_to_ref r p x
let ref_perm (#a:Type0) (r:reference a) = ref_perm r

module T = FStar.Tactics

let ref_perm_implies_ref (#a:Type0) (r:reference a) (p:readable_perm) (m:mem)
: Lemma
  (requires interp (ref_perm r p) m)
  (ensures interp (ref r) m)
= intro_exists p (fun (p:perm{readable p}) -> Mem.ref_perm r p) m;
  assert (ref r == h_exists (fun (p:perm{readable p}) -> Mem.ref_perm r p))
    by (T.norm [delta_only [`%ref]])
  
let sel_ref_w (#a:Type0)
  (r:reference a) (p:readable_perm) (m:hmem (ref_perm r p))
= ref_perm_implies_ref r p m;
  sel_ref r m

let sel_ref_depends_only_on (#a:Type0) (r:reference a) (p:readable_perm)
  (m0:hmem (ref_perm r p)) (m1:mem)
: Lemma
  (requires disjoint m0 m1)
  (ensures
    interp (ref_perm r p) (join m0 m1) /\
    sel_ref_w r p m0 == sel_ref_w r p (join m0 m1))
  [SMTPat (sel_ref_w r p (join m0 m1))]
= Act.sel_ref_depends_only_on r p m0 m1

assume val read (#a:Type0) (p:readable_perm) (r:reference a)
: Steel a
    (ref_perm r p)
    (fun _ -> ref_perm r p)
    (fun _ -> True) (fun m0 x m1 -> sel_ref_w r p m0 == x /\ sel_ref_w r p m1 == x)

assume val write (#a:Type0) (r:reference a) (x:a)
: Steel unit
    (ref_perm r full_perm)
    (fun _ -> ref_perm r full_perm)
    (fun _ -> True)
    (fun _ _ m -> sel_ref_w r full_perm m == x)

open FStar.Integers

let writable (#a:Type0) (r:reference a) = ref_perm r full_perm

let sel_ref (#a:Type0) (r:reference a) (m:hmem (ref_perm r full_perm)) =
  sel_ref_w r full_perm m

let incr (r:reference uint_32)
: Steel unit
    (writable r)
    (fun _ -> writable r)
    (fun m -> ok (+) (sel_ref r m) 1ul /\ True)
    (fun m0 _ m1 -> v (sel_ref r m1) == v (sel_ref r m0) + 1)
= let n = read full_perm r in
  write r (n + 1ul)

let incr_and_frame (r1 r2:reference uint_32)
: Steel unit
    (writable r1 `star` writable r2)
    (fun _ -> writable r1 `star` writable r2)
    (fun m -> ok (+) (sel_ref r1 m) 1ul /\ v (sel_ref r2 m) > 2)
    (fun m0 _ m1 ->
      v (sel_ref r1 m1) == v (sel_ref r1 m0) + 1 /\
      v (sel_ref r2 m1) > 2)
= steel_frame (fun _ -> incr r1) (writable r2) (fun m -> interp (ref_perm r2 full_perm) m /\ v (sel_ref r2 m) > 2)


// assume val sel_ref_core (#a:Type0) (r:reference a) (p:permission{allows_read p}) (m:mem)
// : Lemma
//   (requires interp (ref_perm r p) m)
//   (ensures sel_ref r p m == sel_ref r p (core_mem m))
//   [SMTPat (sel_ref r p (core_mem m))]

// assume Interp_depends_only_on:
//   forall (hp:hprop) (m0:hmem hp) (m1:mem{disjoint m0 m1}).
//      interp hp m0 == interp hp (join m0 m1)

// assume val core_mem_interp (hp:hprop) (m:mem)
// : Lemma
//   (interp hp (core_mem m) == interp hp m)
//   [SMTPat (interp hp (core_mem m))]



// let sel_ref_is_a_refinement (#a:Type0) (r:reference a) (x:a)
// : Lemma
//   (forall (m0:hmem (ref r)) (m1:mem{disjoint m0 m1}).
//      (interp (ref r) m0 /\ sel_ref r m0 == x)  <==>
//      (interp (ref r) (join m0 m1) /\ sel_ref r (join m0 m1) == x))
// = ()


// let sel_ref_is_a_refinement (#a:Type0) (r:reference a) (x:a)
// : Lemma
//   (forall m0 m1. ((interp (ref r) m0 /\ sel_ref r m0 == x) /\ disjoint m0 m1) ==>
//             (interp (ref r) (join m0 m1) /\ sel_ref r (join m0 m1) == x))
// = ()


// let sel_ref_is_a_refinement (#a:Type0) (r1:reference a)
// : Lemma
//   (forall m x. (interp (ref r1) m /\ sel_ref r1 m == x) == (interp (ref r1) (core_mem m) /\ sel_ref r1 (core_mem m) == x))
// = ()

// unfold
// let sel_ref_mprop (#a:Type0) (r:reference a) (p:permission{allows_read p}) (x:a)
// : mem -> prop
// = fun m -> interp (ref_perm r p) m /\ sel_ref r p m == x

// #push-options "--warn_error -271"
// let sel_ref_depends_only_on_aux (#a:Type0) (r:reference a) (p:permission{allows_read p}) (x:a)
// : Lemma
//   (forall (m:mem). (interp (ref_perm r p) m /\ sel_ref r p m == x) == (interp (ref_perm r p) (core_mem m) /\ sel_ref r p (core_mem m) == x))
// = let aux (m:mem)
//     : Lemma
//       ((interp (ref_perm r p) m /\ sel_ref r p m == x) == (interp (ref_perm r p) (core_mem m) /\ sel_ref r p (core_mem m) == x))
//       [SMTPat ()]
//     = FStar.PropositionalExtensionality.apply (sel_ref_mprop r p x m) (sel_ref_mprop r p x (core_mem m)) in
//   ()
// #pop-options

// let sel_ref_refine_depends_only_on (#a:Type0) (r:reference a) (p:permission{allows_read p}) (x:a)
// : Lemma
//   (sel_ref_mprop r p x `refine_mprop_depends_only_on` (ref_perm r p))
// = sel_ref_depends_only_on_aux r p x


// unfold
// let sel_ref_as_refinement (#a:Type0) (r:reference a) (p:permission{allows_read p}) (x:a)
// : refine_mprop (ref_perm r p)
// = sel_ref_refine_depends_only_on r p x;
//   sel_ref_mprop r p x


// assume val refine_intro (p0 p1:hprop) (q:refine_mprop p0)
// : Steel unit
//     (p0 `star` p1)
//     (fun _ -> refine p0 q `star` p1)
//     (fun m -> q m)
//     (fun _ _ _ -> True)
    

// assume val steel_assert (#pre:pre_t) (p:mprop pre)
// : Steel unit pre (fun _ -> emp)
//     (fun m -> p m)
//     (fun _ _ _ -> True)

// assume val steel_admit (#a:_) (#pre:pre_t) (#post:post_t a) (_:unit)
// : Steel a pre post (fun _ -> True) (fun _ _ _ -> False)



// let swap (#a:Type0) (r1 r2:reference a)
// : Steel unit
//     (ref_perm r1 writable `star` ref_perm r2 writable)
//     (fun _ -> (ref_perm r1 writable `star` ref_perm r2 writable))
//     (fun _ -> True)
//     (fun m0 _ m1 ->
//       sel_ref r1 m1 == sel_ref r2 m0 /\
//       sel_ref r2 m1 == sel_ref r1 m0)
// = //(ref_perm r1 writable `star` ref_perm r2 writable)
//   let x = steel_frame (read r1) (ref_perm r2 writable) (fun _ -> True) in

//   //(pts_to_ref r1 writable x `star` ref_perm r2 writable) and sel_ref r1 m == x
//   refine_intro (pts_to_ref r1 writable x) (ref_perm r2 writable) (sel_ref_as_refinement r1 x);

//   //refine (pts_to_ref r1 writable x) (sel_ref_as_refinement r1 x)
//   //*
//   //ref_perm r2 writable

//   h_commute (refine (pts_to_ref r1 writable x) (sel_ref_as_refinement r1 x)) (ref_perm r2 writable);

//   //ref_perm r2 writable
//   //*
//   //refine (pts_to_ref r1 writable x) (sel_ref_as_refinement r1 x)

//   let y = steel_frame (read r2) (refine (pts_to_ref r1 writable x) (sel_ref_as_refinement r1 x)) (fun _ -> True) in

//   refine_intro (pts_to_ref r2 writable y) (refine (pts_to_ref r1 writable x) (sel_ref_as_refinement r1 x)) (sel_ref_as_refinement r2 y);

//   //refine (pts_to_ref r2 writable y) (sel_ref_as_refinement r2 y)
//   //*
//   //refine (pts_to_ref r1 writable x) (sel_ref_as_refinement r1 x)


//   steel_admit ()

