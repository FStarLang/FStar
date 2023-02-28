module Pulse.Steel.Wrapper

open Steel.ST.Effect
open Steel.Memory
open Steel.ST.Util

(***** begin vprop_equiv *****)

#set-options "--print_implicits --ugly --print_universes"
let e (p q:vprop) = p == q

val vprop_equiv (p q:vprop) : prop
val vprop_post_equiv (#t:Type u#a) (p q: t -> vprop) : prop

val intro_vprop_post_equiv
       (#t:Type u#a) 
       (p q: t -> vprop)
       (pf: (x:t -> vprop_equiv (p x) (q x)))
  : vprop_post_equiv p q

val elim_vprop_post_equiv (#t:Type u#a)
                          (p q: t -> vprop) 
                          (pf:vprop_post_equiv p q)
                          (x:t) 
    : vprop_equiv (p x) (q x)

val vprop_equiv_refl (v0:vprop) : vprop_equiv v0 v0

val vprop_equiv_sym (v0 v1:vprop) (_:vprop_equiv v0 v1)
  : vprop_equiv v1 v0

val vprop_equiv_trans (v0 v1 v2:vprop) (_:vprop_equiv v0 v1) (_:vprop_equiv v1 v2)
  : vprop_equiv v0 v2

val vprop_equiv_unit (x:vprop) : vprop_equiv (emp `star` x) x

val vprop_equiv_comm (p1 p2:vprop)
  : vprop_equiv (p1 `star` p2) (p2 `star` p1)

val vprop_equiv_assoc (p1 p2 p3:vprop)
  : vprop_equiv ((p1 `star` p2) `star` p3) (p1 `star` (p2 `star` p3))

val vprop_equiv_cong (p1 p2 p3 p4:vprop)
                     (_: vprop_equiv p1 p3)
                     (_: vprop_equiv p2 p4)
  : vprop_equiv (p1 `star` p2) (p3 `star` p4)

val vprop_equiv_ext (p1 p2:vprop) (_:p1 == p2)
  : vprop_equiv p1 p2

(***** end vprop_equiv *****)

(***** begin computation types and combinators *****)

val emp_inames : inames

inline_for_extraction
val stt (a:Type u#a) (pre:vprop) (post:a -> vprop) : Type0

inline_for_extraction
val stt_atomic (a:Type u#a) (opened:inames) (pre:vprop) (post:a -> vprop) : Type u#(max 2 a)

inline_for_extraction
val stt_ghost (a:Type u#a) (opened:inames) (pre:vprop) (post:a -> vprop) : Type u#(max 2 a)

//
// the returns should probably move to atomic,
//   once we have support for bind etc.
//

let eq2_prop (#a:Type) (x y:a) : prop = x == y
let iff_prop (p q:Type0) : prop = p <==> q

inline_for_extraction
val return_stt (#a:Type u#a) (x:a) (p:a -> vprop)
  : stt a (p x) (fun r -> p r `star` pure (eq2_prop r x))

inline_for_extraction
val return_stt_noeq (#a:Type u#a) (x:a) (p:a -> vprop)
  : stt a (p x) p

// Return in ghost?

inline_for_extraction
val bind_stt
  (#a:Type u#a) (#b:Type u#b)
  (#pre1:vprop) (#post1:a -> vprop) (#post2:b -> vprop)
  (e1:stt a pre1 post1)
  (e2:(x:a -> stt b (post1 x) post2))
  : stt b pre1 post2

inline_for_extraction
val lift_stt_atomic (#a:Type u#a) (#pre:vprop) (#post:a -> vprop)
  (e:stt_atomic a Set.empty pre post)
  : stt a pre post

inline_for_extraction
val bind_sttg
  (#a:Type u#a) (#b:Type u#b)
  (#opened:inames)
  (#pre1:vprop) (#post1:a -> vprop) (#post2:b -> vprop)
  (e1:stt_ghost a opened pre1 post1)
  (e2:(x:a -> stt_ghost b opened (post1 x) post2))
  : stt_ghost b opened pre1 post2

type non_informative_witness (a:Type u#a) =
  x:Ghost.erased a -> y:a{y == Ghost.reveal x}

inline_for_extraction
val bind_stt_atomic_ghost
  (#a:Type u#a) (#b:Type u#b)
  (#opened:inames)
  (#pre1:vprop) (#post1:a -> vprop) (#post2:b -> vprop)
  (e1:stt_atomic a opened pre1 post1)
  (e2:(x:a -> stt_ghost b opened (post1 x) post2))
  (reveal_b:non_informative_witness b)
  : stt_atomic b opened pre1 post2

inline_for_extraction
val bind_stt_ghost_atomic
  (#a:Type u#a) (#b:Type u#b)
  (#opened:inames)
  (#pre1:vprop) (#post1:a -> vprop) (#post2:b -> vprop)
  (e1:stt_ghost a opened pre1 post1)
  (e2:(x:a -> stt_atomic b opened (post1 x) post2))
  (reveal_a:non_informative_witness a)
  : stt_atomic b opened pre1 post2

inline_for_extraction
val lift_stt_ghost (#a:Type u#a) (#opened:inames) (#pre:vprop) (#post:a -> vprop)
  (e:stt_ghost a opened pre post)
  (reveal_a:(x:Ghost.erased a -> y:a{y == Ghost.reveal x}))
  : stt_atomic a opened pre post

inline_for_extraction
val frame_stt
  (#a:Type u#a)
  (#pre:vprop) (#post:a -> vprop)
  (frame:vprop)
  (e:stt a pre post)
  : stt a (pre `star` frame) (fun x -> post x `star` frame)

inline_for_extraction
val frame_stt_atomic
  (#a:Type u#a)
  (#opened:inames)
  (#pre:vprop) (#post:a -> vprop)
  (frame:vprop)
  (e:stt_atomic a opened pre post)
  : stt_atomic a opened (pre `star` frame) (fun x -> post x `star` frame)

inline_for_extraction
val frame_stt_ghost
  (#a:Type u#a)
  (#opened:inames)
  (#pre:vprop) (#post:a -> vprop)
  (frame:vprop)
  (e:stt_ghost a opened pre post)
  : stt_ghost a opened (pre `star` frame) (fun x -> post x `star` frame)

inline_for_extraction
val sub_stt (#a:Type u#a)
            (#pre1:vprop)
            (pre2:vprop)
            (#post1:a -> vprop)
            (post2:a -> vprop)
            (pf1 : vprop_equiv pre1 pre2)
            (pf2 : vprop_post_equiv post1 post2)
            (e:stt a pre1 post1)
  : stt a pre2 post2

inline_for_extraction
val sub_stt_atomic
  (#a:Type u#a)
  (#opened:inames)
  (#pre1:vprop)
  (pre2:vprop)
  (#post1:a -> vprop)
  (post2:a -> vprop)
  (pf1 : vprop_equiv pre1 pre2)
  (pf2 : vprop_post_equiv post1 post2)
  (e:stt_atomic a opened pre1 post1)
  : stt_atomic a opened pre2 post2

inline_for_extraction
val sub_stt_ghost
  (#a:Type u#a)
  (#opened:inames)
  (#pre1:vprop)
  (pre2:vprop)
  (#post1:a -> vprop)
  (post2:a -> vprop)
  (pf1 : vprop_equiv pre1 pre2)
  (pf2 : vprop_post_equiv post1 post2)
  (e:stt_ghost a opened pre1 post1)
  : stt_ghost a opened pre2 post2

inline_for_extraction
let unit_non_informative : non_informative_witness unit =
  fun u -> u

inline_for_extraction
let prop_non_informative : non_informative_witness prop =
  fun p -> p

inline_for_extraction
let erased_non_informative (a:Type u#a) : non_informative_witness (Ghost.erased u#a a) =
  fun x -> Ghost.reveal x

inline_for_extraction
let squash_non_informative (a:Type u#a) : non_informative_witness (squash  u#a a) =
  fun x -> x

(***** end computation types and combinators *****)


module G = FStar.Ghost
module U32 = FStar.UInt32
module R = Steel.ST.Reference

type u32 : Type0 = U32.t

open FStar.Ghost

val read (r:R.ref u32) (#n:erased u32) (#p:perm)
  : stt (x:u32{reveal n == x})
        (R.pts_to r p n)
        (fun x -> R.pts_to r p n)

val write (r:R.ref u32) (x:u32) (#n:erased u32)
  : stt unit
        (R.pts_to r full_perm n) 
        (fun _ -> R.pts_to r full_perm (hide x))

val read_pure (r:R.ref u32) (#n:erased u32) (#p:perm)
  : stt u32
        (R.pts_to r p n)
        (fun x -> R.pts_to r p n `star` pure (eq2_prop (reveal n) x))

val read_atomic (r:R.ref u32) (#n:erased u32) (#p:perm)
  : stt_atomic u32 emp_inames
               (R.pts_to r p n)
               (fun x -> R.pts_to r p n `star` pure (eq2_prop (reveal n) x))

val write_atomic (r:R.ref u32) (x:u32) (#n:erased u32)
  : stt_atomic unit emp_inames
        (R.pts_to r full_perm n) 
        (fun _ -> R.pts_to r full_perm (hide x))

val elim_pure (_:unit) (#p:prop)
  : stt_ghost (squash p) emp_inames
              (pure p)
              (fun _ -> emp)

val intro_pure (p:prop) (_:squash p)
  : stt_ghost unit emp_inames
              emp
              (fun _ -> pure p)

val elim_exists (#a:Type) (p:a -> vprop)
  : stt_ghost (erased a) emp_inames (exists_ p) (fun x -> p (reveal x))

val intro_exists (#a:Type) (p:a -> vprop) (e:a)
  : stt_ghost unit emp_inames (p e) (fun _ -> exists_ p)

val while_loop
  (inv:bool -> vprop)
  (cond:stt bool (exists_ inv) inv)
  (body:stt unit (inv true) (fun _ -> exists_ inv))
  : stt unit (exists_ inv) (fun _ -> inv false)

val stt_ghost_reveal (a:Type) (x:erased a)
  : stt_ghost a emp_inames emp (fun y -> pure (eq2_prop (reveal x) y))

val stt_admit (a:Type) (p:vprop) (q:a -> vprop) : stt a p q
val stt_atomic_admit (a:Type) (p:vprop) (q:a -> vprop) : stt_atomic a emp_inames p q
val stt_ghost_admit (a:Type) (p:vprop) (q:a -> vprop) : stt_ghost a emp_inames p q
