module Pulse.Steel.Wrapper

open Steel.ST.Effect
open Steel.Memory
open Steel.ST.Util
module U32 = FStar.UInt32
module G = FStar.Ghost
module A = Steel.ST.Array
module R = Steel.ST.Reference
module GR = Steel.ST.GhostReference
module Lock = Steel.ST.SpinLock
module US = FStar.SizeT

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

(* stt a pre post: The type of a pulse computation
   that when run in a state satisfying `pre`
   may loop forever
   but if it returns, it returns `x:a`
   such that the final state satisfies `post x` *)
inline_for_extraction
val stt (a:Type u#a) (pre:vprop) (post:a -> vprop) : Type0

(* stt_atomic a opened pre post: The type of a pulse computation
   that when run in a state satisfying `pre`
   takes a single concrete atomic step
   while relying on the ghost invariant names in `opened` 
   and returns `x:a`
   such that the final state satisfies `post x` *)
inline_for_extraction
val stt_atomic (a:Type u#a) (opened:inames) (pre:vprop) (post:a -> vprop) : Type u#(max 2 a)

(* stt_ghost a opened pre post: The type of a pulse computation
   that when run in a state satisfying `pre`
   takes a single ghost atomic step (i.e. a step that does not modify the heap, and does not get extracted)
   while relying on the ghost invariant names in `opened` 
   and returns `x:a`
   such that the final state satisfies `post x` *)
inline_for_extraction
val stt_ghost (a:Type u#a) (opened:inames) (pre:vprop) (post:a -> vprop) : Type u#(max 2 a)

//
// the returns should probably move to atomic,
//   once we have support for bind etc.
//

let eq2_prop (#a:Type) (x y:a) : prop = x == y
let iff_prop (p q:Type0) : prop = p <==> q
let and_prop (p q:Type0) : prop = p /\ q

inline_for_extraction
val return_stt (#a:Type u#a) (x:a) (p:a -> vprop)
  : stt a (p x) (fun r -> p r `star` pure (r == x))

inline_for_extraction
val return (#a:Type u#a) (x:a) (p:a -> vprop)
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

val rewrite (p:vprop) (q:vprop) (_:vprop_equiv p q)
  : stt_ghost unit emp_inames p (fun _ -> q)


open FStar.Ghost

(***** begin ref *****)

val alloc (#a:Type) (x:a)
  : stt (R.ref a) emp (fun r -> R.pts_to r full_perm x)
  
val read (#a:Type) (r:R.ref a) (#n:erased a) (#p:perm)
  : stt a
        (R.pts_to r p n)
        (fun x -> R.pts_to r p x `star` pure (reveal n == x))

let ( ! ) (#a:Type) (r:R.ref a) (#n:erased a) (#p:perm)
  : stt a (R.pts_to r p n)
          (fun x -> R.pts_to r p x `star`
                    pure (reveal n == x)) =
  read #a r #n #p

val write (#a:Type) (r:R.ref a) (x:a) (#n:erased a)
  : stt unit
        (R.pts_to r full_perm n) 
        (fun _ -> R.pts_to r full_perm (hide x))

let ( := ) (#a:Type) (r:R.ref a) (x:a) (#n:erased a)
  : stt unit (R.pts_to r full_perm n) (fun _ -> R.pts_to r full_perm (hide x)) =
  write #a r x #n

val read_atomic (r:R.ref U32.t) (#n:erased U32.t) (#p:perm)
  : stt_atomic U32.t emp_inames
               (R.pts_to r p n)
               (fun x -> R.pts_to r p n `star` pure (reveal n == x))

val write_atomic (r:R.ref U32.t) (x:U32.t) (#n:erased U32.t)
  : stt_atomic unit emp_inames
        (R.pts_to r full_perm n) 
        (fun _ -> R.pts_to r full_perm (hide x))

(***** end ref *****)

(***** begin ghost ref ******)


val galloc (#a:Type0) (x:erased a)
  : stt_ghost (GR.ref a) emp_inames emp (fun r -> GR.pts_to r full_perm x)

val gread (#a:Type0) (r:GR.ref a) (#v:erased a) (#p:perm)
  : stt_ghost (erased a) emp_inames
      (GR.pts_to r p v)
      (fun x -> GR.pts_to r p x `star` pure (v == x))

val gwrite (#a:Type0) (r:GR.ref a) (x:erased a) (#v:erased a)
  : stt_ghost unit emp_inames
      (GR.pts_to r full_perm v)
      (fun _ -> GR.pts_to r full_perm x)

val gshare (#a:Type0) (r:GR.ref a) (#v:erased a) (#p:perm)
  : stt_ghost unit emp_inames
      (GR.pts_to r p v)
      (fun _ ->
       GR.pts_to r (half_perm p) v `star`
       GR.pts_to r (half_perm p) v)

val ggather (#a:Type0) (r:GR.ref a) (#x0 #x1:erased a) (#p0 #p1:perm)
  : stt_ghost unit emp_inames
      (GR.pts_to r p0 x0 `star` GR.pts_to r p1 x1)
      (fun _ -> GR.pts_to r (sum_perm p0 p1) x0 `star` pure (x0 == x1))

val gfree (#a:Type0) (r:GR.ref a) (#v:erased a)
  : stt_ghost unit emp_inames
      (GR.pts_to r full_perm v)
      (fun _ -> emp)

(***** end ghost ref *****)

(***** begin array ******)

val new_array
  (#elt: Type)
  (x: elt)
  (n: US.t)
: stt (A.array elt) 
     (requires emp)
     (ensures fun a ->
        A.pts_to a full_perm (Seq.create (US.v n) x) `star`
        pure (A.length a == US.v n /\ A.is_full_array a))

(* 
   a: array int |- 
    { A.pts a q sq }
      index a 0ul : #s -> #p -> stt t (A.pts_to a p s `star` ...) (...)
*)
val op_Array_Access
  (#t: Type)
  (a: A.array t)
  (i: US.t)
  (#s: Ghost.erased (Seq.seq t))
  (#p: perm)
: stt t
    (requires
      A.pts_to a p s `star`
      pure (US.v i < A.length a \/ US.v i < Seq.length s))
    (ensures fun res ->
      A.pts_to a p s `star`
      pure (Seq.length s == A.length a /\
            US.v i < Seq.length s /\
            res == Seq.index s (US.v i)))

val op_Array_Assignment
  (#t: Type)
  (a: A.array t)
  (i: US.t)
  (v: t)
  (#s: Ghost.erased (Seq.seq t) {US.v i < Seq.length s})
: stt unit
    (requires A.pts_to a full_perm s)
    (ensures fun res -> A.pts_to a full_perm (Seq.upd s (US.v i) v))

val op_Array_Index
  (#t: Type)
  (a: A.array t)
  (#p: perm)
  (#s: Ghost.erased (Seq.seq t))
  (i: US.t{ US.v i < Seq.length s })
: stt t
    (requires A.pts_to a p s)
    (ensures fun res -> A.pts_to a p s `star` pure (res == Seq.index s (US.v i)))

val free_array
      (#elt: Type)
      (a: A.array elt)
      (#s: Ghost.erased (Seq.seq elt))
: stt unit
    (A.pts_to a full_perm s `star` pure (A.is_full_array a))
    (fun _ -> emp)

(***** begin spinlock *****)


val new_lock (p:vprop) : stt (Lock.lock p) p (fun _ -> emp)

val acquire (#p:vprop) (l:Lock.lock p)
  : stt unit emp (fun _ -> p)

val release (#p:vprop) (l:Lock.lock p)
  : stt unit p (fun _ -> emp)

(***** end spinlock *****)

val elim_pure_explicit (p:prop)
  : stt_ghost (squash p) emp_inames
              (pure p)
              (fun _ -> emp)

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

val intro_exists_erased (#a:Type) (p:a -> vprop) (e:erased a)
  : stt_ghost unit emp_inames (p (reveal e)) (fun _ -> exists_ p)

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

val stt_par
  (#aL:Type u#a)
  (#aR:Type u#a)
  (#preL:vprop)
  (#postL:aL -> vprop) 
  (#preR:vprop)
  (#postR:aR -> vprop)
  (f:stt aL preL postL)
  (g:stt aR preR postR)
  : stt (aL & aR)
        (preL `star` preR)
        (fun x -> postL (fst x) `star` postR (snd x))

val with_local
  (#a:Type0)
  (init:a)
  (#pre:vprop)
  (#ret_t:Type)
  (#post:ret_t -> vprop)
  (body:(r:R.ref a) -> stt ret_t (pre `star` R.pts_to r full_perm init)
                                 (fun v -> post v `star` exists_ (R.pts_to r full_perm)))
  : stt ret_t pre post

val assert_ (p:vprop)
  : stt_ghost unit emp_inames p (fun _ -> p)

val assume_ (p:vprop)
  : stt_ghost unit emp_inames emp (fun _ -> p)

val drop_ (p:vprop) 
  : stt_ghost unit emp_inames p (fun _ -> emp)