module Pulse.Lib.Core

open Steel.ST.Effect
open Steel.ST.Effect.Atomic
open Steel.ST.Effect.Ghost
open Steel.Memory
open Steel.ST.Util
open Steel.ST.Loops
module T = FStar.Tactics

let vprop = vprop

[@@"__reduce__"; "__steel_reduce__"]
let emp = emp

[@@"__reduce__"; "__steel_reduce__"]
let op_Star_Star = star

let star_def (_:unit)
  : Lemma ( ( ** ) == star )
  = assert ( ( ** ) == star )
        by (T.trefl())

[@@"__reduce__"; "__steel_reduce__"]
let pure = pure
[@@"__reduce__"; "__steel_reduce__"]
let exists_ = exists_

let vprop_equiv (p q:vprop) = squash (equiv p q)
let vprop_post_equiv (#t:Type u#a) (p q: t -> vprop) = forall x. vprop_equiv (p x) (q x)
  
let intro_vprop_post_equiv
       (#t:Type u#a) 
       (p q: t -> vprop)
       (pf: (x:t -> vprop_equiv (p x) (q x)))
  : vprop_post_equiv p q
  = let pf = 
        introduce forall x. vprop_equiv (p x) (q x)
        with pf x
    in
    FStar.Squash.join_squash pf
       
let elim_vprop_post_equiv (#t:Type u#a)
                          (p q: t -> vprop) 
                          (pf:vprop_post_equiv p q)
                          (x:t) 
    : vprop_equiv (p x) (q x)
    = let pf : squash (vprop_equiv (p x) (q x))
             = eliminate forall x. vprop_equiv (p x) (q x) with x
      in
      FStar.Squash.join_squash pf

let vprop_equiv_refl (v0:vprop) 
  : vprop_equiv v0 v0
  = equiv_refl v0

let vprop_equiv_sym (v0 v1:vprop) (_:vprop_equiv v0 v1)
  : vprop_equiv v1 v0
  = equiv_sym v0 v1

let vprop_equiv_trans (v0 v1 v2:vprop) (_:vprop_equiv v0 v1) (_:vprop_equiv v1 v2)
  : vprop_equiv v0 v2
  = equiv_trans v0 v1 v2

let vprop_equiv_unit (x:vprop)
  : vprop_equiv (emp ** x) x
  = cm_identity x

let vprop_equiv_comm (p1 p2:vprop)
  : vprop_equiv (p1 ** p2) (p2 ** p1)
  = star_commutative p1 p2

let vprop_equiv_assoc (p1 p2 p3:vprop)
  : vprop_equiv ((p1 ** p2) ** p3) (p1 ** (p2 ** p3))
  = star_associative p1 p2 p3

let vprop_equiv_cong (p1 p2 p3 p4:vprop)
                     (_: vprop_equiv p1 p3)
                     (_: vprop_equiv p2 p4)
  : vprop_equiv (p1 ** p2) (p3 ** p4)
  = star_congruence p1 p2 p3 p4

let vprop_equiv_ext p1 p2 _ = equiv_refl p1

let iname = iname
let emp_inames = Ghost.hide Set.empty

inline_for_extraction
type stt (a:Type u#a) (pre:vprop) (post:a -> vprop) = unit -> STT a pre post

let mk_stt #a #pre #post e = e

let reveal_stt #a #pre #post e = e

inline_for_extraction
type stt_atomic (a:Type u#a) (opened:inames) (pre:vprop) (post:a -> vprop) =
  unit -> STAtomicT a opened pre post

let mk_stt_atomic #a #opened #pre #post e = e

let reveal_stt_atomic #a #opened #pre #post e = e
 
inline_for_extraction
type stt_ghost (a:Type u#a) (opened:inames) (pre:vprop) (post:a -> vprop) =
  unit -> STGhostT a opened pre post

let mk_stt_ghost #a #opened #pre #post e = e

let reveal_stt_ghost #a #opened #pre #post e = e

inline_for_extraction
let return_stt (#a:Type u#a) (x:a) (p:a -> vprop) =
  fun _ ->
    intro_pure (x == x);
    rewrite (p x ** pure (x == x))
            (p x ** pure (x == x));
    return x
    

inline_for_extraction
let return (#a:Type u#a) (x:a) (p:a -> vprop) =
  fun _ -> return x


inline_for_extraction
let return_stt_ghost (#a:Type u#a) (x:a) (p:a -> vprop) =
  fun _ ->
    intro_pure (x == x);
    rewrite (p x ** pure (x == x))
            (p x ** pure (x == x));
    x


inline_for_extraction
let return_stt_ghost_noeq (#a:Type u#a) (x:a) (p:a -> vprop) =
  fun _ ->
    let _ = noop() in x

inline_for_extraction
let bind_stt (#a:Type u#a) (#b:Type u#b) (#pre1:vprop) (#post1:a -> vprop) (#post2:b -> vprop)
  (e1:stt a pre1 post1)
  (e2:(x:a -> stt b (post1 x) post2))

  : stt b pre1 post2 =

  fun _ ->
  let x = e1 () in
  e2 x ()

inline_for_extraction
let lift_stt_atomic #a #pre #post e = fun _ -> e ()

inline_for_extraction
let bind_sttg #a #b #opened #pre1 #post1 #post2 e1 e2 =
  fun _ ->
  let x = e1 () in
  e2 x ()

let bind_stt_atomic_ghost #a #b #opened #pre1 #post1 #post2 e1 e2 reveal_b =
  fun _ ->
  let x = e1 () in
  let y =
    let y = e2 x () in
    rewrite (post2 y) (post2 (reveal_b (Ghost.hide y)));
    Ghost.hide y in
  Steel.ST.Util.return (reveal_b y)

let bind_stt_ghost_atomic #a #b #opened #pre1 #post1 #post2 e1 e2 reveal_a =
  fun _ ->
  let x =
    let x = e1 () in
    rewrite (post1 x) (post1 (reveal_a (Ghost.hide x)));
    Ghost.hide x in
  e2 (reveal_a x) ()

inline_for_extraction
let lift_stt_ghost #a #opened #pre #post e reveal_a =
  fun _ ->
  let x =
    let y = e () in
    rewrite (post y) (post (reveal_a (Ghost.hide y)));
    Ghost.hide y in
  Steel.ST.Util.return (reveal_a x)

inline_for_extraction
let frame_stt (#a:Type u#a) (#pre:vprop) (#post:a -> vprop) (frame:vprop) (e:stt a pre post)
  : stt a (pre ** frame) (fun x -> post x ** frame) =
  fun _ ->
    rewrite (pre ** frame) (pre ** frame);
    let x = e () in
    rewrite (post x ** frame) (post x ** frame);
    Steel.ST.Util.return x
    
let frame_stt_atomic #a #opened #pre #post frame e = 
  fun _ -> 
    rewrite (pre ** frame) (pre ** frame);
    let x = e () in
    rewrite (post x ** frame) (post x ** frame);
    Steel.ST.Util.return x    
    
let frame_stt_ghost #a #opened #pre #post frame e = 
  fun _ -> 
    rewrite (pre ** frame) (pre ** frame);
    let x = e () in
    rewrite (post x ** frame) (post x ** frame);
    x    

inline_for_extraction
let sub_stt (#a:Type u#a)
            (#pre1:vprop)
            (pre2:vprop)
            (#post1:a -> vprop)
            (post2:a -> vprop)
            (pf1 : vprop_equiv pre1 pre2)
            (pf2 : vprop_post_equiv post1 post2)
            (e:stt a pre1 post1)
  : stt a pre2 post2 =
  fun _ ->
    rewrite_equiv pre2 pre1;
    let x = e () in
    [@inline_let]    
    let pf : vprop_equiv (post1 x) (post2 x) = 
      elim_vprop_post_equiv post1 post2 pf2 x
    in
    rewrite_equiv (post1 x) (post2 x);
    Steel.ST.Util.return x

inline_for_extraction
let sub_stt_atomic #a #opened #pre1 pre2 #post1 post2 pf1 pf2 e =
  fun _ ->
  rewrite_equiv pre2 pre1;
  let x = e () in
  [@inline_let]    
  let pf : vprop_equiv (post1 x) (post2 x) = 
    elim_vprop_post_equiv post1 post2 pf2 x
  in
  rewrite_equiv (post1 x) (post2 x);
  Steel.ST.Util.return x

inline_for_extraction
let sub_stt_ghost #a #opened #pre1 pre2 #post1 post2 pf1 pf2 e =
  fun _ ->
  rewrite_equiv pre2 pre1;
  let x = e () in
  [@inline_let]    
  let pf : vprop_equiv (post1 x) (post2 x) = 
    elim_vprop_post_equiv post1 post2 pf2 x
  in
  rewrite_equiv (post1 x) (post2 x);
  x

let rewrite p q _ = fun _ -> rewrite_equiv p q


let elim_pure_explicit p = fun _ -> elim_pure p
let elim_pure _ #p = fun _ -> elim_pure p

let intro_pure p _ = fun _ -> let x = intro_pure p in x

let elim_exists #a p = fun _ -> elim_exists ()

let intro_exists #a p e = fun _ -> intro_exists e p

let intro_exists_erased #a p e = intro_exists p (reveal e)

let while_loop inv cond body = fun _ -> while_loop inv cond body

#push-options "--print_full_names"
val stt_ghost_reveal_aux (a:Type) (x:erased a)
  : stt_ghost a emp_inames Steel.ST.Util.emp (fun y -> Steel.ST.Util.pure (reveal x == y))
let stt_ghost_reveal_aux a x = fun _ ->
  noop(); reveal x


let stt_ghost_reveal a x = 
  fun _ -> 
    let y = stt_ghost_reveal_aux a x () in y

let stt_admit _ _ _ = admit ()
let stt_atomic_admit _ _ _ = admit ()
let stt_ghost_admit _ _ _ = admit ()


let stt_ghost_ni (#a:Type) (#p:vprop) (#q:a -> vprop)
  : non_informative_witness (stt_ghost a emp_inames p q)
  = fun x -> reveal x

let ghost_app (#a:Type) (#b:a -> Type) 
              ($f: (x:a -> b x))
              (y:erased a)
              ($w:(x:erased a -> non_informative_witness (b (reveal x))))
  : b (reveal y)
  = w y (hide (f (reveal y)))


let ghost_app2 (#a:Type) (#b:a -> Type) (#p:a -> vprop) (#q: (x:a -> b x -> vprop))
              (f: (x:a -> stt_ghost (b x) emp_inames (p x) (q x)))
              (y:erased a)
  : stt_ghost (b (reveal y)) emp_inames (p (reveal y)) (q (reveal y))
  = ghost_app f y (fun _ -> stt_ghost_ni)

let stt_par #aL #aR #preL #postL #preR #postR
            f g
  = fun _ -> 
     Steel.ST.Util.rewrite (preL ** preR) (preL ** preR);
     let x = par f g in
     Steel.ST.Util.rewrite (postL (fst x) ** postR (snd x))
             (postL (fst x) ** postR (snd x));
     Steel.ST.Util.return x

// let with_local #a init #pre #ret_t #post body =
//   fun _ -> 
//     let body (r:R.ref a) 
//       : STT ret_t
//         (pre ** R.pts_to r init)
//         (fun v -> post v ** exists_ (R.pts_to r))
//       = Steel.ST.Util.rewrite
//                 (pre ** R.pts_to r init)
//                 (pre ** R.pts_to r init);
//         let v = body r () in
//         Steel.ST.Util.rewrite
//                 (post v ** exists_ (R.pts_to r))
//                 (post v ** exists_ (R.pts_to r));
//         Steel.ST.Util.return v
//     in
//     let v = R.with_local init body in
//     Steel.ST.Util.return v    
    
    

let assert_ (p:vprop) = fun _ -> noop()

let assume_ (p:vprop) = fun _ -> admit_()
let drop_ (p:vprop) = fun _ -> let x = drop p in x 

let elim_false (a:Type) (p:a -> vprop) =
  fun _ ->
    let _ = Steel.ST.Util.elim_pure False in
    let x = false_elim #a () in
    Steel.ST.Util.rewrite Steel.ST.Util.emp (p x);
    x
