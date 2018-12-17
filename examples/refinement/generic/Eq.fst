module Eq

open Lens
open FStar.HyperStack
open FStar.HyperStack.ST
open LowStar.Buffer
open LowStar.BufferOps
open LowStar.Modifies
open Mem_eq
open Relations 

module H = FStar.Monotonic.Heap
module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module U32 = FStar.UInt32
module Map = FStar.Map
module M = LowStar.Modifies


(** ** Equality of high computations **)

 let h_eq #state (#a:Type) (wp1:hwp_mon #state a) (wp2:hwp_mon #state a) 
    (c1:high a wp1) (c2:high a wp2) =
    (forall s0. wp1 s0 (fun _ -> True) <==> wp2 s0 (fun _ -> True)) /\
    (forall s0. wp1 s0 (fun _ -> True) ==> c1 s0 == c2 s0)

let implies #state #a (wp1 : hwp_mon #state a) (wp2 : hwp_mon #state a) = forall s0 post. wp1 s0 post ==> wp2 s0 post

let h_eq_refl #state (#a:Type) (wp:hwp_mon a) (c:high a wp) : Lemma (h_eq wp wp c c) = ()

(** ** Equality of low computations **)
type lwp lstate a = lstate -> (HS.mem -> (a * HS.mem -> Type) -> Type)

let sat #lstate (#lw:low_state lstate) #a (wp:lwp lstate a) : Type = 
  forall (h:HS.mem) (ls:lstate{wf #_ #lw h ls}). wp ls h (fun _ -> True)

let precise #lstate (#lw:low_state lstate) #a (wp:lwp lstate a) =
  sat #_ #lw #_ wp ==>
  (forall h0 (ls:lstate{wf #_ #lw h0 ls}).
      wp ls h0 (fun (r1, h1) ->
      wp ls h0 (fun (r2, h2) ->
      r1 == r2 /\ h1 == h2)))

let lwp_eq #lstate (#lw:low_state lstate) #a (wp1:lwp lstate a) (wp2:lwp lstate a) =
  precise #_ #lw #_ wp1 /\
  precise #_ #lw #_ wp2 /\
  (forall ls h0 post. wp1 ls h0 post <==> wp2 ls h0 post)

let as_lwp #lstate (#lw:low_state lstate) #hstate (#p: state_lens lstate hstate) #a #wp 
   (c:high a wp) : lwp lstate a =
    fun ls h0 post ->
      wf #_ #lw h0 ls /\ (* ZP : /\ or ==> *)
      (let s0 = to_high #_ #lw #_ #p h0 ls in
       wp s0 (fun _ -> True) /\ (* ZP : /\ or ==> *)
       (let (x, s1) = c s0 in
        let h1 = to_low #_ #lw #_ #p h0 ls s1 in post (x, h1)))

let l_eq #lstate (#lw:low_state lstate) #hstate (#p: state_lens lstate hstate) #a
         (wp1:hwp_mon #hstate a) (c1:high a wp1) (lc1: low #_ #lw #_ #p a wp1 c1)
         (wp2:hwp_mon #hstate a) (c2:high a wp2) (lc2 : low #_ #lw #_ #p a wp2 c2) =
  lwp_eq #lstate #lw #a (as_lwp #_ #lw #_ #p c1) (as_lwp #_ #lw #_ #p c2)

let l_eq_alt #lstate (#lw:low_state lstate) #hstate (#p: state_lens lstate hstate) #a
         (#wp1:hwp_mon #hstate a) (#c1:high a wp1) (lc1: low #_ #lw #_ #p a wp1 c1)
         (#wp2:hwp_mon #hstate a) (#c2:high a wp2) (lc2 : low #_ #lw #_ #p a wp2 c2) =
    h_eq wp1 wp2 c1 c2 
    
let l_eq_alt_implies_l_eq #lstate (#lw:low_state lstate) #hstate (#p: state_lens lstate hstate) #a
                          (#wp1:hwp_mon #hstate a) (#c1:high a wp1) (lc1: low #_ #lw #_ #p a wp1 c1)
                          (#wp2:hwp_mon #hstate a) (#c2:high a wp2) (lc2 : low #_ #lw #_ #p a wp2 c2) :
    Lemma (requires (l_eq_alt #_ #lw  #_ #p lc1 lc2))
          (ensures (l_eq wp1 c1 lc1 wp2 c2 lc2)) = ()


(** Morph lemmas *)

unfold
let cast #hstate #a #wp1 (wp2:hwp_mon a{implies wp2 wp1}) (c : high #hstate a wp1) : high #hstate a wp2 = c 

unfold
let lcast #lstate (#lw:low_state lstate) #hstate (#p: state_lens lstate hstate) #a 
          (wp1 : hwp_mon a) (wp2: hwp_mon a{implies wp2 wp1}) (c : high #hstate a wp1) (l : low #_ #lw #_ #p a wp1 c) : low #_ #lw #_ #p a wp2 c = l

(** RETURN *)

(* The "easy" version *)
let morph_return' #lstate (#lw:low_state lstate) #hstate (#p: state_lens lstate hstate) #a
   (x:a) :
   Lemma
    (l_eq (return_wp x) (return_elab x) (morph #_ #lw  #_ #p a (return_wp x) (return_elab x)) 
          (return_wp x) (return_elab x) (lreturn x)) = () 

(* This formulation does not seem provable *)
[@expect_failure]
let morph_return_fail #lstate (#lw:low_state lstate) #hstate (#p: state_lens lstate hstate) #a
  (wp : hwp_mon #hstate a) (c:high a wp) (x:a) :
  Lemma
    (requires (implies wp (return_wp x) /\ c == return_elab x))
    (ensures (l_eq wp c (morph #_ #lw  #_ #p a wp c) 
                   (return_wp x) (return_elab x) (lreturn x))) =
  let i () : Lemma (implies wp (return_wp x)) = () in
  let i' = Classical.lemma_to_squash_gtot i () in 
  assert (c == cast #hstate #a #_ wp #i' (return_elab x));
  ()

// (* We would have to write something like this instead *)
// Redundant 
// let morph_return'' #lstate (#lw:low_state lstate) #hstate (#p: state_lens lstate hstate) #a
//     (wp : hwp_mon #hstate a) (c:high a wp) (x:a) :
//   Lemma
//     (requires (implies wp (return_wp x) /\ c == return_elab x))
//     (ensures (l_eq wp c (morph #_ #lw  #_ #p a wp c) 
//                    wp (return_elab x) (lcast (return_wp x) wp (return_elab x) (lreturn x)))) =
//   ()

let morph_return #lstate (#lw:low_state lstate) #hstate (#p: state_lens lstate hstate) #a
    (wp : hwp_mon #hstate a) (c:high a wp) (x:a) :
  Lemma
    (requires (implies wp (return_wp x) /\ c == return_elab x))
    (ensures (l_eq wp c (morph #_ #lw  #_ #p a wp c) 
                   wp (return_elab x) (lreturn #_ #lw #_ #p #a x))) =
  ()


let morph_bind #lstate (lw:low_state lstate) #hstate (#p: state_lens lstate hstate) #a #b
    (wp : hwp_mon #hstate b) (c:high b wp)
    (wp1 : hwp_mon #hstate a) (c1:high a wp1)
    (fwp : a -> hwp_mon #hstate b) (fc:(x:a) -> high b (fwp x))
    :
  Lemma
    (requires (implies wp (bind_wp wp1 fwp) /\ c == bind_elab c1 fc))
    (ensures (l_eq wp c (morph #_ #lw  #_ #p b wp c) 
                   wp (bind_elab c1 fc) (lbind #_ #lw #_ #p (morph #_ #lw #_ #p a wp1 c1) (fun x -> morph #_ #lw #_ #p b (fwp x) (fc x))))) =
  ()

let morph_write lstate (lw:low_state lstate) #hstate (#p: state_lens lstate hstate)
    (wp : hwp_mon #hstate unit) (c:high unit wp) (s:hstate) :
  Lemma
    (requires (implies wp (write_wp s) /\ c == write_elab s))
    (ensures (l_eq wp c (morph #_ #lw  #_ #p unit wp c) 
                   wp (write_elab s) (lwrite #_ #lw #_ #p s))) =
   ()

let morph_read lstate (lw:low_state lstate) #hstate (#p: state_lens lstate hstate)
    (wp : hwp_mon #hstate hstate) (c:high hstate wp) :
  Lemma
    (requires (implies wp read_wp) /\ c == read_elab ())
    (ensures (l_eq wp c (morph #_ #lw  #_ #p hstate wp c) 
                   wp (read_elab ()) (lread #_ #lw #_ #p ()))) =
  ()

let morph_write_comp lstate (lw:low_state lstate) #hstate (#p: state_lens lstate hstate)
    (#a:Type) (#l1:lens hstate a) (l2:state_lens lstate a) (#cm:commutes p l1 l2)
    (wp : hwp_mon #hstate unit) (c:high unit wp) (x:a) :
  Lemma
    (requires (implies wp (write_comp_wp l1 x) /\ c == write_comp l1 x))
    (ensures (l_eq wp c (morph #_ #lw  #_ #p unit wp c) 
                   wp (write_comp l1 x) (lwrite_comp #_ #lw #_ #p #a #l1 l2 #cm x))) =
  ()

let morph_read_comp lstate (lw:low_state lstate) #hstate (#p: state_lens lstate hstate)
    (#a:Type) (#l1:lens hstate a) (l2:state_lens lstate a) (#cm:commutes p l1 l2)
    (wp : hwp_mon #hstate a) (c:high a wp) :
  Lemma
    (requires (implies wp (read_comp_wp l1)) /\ c == read_comp l1 ())
    (ensures (l_eq wp c (morph #_ #lw  #_ #p a wp c) 
                   wp (read_comp l1 ()) (lread_comp #_ #lw #_ #p #a #l1 l2 #cm ()))) =
  ()

unfold
let inv_as_wp (#state : Type) (#a : Type) (inv : state -> int -> Type0) lo hi
: hwp_mon #state a =
  as_wp (fun h0 -> inv h0 lo) (fun h0 _ h1 -> inv h1 hi)

let morph_for lstate (lw:low_state lstate) #hstate (#p: state_lens lstate hstate)
    (wp : hwp_mon #hstate unit) (c:high unit wp)
    (inv : hstate -> int -> Type0)
    (f : (i:int) -> high_p unit (requires (fun h0 -> inv h0 i))
                             (ensures (fun h0 _ h1 -> inv h1 (i + 1)))) 
    (lo : int) (hi : int{lo <= hi}) :
  Lemma 
    (requires ((implies wp (inv_as_wp inv lo hi)) /\ c == for_elab inv f lo hi))
    (ensures (l_eq wp c (morph #_ #lw  #_ #p unit wp c) 
                   wp (for_elab inv f lo hi) (lfor' #_ #lw #_ #p inv f (fun i -> morph #_ #lw #_ #p unit _ (f i)) lo hi))) = 
  ()

