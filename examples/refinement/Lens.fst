module Lens 

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

(* Standard lens class *)
class lens a b = 
  { put : a -> b -> a; 
    get : a -> b;
    get_put : x:a -> Lemma (put x (get x) == x);
    put_get : x:a -> y:b -> Lemma (get (put x y) == y); 
    put_put : x:a -> y1:b -> y2:b -> Lemma (put (put x y1) y2 == put x y2) }

class low_state low = 
  { wf : HS.mem -> low -> Type } 

(* "Stack" lens  *)
class state_lens low (#c : low_state low) high = 
  { (* pure versions *)
    to_low : h:HS.mem -> ls:low{wf #_ #c h ls} -> high -> GTot (h':HS.mem{wf #_ #c h' ls}); 
    to_high : HS.mem -> low -> GTot high; 
    (* effectful versions to define morph *)         
    to_low' : ls:low -> hs:high -> 
              Stack unit (requires (fun h -> wf #_ #c h ls)) (ensures (fun h r h' -> wf h' ls /\ to_low h ls hs == h'));
    to_high' : ls:low -> Stack high (requires (fun h -> wf h ls)) (ensures (fun h r h' -> h == h' /\ to_high h ls == r));

    high_low : h:HS.mem -> ls:low{wf h ls} ->
               Lemma (to_low h ls (to_high h ls) == h);
    low_high : h:HS.mem -> ls:low{wf h ls} -> hs:high ->
               Lemma (to_high (to_low h ls hs) ls == hs); 
    low_low : h:HS.mem -> ls:low{wf h ls} -> hs1:high -> hs2:high ->
              Lemma (to_low h ls hs2 == to_low (to_low h ls hs1) ls hs2) }

(* Effect definition *)

let comp hstate a = hstate -> M (a * hstate) 

let hreturn hstate (a:Type) (x : a) : comp hstate a = fun s -> (x, s)

let hbind hstate (a:Type) (b:Type) (m : comp hstate a) (f : a -> comp hstate b) : comp hstate b =
  fun s -> let (x, s1) = m s in f x s1

let hread hstate () : comp hstate hstate =
  fun s -> (s, s)

let hwrite hstate (s':hstate) : comp hstate unit =
  fun s -> ((), s')
  
// Effect definition
total reifiable reflectable new_effect {
  HIGH_h (s:Type0) : a:Type -> Effect
        with repr  = comp s
        ; bind     = hbind s
        ; return   = hreturn s
        ; get      = hread s
        ; put      = hwrite s
  }

(* WPs of high computations *)
type hwp hstate a = HIGH_h?.wp hstate a
// hstate -> (a * hstate -> Type) -> GTot Type

type hpre #hstate = hstate -> Type0
type hpost #hstate a = hstate -> a -> hstate -> Type0

let monotonic #hstate #a (wp:hwp hstate a) =
  forall p1 p2 s. {:pattern wp s p1; wp s p2}
    (forall x.{:pattern (p1 x) \/ (p2 x)} p1 x ==> p2 x) ==>
    wp s p1 ==>
    wp s p2

type hwp_mon #hstate 'a = (wp:hwp hstate 'a{monotonic wp})

unfold
let as_wp (#state : Type) (#a : Type) (pre : hpre #state) (post : hpost a) : hwp_mon #state a =
  (fun s0 p -> pre s0 /\ (forall r s1. post s0 r s1 ==> p (r, s1)))

(* High compuations *)
type high #hstate a (wp : hwp_mon #hstate a) = s0:hstate -> PURE (a * hstate) (wp s0)

// Better name?
type high_p #hstate 'a (pre : hpre #hstate) (post : hpost #hstate 'a) = high 'a (as_wp #hstate #'a pre post)


(* Low computations *)
type low #lstate (#l:low_state lstate) #hstate (#p: state_lens lstate hstate)
         (a:Type) (wp : hwp_mon a) (c : high #hstate a wp) =
         ls:lstate ->
         Stack a
           (requires (fun h -> wf #_ #l h ls /\ (let s0 = to_high #_ #l #_ #p h ls in wp s0 (fun _ -> True))))
           (ensures  (fun h r h' ->
                       wf #_ #l h' ls /\
                      (let s0 = to_high #_ #l #_ #p h ls in
                       let (x, s1) = c s0 in
                       h' == to_low #_ #l #_ #p h ls s1 /\ x == r )))


let low_p #lstate (#l : low_state lstate) #hstate (#p: state_lens lstate hstate)
        (a : Type) pre post (c : high_p a pre post) = 
  low #lstate #l #hstate #p a
      (fun s0 p -> pre s0 /\ (forall r s1. post s0 r s1 ==> p (r, s1))) c

let run_high #hstate #a #wp (c:high #hstate a wp) (s0:_{wp s0 (fun _ -> True)}) : (a * hstate) = c s0

// "Lifting" of high programs to low programs
let morph #lstate (#l : low_state lstate) #hstate (#p: state_lens lstate hstate)
           (a:Type) (wp : hwp_mon a) (c : high #hstate a wp) : low #lstate #l #hstate #p a wp c =
  fun ls ->
    let hs = to_high' #_ #l #_ #p ls in 
    let (x, hs') = run_high c hs in
    to_low' #_ #l #_ #p ls hs'; x


(* High WPS *)

assume val range0: range

unfold
let return_wp #hstate (#a:Type) (x : a) : hwp_mon a = HIGH_h?.return_wp hstate a x
// fun (s0 : hstate) p -> p (x, s0)

unfold
let bind_wp #hstate #a #b (wp1:hwp_mon a) (fwp2 : (a -> hwp_mon b)) : (wp:hwp_mon b) =
    HIGH_h?.bind_wp hstate range0 a b wp1 fwp2
// fun (s0:hstate) p -> wp1 s0 (fun ((x, s1) : (a * hstate)) -> fwp2 x s1 p)

unfold 
let read_wp #hstate : hwp_mon hstate = fun (s: hstate) p -> p (s, s)

unfold 
let write_wp #hstate (s : hstate) : hwp_mon unit = fun (s0: hstate) p -> p ((), s)

unfold 
let read_comp_wp #hstate #a (l : lens hstate a) : hwp_mon a = fun (s: hstate) p -> p (get #hstate #a #l s, s)

unfold 
let write_comp_wp #hstate #a (l : lens hstate a) (x : a) : hwp_mon unit = fun (s0: hstate) p -> p ((), put #hstate #a #l s0 x)
  
(** Elaborated combinators **)
let return_elab (#hstate:Type) (#a:Type) (x : a) : high #hstate a (return_wp x) =
  HIGH_h?.return_elab hstate a x
// fun (s0 : hstate) -> (x, s0)

let bind_elab #hstate #a #b #f_w (f:high #hstate a f_w) #g_w ($g:(x:a) -> high #hstate b (g_w x)) 
: high #hstate b (bind_wp f_w g_w) = 
  HIGH_h?.bind_elab hstate a b f_w f g_w g
//fun s0 -> let (r1, s1) = run_high f s0 in run_high (g r1) s1

let read_elab #hstate (_ : unit) : high hstate read_wp = fun (s : hstate) -> (s, s) 

let write_elab #hstate (s : hstate) : high unit (write_wp s) = fun (s0 : hstate) -> ((), s) 

let read_comp #hstate #a (l : lens hstate a) (_ : unit) : high a (read_comp_wp l) = fun (s : hstate) -> (get #_ #_ #l s, s) 

let write_comp #hstate #a (l: lens hstate a) (x : a) : high unit (write_comp_wp l x) = fun (s0 : hstate) -> ((), put #_ #_ #l s0 x) 

let rec for_elab (#hstate:Type) (inv : hstate -> int -> Type0)
                 (f : (i:int) -> high_p unit (requires (fun h0 -> inv h0 i))
                                          (ensures (fun h0 _ h1 -> inv h1 (i + 1)))) 
                  (lo : int) (hi : int{lo <= hi}) 
: Tot (high_p unit (requires (fun h0 -> inv h0 lo))
                   (ensures (fun h0 _ h1 -> inv h1 hi))) (decreases (hi - lo)) =
  if lo = hi then (return_elab ())
  else 
    begin 
      let k () = for_elab inv f (lo + 1) hi in 
      bind_elab (f lo) k
    end


(* Low combinators *)

let lreturn #lstate (#l : low_state lstate) #state (#p: state_lens lstate state) (#a:Type) (x : a)
: low #_ #l #_ #p a (return_wp x) (return_elab x) = 
  fun ls -> 
     let h0 = ST.get () in
     let p = high_low #_ #l #_ #p h0 ls in (* 1st lens law *)
     assert (h0 == to_low h0 ls (to_high h0 ls));
     x

let lbind #lstate (#l:low_state lstate) #state (#p: state_lens lstate state) #a #b
    (#wp1:hwp_mon a) (#fwp2:(a -> hwp_mon #state b))
    (#c1:high #state a wp1) (#c2:(x:a -> high #state b (fwp2 x)))
    (m:low #lstate #l #state #p a wp1 c1) (f:(x:a) -> low #lstate #l #state #p b (fwp2 x) (c2 x)) :
    low #lstate #l #state #p b (bind_wp wp1 fwp2) (bind_elab c1 c2) =
  fun ls -> 
    (* almost verbatim from specialized [lbind] *)
    (* ********************************************* *)

    let h0 = ST.get () in // initial heap

    (* ********************************************* *)

    let x_a = m ls in 

    (* ********************************************* *)

    let h1 = ST.get () in // intermediate heap

    let hc : Ghost.erased _ =
      //In this block, we run the high computation
      //in ghost code and remember its intermediate states and result
      let s0 = to_high #_ #l #_ #p h0 ls in
      let x, s1 = run_high c1 s0 in
      assert (x == x_a);
      assert (h1 == to_low #_ #l #_ #p h0 ls s1);
      low_high h0 ls s1; //Get-Put: 1st lens law
      assert (to_high  #_ #l #_ #p h1 ls == s1); //this assertion is key to running `f x_a ls` below
      let y, s2 = run_high (c2 x) s1 in
      assert (s2 == snd (run_high #state #b #(bind_wp wp1 fwp2) (bind_elab c1 c2) s0));
      Ghost.hide (s0, (x, s1), (y, s2))
    in
  
    (* ********************************************* *)
    
    let y_b = f x_a ls in
    
    (* ********************************************* *)
    
    let h2 = ST.get () in // final heap
    let _ : unit =
      //In this block, we unpack the memoized result from earlier
      //and relate those values to the result and final heap
      let s0, (x, s1), (y, s2) = Ghost.reveal hc in
      assert (x == x_a);
      assert (y == y_b);
      assert (h2 == to_low #_ #l #_ #p h1 ls s2);
      assert (h1 == to_low #_ #l #_ #p h0 ls s1);
      let _ = low_low #_ #l #_ #p h0 ls s1 s2 in
      assert (to_low #_ #l #_ #p h0 ls s2 == to_low #_ #l #_ #p (to_low #_ #l #_ #p h0 ls s1) ls s2);
      assert (to_low #_ #l #_ #p h0 ls s2 == to_low #_ #l #_ #p h1 ls s2)
    in
  
    (* ********************************************* *)
    y_b


let lread #lstate (#l: low_state lstate) #state (#p: state_lens lstate state) (_ : unit) : low #_ #l #_ #p state read_wp (read_elab ()) = 
  fun ls ->
    let h0 = ST.get () in 
    let p = high_low h0 ls in (* lens law *)
    to_high' ls


let lwrite #lstate (#l:low_state lstate) #state (#p: state_lens lstate state) (s : state) : low #_ #l #_ #p unit (write_wp s) (write_elab s) =
   fun ls ->
     let h0 = ST.get () in 
     to_low' ls s

class commutes #low (#l:low_state low) #high #a (p : state_lens low high) (l1 : lens high a) (l2 : state_lens low a) = { 
  get_eq : h:HS.mem -> ls:low{wf #_ #l h ls} -> Lemma (get #_ #_ #l1 (to_high #_ #l #_ #p h ls) == to_high #_ #l #_ #l2 h ls);
  put_eq : h:HS.mem -> ls:low{wf #_ #l h ls} -> s:high -> x:a -> Lemma (to_low #_ #l #_ #p h ls (put #_ #_ #l1 s x) ==
                                                                    to_low #_ #l #_ #l2 (to_low #_ #l #_ #p h ls s) ls x);
}

(* rather unsatisfying since it require to first read all the low state *)
let lread_comp' #lstate (#l:low_state lstate) #state (#p: state_lens lstate state) #a (s : lens state a) (_ : unit) 
: low #_ #l #_ #p a (read_comp_wp s) (read_comp s ()) = 
  fun ls ->
    let h0 = ST.get () in 
    let p = high_low h0 ls in (* lens law *)
    get (to_high' ls)

(* add a third lens instance and require all three instances to commute *)
let lread_comp #lstate (#l:low_state lstate) #state (#p: state_lens lstate state) 
   (#a:eqtype) (#l1:lens state a) (l2:state_lens lstate a) (#c:commutes p l1 l2) (_ : unit) 
 : low #_ #l #_ #p a (read_comp_wp l1) (read_comp l1 ()) = 
  fun ls ->
    let h0 = ST.get () in 
    let p = high_low h0 ls in (* lens law *)
    let p' = get_eq h0 ls in
    to_high' #_ #l #_ #l2 ls

let lwrite_comp #lstate (#l:low_state lstate) #state (#p: state_lens lstate state) 
  (#a:eqtype) (#l1 : lens state a) (l2: state_lens lstate a) (#c : commutes p l1 l2) (x : a) 
 : low #_ #l #_ #p unit (write_comp_wp l1 x) (write_comp l1 x) =
  fun ls ->
    let h0 = ST.get () in 
    let peq = high_low h0 ls in 
    let p = put_eq #_ #_ #_ #_ #p #l1 #l2 h0 ls (to_high h0 ls) x in 
    to_low' #_ #l #_ #l2 ls x


let rec lfor' #lstate (#l:low_state lstate) #hstate (#p: state_lens lstate hstate) 
              (inv : hstate -> int -> Type0) 
              (fh : (i:int) -> high_p unit (fun h0 -> inv h0 i) (fun h0 _ h1 -> inv h1 (i + 1)))
              (f : (i:int) -> low_p #lstate #l #hstate #p unit (fun h0 -> inv h0 i)
                                                        (fun h0 _ h1 -> inv h1 (i + 1)) (fh i)) 
              (lo : int) (hi : int{lo <= hi}) : Tot (low_p #lstate #l #hstate #p unit 
                                                      (requires (fun h0 -> inv h0 lo))
                                                      (ensures (fun h0 _ h1 -> inv h1 hi))
                                                      (for_elab inv fh lo hi)) (decreases (hi - lo)) =
  if lo = hi then (lreturn #_ #l #_ #p ())
  else 
    begin 
      let k () = lfor' #_ #l #_ #p inv fh f (lo + 1) hi in 
      lbind #_ #l #_ #p (f lo) (fun _ -> 
      k ())
    end


(* TBD : 
   1.) Effect declaration -> the same as before but parametric in the hstate 
   2.) form of morph lemmas


  - Write morph lemmas with subsumption hyp 
    conclusion : l_eq 

  - for each action : lens between hstate and τ 
    low action : spec indexed by high lens and morph lemma

*)
