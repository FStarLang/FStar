module Lens 


open LowComp
open HighComp
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

(* A more specific one for our case *)
class state_lens low (high:eqtype) = 
  { wf : HS.mem -> low -> Type;
    (* pure versions *)
    to_low : h:HS.mem -> ls:low{wf h ls} -> high -> GTot (h':HS.mem{wf h' ls}); 
    to_high : HS.mem -> low -> GTot high; 
    (* effectful versions to define morph *)         
    to_low' : ls:low -> hs:high -> 
              Stack unit (requires (fun h -> wf h ls)) (ensures (fun h r h' -> wf h' ls /\ to_low h ls hs == h'));
    to_high' : ls:low -> Stack high (requires (fun h -> wf h ls)) (ensures (fun h r h' -> h == h' /\ to_high h ls = r));

    high_low : h:HS.mem -> ls:low{wf h ls} ->
               Lemma (to_low h ls (to_high h ls) == h);
    low_high : h:HS.mem -> ls:low{wf h ls} -> hs:high ->
               Lemma (to_high (to_low h ls hs) ls == hs); 
    low_low : h:HS.mem -> ls:low{wf h ls} -> hs1:high -> hs2:high ->
              Lemma (to_low h ls hs2 == to_low (to_low h ls hs1) ls hs2) }


instance tuple_lens : state_lens lstate state = 
  { wf = well_formed; 
    to_low = state_as_lstate;
    to_high = lstate_as_state;
    to_low' = admit ();
    to_high' = admit ();
    high_low = state_as_lstate_get_put;
    low_high = state_as_lstate_put_get;
    low_low = state_as_lstate_put_put; } 

(* WPs of high computations *)
type hwp state a = state -> (a * state -> Type) -> GTot Type

let monotonic #state #a (wp:hwp state a) =
  forall p1 p2 s. {:pattern wp s p1; wp s p2}
    (forall x.{:pattern (p1 x) \/ (p2 x)} p1 x ==> p2 x) ==>
    wp s p1 ==>
    wp s p2

type hwp_mon state 'a = (wp:hwp state 'a{monotonic wp})

(* High compuations *)
type high state a (wp : hwp_mon state a) = s0:state -> PURE (a * state) (wp s0)

(* Low computations *)
type low lstate hstate (#p: state_lens lstate hstate)
         (a:Type) (wp : hwp_mon hstate a) (c : high hstate a wp) =
         ls:lstate ->
         Stack a
           (requires (fun h -> wf #_ #_ #p h ls /\ (let s0 = to_high #_ #_ #p h ls in wp s0 (fun _ -> True))))
           (ensures  (fun h r h' ->
                       wf h' ls /\
                      (let s0 = to_high #_ #_ #p h ls in
                       let (x, s1) = c s0 in
                       h' == to_low #_ #_ #p h ls s1 /\ x == r )))

let run_high #hstate #a #wp (c:high hstate a wp) (s0:_{wp s0 (fun _ -> True)}) : (a * hstate) = c s0

// Lifting of high programs to low programs
let morph lstate hstate (#p: state_lens lstate hstate)
           (a:Type) (wp : hwp_mon hstate a) (c : high hstate a wp) : low lstate hstate #p a wp c =
  fun ls ->
    let hs = to_high' #_ #_ #p ls in 
    let h = ST.get () in
    assert (to_high #_ #_ #p h ls == hs);
    let (x, hs') = run_high c hs in
    to_low' #_ #_ #p ls hs'; x
