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

module HS = FStar.HyperStack
module H = HighComp
module L = LowComp 


(* Standard lens class *)
class lens a b = 
  { put : a -> b -> a; 
    get : a -> b;
    get_put : x:a -> Lemma (put x (get x) == x);
    put_get : x:a -> y:b -> Lemma (get (put x y) == y); 
    put_put : x:a -> y1:b -> y2:b -> Lemma (put (put x y1) y2 == put x y2) }

(* A more specific one for our case *)
class state_lens low high = 
  { wf : HS.mem -> low -> Type;
    to_low : h:HS.mem -> ls:low{wf h ls} -> high -> GTot (h':HS.mem{wf h' ls}); 
    to_high : HS.mem -> low -> GTot high; 
    high_low : h:HS.mem -> ls:low{wf h ls} ->
               Lemma (to_low h ls (to_high h ls) == h);
    low_high : h:HS.mem -> ls:low{wf h ls} -> hs:high ->
               Lemma (to_high (to_low h ls hs) ls == hs); 
    low_low : h:HS.mem -> ls:low{wf h ls} -> hs1:high -> hs2:high ->
              Lemma (to_low h ls hs2 == to_low (to_low h ls hs1) ls hs2) }


instance tuple_lens : state_lens L.lstate H.state = 
  { wf = well_formed; 
    to_low = state_as_lstate;
    to_high = lstate_as_state;
    high_low = state_as_lstate_get_put;
    low_high = state_as_lstate_put_get;
    low_low = state_as_lstate_put_put; } 




