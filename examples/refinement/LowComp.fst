module LowComp

module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module U32 = FStar.UInt32

open HighComp
open FStar.HyperStack
open FStar.HyperStack.ST 
open LowStar.Buffer  
open LowStar.BufferOps
open LowStar.Modifies


type bref = b:B.buffer mint { B.length b = 1 } // XXX pointers already exist

type lstate = bref * bref 

val well_formed : HS.mem -> lstate -> GTot Type0
let well_formed h = fun (b1, b2) -> live h b1 /\ live h b2 /\ disjoint b1 b2

val lstate_as_state : HS.mem -> lstate -> GTot state
let lstate_as_state h  = fun (b1, b2) -> (B.get h b1 0, B.get h b2 0)



// works
type lcomp 'a (c : comp 'a) = 
    (ls:lstate) ->
    Stack 'a
      (requires (fun h -> well_formed h ls))
      (ensures  (fun h r h' -> 
                   well_formed h' ls /\
                   modifies (loc_union (loc_buffer (fst ls)) (loc_buffer (snd ls))) h h' /\
                   (let s0 = lstate_as_state h ls in 
                    let (res : 'a * state) = c s0 in
                    let s1 = lstate_as_state h' ls in
                    snd res == s1 /\ fst res == r )))


// works with trial post
let lcomp_wp1 (a:Type) (wp : state -> (a * state -> Type) -> Type) (c : comp_wp a wp) = 
     (ls:lstate) ->
     Stack a
       (requires (fun h -> well_formed h ls))
       (ensures  (fun h r h' -> 
                    well_formed h' ls /\
                    modifies (loc_union (loc_buffer (fst ls)) (loc_buffer (snd ls))) h h'))


// Assertion failed ..
let lcomp_wp2 (a:Type) (wp : state -> (a * state -> Type) -> Type) (c : comp_wp a wp) = 
     (ls:lstate) ->
     Stack a
       (requires (fun h -> well_formed h ls))
       (ensures  (fun h r h' -> 
                    well_formed h' ls /\
                    modifies (loc_union (loc_buffer (fst ls)) (loc_buffer (snd ls))) h h' /\
                    (let s0 = lstate_as_state h ls in 
                     let s1 = lstate_as_state h' ls in
                     let res = c s0 in True )))
                     // wp s0 (fun _ -> True) )))
                     // snd res == s1 /\ fst res == r 


