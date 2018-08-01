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




let lcomp_wp (a:Type) (wp : state -> (a * state -> Type) -> Type) (c : comp_wp a wp) = 
     (ls:lstate) ->
     Stack a
       (requires (fun h -> well_formed h ls))
       (ensures  (fun h r h' -> 
                    well_formed h' ls /\
                    modifies (loc_union (loc_buffer (fst ls)) (loc_buffer (snd ls))) h h' /\
                   
                    (let s0 = lstate_as_state h ls in 
                     wp s0 (fun _ -> True) /\
                     (let res = c s0 in
                     snd res == lstate_as_state h' ls /\ fst res == r)))) 

let lcomp_p (a:Type) pre post (c : comp_p a pre post) = 
    (ls:lstate) ->
    Stack a
      (requires (fun h -> well_formed h ls))
      (ensures  (fun h r h' -> 
                   well_formed h' ls /\
                   modifies (loc_union (loc_buffer (fst ls)) (loc_buffer (snd ls))) h h' /\
                     
                   (let s0 = lstate_as_state h ls in 
                     pre s0 /\
                     (let res = c s0 in
                     snd res == lstate_as_state h' ls /\ fst res == r)))) 


let reif (#a:Type) (wp:state -> (a * state -> Type) -> Type) (c : unit -> HIGH a wp) : 
  comp_wp a wp  = reify (c ())


let lcomp_r (a:Type) (wp:state -> (a * state -> Type) -> Type) (c : unit -> HIGH a wp) = 
  (ls:lstate) ->
    Stack a
      (requires (fun h -> well_formed h ls))
      (ensures  (fun h r h' -> 
                   well_formed h' ls /\
                   modifies (loc_union (loc_buffer (fst ls)) (loc_buffer (snd ls))) h h' /\
                   (let s0 = lstate_as_state h ls in 
                    wp s0 (fun _ -> True) /\
                    (let res = reif wp c s0 in
                     // let res = reify (c ()) s0 in XXX using reify directly fails
                     snd res == lstate_as_state h' ls /\ fst res == r))))


(* DSL for low computations *)

let lreturn (#a:Type) (x:a) : lcomp_wp a (return_wp x) (hreturn' x) = fun ls -> x

let lbind (#a:Type) (#b:Type) #wp1 #wp2 (#c1:comp_wp a wp1) (#c2:(x:a -> comp_wp b (wp2 x))) 
    (m : lcomp_wp a wp1 c1) (f : (x:a) -> lcomp_wp b (wp2 x) (c2 x)) : 
    lcomp_wp b (bind_wp wp1 wp2) (hbind' c1 c2) = 
    fun s -> let a = m s in f a s
