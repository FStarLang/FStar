module Simple_state_v2

//open FStar.Integers

module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module U32 = FStar.UInt32

open FStar.HyperStack
open FStar.HyperStack.ST 
open LowStar.Buffer  
open LowStar.BufferOps
open LowStar.Modifies

// High-level state
type mint = U32.t
type state = mint * mint
type comp 'a = state -> 'a * state


val return : 'a -> comp 'a
let return (x : 'a) = fun s -> (x, s)

val bind : comp 'a -> ('a -> comp 'b) -> comp 'b
let bind (m : comp 'a) (f : 'a -> comp 'b) = 
  fun s -> let (a, s1) = m s in f a s1
  

val read : i:nat{ i < 2 } -> comp mint
let read i = 
  fun s -> if i = 0 then (fst s, s) 
        else (snd s, s)

val write : i:nat{ i < 2 } -> v:mint -> comp unit
let write i v = 
  fun s -> if i = 0 then ((), (v, snd s))
        else ((), (fst s, v))


// swap_and_sum spec
val swap_and_sum : unit -> comp int
let swap_and_sum () = 
  bind (read 0) (fun x0 -> 
  bind (read 1) (fun x1 -> 
  bind (write 0 x1) (fun () -> 
  bind (write 1 x0) (fun () ->
  return (U32.v x0 + U32.v x1)))))


// Low-level implementation writen in a "monadic" stype

type bref = b:B.buffer mint { B.length b = 1 } // XXX pointers already exist

type lstate = bref * bref 


val well_formed : HS.mem -> lstate -> GTot Type0
let well_formed h = fun (b1, b2) -> live h b1 /\ live h b2 /\ disjoint b1 b2

val lstate_as_state : HS.mem -> lstate -> GTot state
let lstate_as_state h  = fun (b1, b2) -> (B.get h b1 0, B.get h b2 0)

type low_type 'a (c : comp 'a) = 
  (ls:lstate) ->
  Stack 'a 
    (requires (fun h -> well_formed h ls))
    (ensures  (fun h r h' -> 
                 well_formed h' ls /\
                 modifies (loc_union (loc_buffer (fst ls)) (loc_buffer (snd ls))) h h' /\
                 (let s1 = lstate_as_state h ls in 
                  let res = c s1 in   
                  snd res == lstate_as_state h' ls /\ fst res == r)))

val lwrite : i:nat{ i < 2 } -> v:mint -> low_type unit (write i v)
let lwrite i v = fun (b1, b2) -> if i = 0 then b1.(0ul) <- v else b2.(0ul) <- v

val lread : i:nat{ i < 2 } -> low_type mint (read i)
let lread i = fun (b1, b2) -> if i = 0 then b1.(0ul) else b2.(0ul)


val low_swap_and_sum : low_type int (swap_and_sum ())
let low_swap_and_sum = fun ls ->
  let (v1 : mint) = lread 0 ls in 
  let (v2 : mint) = lread 1 ls in
  lwrite 0 v2 ls;
  lwrite 1 v1 ls;
  U32.v v1 + U32.v v2
 
