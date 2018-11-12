module Simple_state

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


// Low-level implementation
type bref = b:B.buffer mint { B.length b = 1 } 

val heap_as_state : HS.mem -> bref -> bref -> GTot state
let heap_as_state h b1 b2 : GTot state =
  (B.get h b1 0, B.get h b2 0)

val low_swap_and_sum :
  b1:bref -> b2:bref -> 
  Stack int 
    (requires (fun h -> live h b1 /\ live h b2 /\ disjoint b1 b2))
    (ensures  (fun h sum h' -> 
                 live h' b1 /\ live h' b2 /\ disjoint b1 b2 /\
                 modifies (loc_union (loc_buffer b1) (loc_buffer b2)) h h' /\
                 (let s1 = heap_as_state h b1 b2 in 
                  let res = swap_and_sum () s1 in   
                  snd res == heap_as_state h' b1 b2 /\ fst res == sum)))
let low_swap_and_sum b1 b2 =
  let tmp = b1.(0ul) in 
  b1.(0ul) <- b2.(0ul);
  b2.(0ul) <- tmp;
  U32.v b1.(0ul) + U32.v b2.(0ul)
