module FibState 

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

type mint = U32.t
type state = mint * mint

type lstate = pointer mint * pointer mint

val well_formed : HS.mem -> lstate -> GTot Type0
let well_formed h = fun (r1, r2) -> live h r1 /\ live h r2 /\ disjoint r1 r2

instance fib_st : low_state lstate = { wf = well_formed } 

// To and from high- and low-level state coercions

val lstate_as_state : HS.mem -> lstate -> GTot state
let lstate_as_state h  = fun (b1, b2) -> (B.get h b1 0, B.get h b2 0)

val state_as_lstate : h:HS.mem -> ls:lstate{well_formed h ls} -> state -> GTot (h':HS.mem{well_formed h' ls})
let state_as_lstate h =
  fun (r1, r2) (v1, v2) ->
    let h' = g_upd r1 0 v1 h in
    let p = g_upd_preserves_live h r1 r2 v1 in
    let h'' = g_upd r2 0 v2 h' in
    let p' = g_upd_preserves_live h' r2 r1 v2 in
    h''

(** Lens laws *)

val state_as_lstate_put_get : h:HS.mem -> ls:lstate{well_formed h ls} -> bs:state ->
   Lemma (lstate_as_state (state_as_lstate h ls bs) ls == bs)
let state_as_lstate_put_get h ls bs =
  let (b1, b2) = ls in
  let (s1, s2) = bs in
  let h1 = g_upd b1 0 s1 h in
  let l1 = g_upd_preserves_live h b1 b2 s1 in
  let h2 = g_upd b2 0 s2 h1 in
  let l2 = g_upd_preserves_live h1 b2 b1 s2 in

  let p1 = get_upd_same h b1 s1 in
  assert (get h1 b1 0 == s1);
  let p1' = get_upd_other h1 b2 b1 s2 s1 in
  assert (get h2 b1 0 == get h1 b1 0);
  let p2 = get_upd_same h1 b2 s2 in
  assert (get h2 b2 0 == s2);
  ()

val state_as_lstate_get_put : h:HS.mem -> ls:lstate{well_formed h ls} ->
    Lemma (state_as_lstate h ls (lstate_as_state h ls) == h)
let state_as_lstate_get_put h ls = 
    let (b1, b2) = ls in
    let s1 = B.get h b1 0 in 
    let s2 = B.get h b2 0 in 
    
    let h1 = g_upd b1 0 s1 h in
    let l1 = g_upd_preserves_live h b1 b2 s1 in
    let h2 = g_upd b2 0 s2 h1 in
    let l2 = g_upd_preserves_live h1 b2 b1 s2 in

    let p1 = get_upd_eq h b1 0 s1 in
    assert (h1 == h);
    let p2 = get_upd_eq h b2 0 s2 in 
    assert (h2 == h);
    ()

val state_as_lstate_put_put : h:HS.mem -> ls:lstate{well_formed h ls} -> bs1:state -> bs2:state ->
    Lemma (state_as_lstate h ls bs2 == state_as_lstate (state_as_lstate h ls bs1) ls bs2)
let state_as_lstate_put_put h ls bs1 bs2 =
  let (b1, b2) = ls in
  let (s1, s2) = bs1 in
  let (s1', s2') = bs2 in

  let h1 = g_upd b1 0 s1 h in
  let l1 = g_upd_preserves_live h b1 b2 s1 in
  let h2 = g_upd b2 0 s2 h1 in
  let l2 = g_upd_preserves_live h1 b2 b1 s2 in

  let h1' = g_upd b1 0 s1' h2 in
  let l1' = g_upd_preserves_live h2 b1 b2 s1' in
  let h2' = g_upd b2 0 s2' h1' in
  let l2' = g_upd_preserves_live h1' b2 b1 s2' in

  let p1 = upd_com h1 b1 b2 s1' s2 in
  let lv1 = g_upd_preserves_live h1 b1 b2 s1' in
  assert (h1' == g_upd b2 0 s2 (g_upd b1 0 s1' h1));
  let p2 = upd_upd_eq h b1 0 s1 s1' in
  let lv2 = g_upd_preserves_live h b1 b2 s1' in
  assert (h1' == g_upd b2 0 s2 (g_upd b1 0 s1' h));
  let p3 = upd_upd_eq (g_upd b1 0 s1' h) b2 0 s2 s2' in
  let lv3 = g_upd_preserves_live (g_upd b1 0 s1' h) b2 b1 s2' in
  assert (h2' == g_upd b2 0 s2' (g_upd b1 0 s1' h));
  ()


// Effectful lenses 

let state_as_lstate' (ls:lstate) (hs:state) :
                     Stack unit (requires (fun h -> wf #_ #fib_st h ls)) 
                                (ensures (fun h r h' -> wf h' ls /\ 
                                                     state_as_lstate h ls hs == h')) = 
  let (b1, b2) = ls in
  let (s1, s2) = hs in 
  let h = ST.get () in

  b1.(0ul) <- s1;
  
  let h' = ST.get () in
  let p = g_upd_preserves_live h b1 b2 s1 in

  b2.(0ul) <- s2;

  let h'' = ST.get () in
  let p = g_upd_preserves_live h' b2 b1 s2 in
  assume (h'' == g_upd b2 0 s2 (g_upd b1 0 s1 h));
  ()

let lstate_as_state' (ls:lstate) :
  Stack state (requires (fun h -> wf h ls)) 
               (ensures (fun h r h' -> h == h' /\ lstate_as_state h ls == r)) =
  let (b1, b2) = ls in
  (b1.(0ul), b2.(0ul))


instance fib_lens : state_lens lstate #fib_st state = 
 { to_low = state_as_lstate;
   to_high = lstate_as_state;
   to_low' = state_as_lstate';
   to_high' = lstate_as_state';
   high_low = state_as_lstate_get_put;
   low_high = state_as_lstate_put_get;
   low_low = state_as_lstate_put_put; } 

new_effect FIB = HIGH_h state 

instance focus_i (i:nat) : lens state mint = 
{ put = (fun s m -> if i = 0 then (m, snd s) else (fst s, m));
  get = (fun s -> if i = 0 then fst s else snd s);
  get_put = (fun x -> ());
  put_get = (fun x y -> ());
  put_put = (fun x y1 y2 -> ());  
}


(* This is annoying but right know we have to declare this instance for lread/lrwrite *)

val read_i (i : nat) : h:HS.mem -> ls:lstate -> GTot mint
let read_i i h = fun (b1, b2) -> if (i = 0) then B.get h b1 0 else B.get h b2 0

val write_i (i : nat) : h:HS.mem -> ls:lstate{well_formed h ls} -> mint -> GTot (h':HS.mem{well_formed h' ls})
let write_i i h = 
  fun (r1, r2) m -> 
   if (i = 0) then 
     let h' = g_upd r1 0 m h in
     let p = g_upd_preserves_live h r1 r2 m in
     h'
   else 
     let h' = g_upd r2 0 m h in
     let p = g_upd_preserves_live h r2 r1 m in
     h'

(** Lens laws *)

val put_get_i : i:nat -> h:HS.mem -> ls:lstate{well_formed h ls} -> m:mint ->
   Lemma (read_i i (write_i i h ls m) ls == m)
let put_get_i i h ls m =
  let (b1, b2) = if i = 0 then ls else (snd ls, fst ls) in
  let h1 = g_upd b1 0 m h in
  let l1 = g_upd_preserves_live h b1 b2 m in
  let p1 = get_upd_same h b1 m in
  assert (get h1 b1 0 == m)
  
  
val get_put_i : i:nat -> h:HS.mem -> ls:lstate{wf h ls} ->
    Lemma (write_i i h ls (read_i i h ls) == h)
let get_put_i i h ls = 
  let (b1, b2) = if i = 0 then ls else (snd ls, fst ls) in
  let s1 = B.get h b1 0 in 
  let h1 = g_upd b1 0 s1 h in
  let l1 = g_upd_preserves_live h b1 b2 s1 in
  let p1 = get_upd_eq h b1 0 s1 in
  assert (h1 == h)


val put_put_i : i:nat -> h:HS.mem -> ls:lstate{wf h ls} -> m1:mint -> m2:mint ->
    Lemma (write_i i h ls m2 == write_i i (write_i i h ls m1) ls m2)
let put_put_i i h ls m1 m2 =
  let (b1, b2) = if i = 0 then ls else (snd ls, fst ls) in 
  let h1 = g_upd b1 0 m1 h in
  let l1 = g_upd_preserves_live h b1 b2 m1 in 
  let h2 = g_upd b1 0 m2 h1 in
  let l2 = g_upd_preserves_live h1 b1 b2 m2 in

  let h2' = g_upd b1 0 m2 h in
  let l2' = g_upd_preserves_live h b1 b2 m2 in
    
  let p2 = upd_upd_eq h b1 0 m1 m2 in ()
  

// Effectful lenses 

let write_i' (i:nat) (ls:lstate) (m:mint) :
             Stack unit (requires (fun h -> wf #_ #fib_st h ls)) 
                        (ensures (fun h r h' -> wf h' ls /\ write_i i h ls m == h')) = 
  let (b1, b2) = if i = 0 then ls else (snd ls, fst ls) in 
  let h = ST.get () in
  
  b1.(0ul) <- m;
  
  let h' = ST.get () in
  let p = g_upd_preserves_live h b1 b2 m in
  assume (h' == g_upd b1 0 m h);
  ()

let read_i' (i:nat) (ls:lstate) :
  Stack mint (requires (fun h -> wf h ls)) 
             (ensures (fun h r h' -> h == h' /\ read_i i h ls == r)) =
  let (b1, b2) = if i = 0 then ls else (snd ls, fst ls) in 
  b1.(0ul)


instance fib_lens_i (i : nat) : state_lens lstate #fib_st mint = 
{ to_low = write_i i;
  to_high = read_i i;
  to_low' = write_i' i;
  to_high' = read_i' i;
  high_low = get_put_i i;
  low_high = put_get_i i;
  low_low =  put_put_i i 
  } 

// instance fib_commutes (i : nat) : commutes f

//  (* Shorthand for actions *) 
// let get (i : nat) () : FIB mint =  
// let put (i : nat) (m : mint) : FIB unit =

