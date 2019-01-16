module FibState 

open Lens
open FStar.HyperStack
open FStar.HyperStack.ST
open LowStar.Buffer
open LowStar.BufferOps
open LowStar.Modifies
open Mem_eq
open Relations
open FStar.UInt32

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

reifiable reflectable total new_effect FIB = HIGH_h state 

// TODO : Can we define the Hoare version of the HIGH_h effect before instantiaton?
effect Fib (a:Type) (pre : hpre #state) (post : hpost #state a) = FIB a (as_wp pre post)


// for combinator. Annoyingly we can't seem to define this for the general, uninstantiated effect.
// TODO define it as reflect for_elab
let rec for (inv : state -> int -> Type0)
            (f : (i:int) -> Fib unit (requires (fun h0 -> inv h0 i))
                                  (ensures (fun h0 _ h1 -> inv h1 (i + 1)))) 
            (lo : int) (hi : int{lo <= hi}) 
: Fib unit (requires (fun h0 -> inv h0 lo))
           (ensures (fun h0 _ h1 -> inv h1 hi)) (decreases (hi - lo)) = 
 FIB?.reflect (for_elab inv (fun i -> reify (f i)) lo hi)


(* Other lenses *)

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

instance fib_commutes i : commutes fib_lens (focus_i i) (fib_lens_i i) = 
 { get_eq = (fun h ls -> ());
   put_eq = admit () }


let get_i (i : nat) : FIB mint (read_comp_wp #state #mint (focus_i i)) = 
  FIB?.reflect (read_comp #state #mint (focus_i i) ())
  // Lens.get #state #mint #(focus_i i) (FIB?.get ())

let put_i (i : nat) (m : mint) : FIB unit (write_comp_wp #state #mint (focus_i i) m) = 
  FIB?.reflect (write_comp #state #mint (focus_i i) m)
  // let s = FIB?.get () in
  // FIB?.put (Lens.put #state #mint #(focus_i i) s m)

let lget_i (i : nat) : low mint (read_comp_wp #state #mint (focus_i i)) 
                              (read_comp #state #mint (focus_i i) ()) =
  lread_comp #_ #fib_st #_ #fib_lens #mint #(focus_i i) (fib_lens_i i) #(fib_commutes i) ()
  
let lput_i (i : nat) (m : mint) : low unit (write_comp_wp #state #mint (focus_i i) m)
                                         (write_comp #state #mint (focus_i i) m)= 
  lwrite_comp #_ #fib_st #_ #fib_lens #mint #(focus_i i) (fib_lens_i i) #(fib_commutes i) m
    


(* *********** Fibonacci Example ************ *)

(* Purely functional spec *)
let rec fib (n : int) : Tot mint (decreases n) = 
  if n <= 0 then 0ul
  else if n = 1 then 1ul
  else 
    let f1 : mint = fib (n - 1) in
    let f2 : mint = fib (n - 2) in 
    f1 +%^ f2

(* Loop invariant *)
let inv (s : state) (i:int) = i >= 1 /\ (fst s = fib (i - 1) /\ snd s = fib i)


let shift i : Fib unit (fun s0 -> inv s0 i)
                       (fun s0 () s1 -> inv s1 (i + 1)) = 
    let x0 = get_i 0 in
    let x1 = get_i 1 in
    let _  = put_i 0 x1 in 
    let _  = put_i 1 (x0 +%^ x1) in
    ()


let fib_fast n : Fib mint (fun s0 -> True) (fun s0 r s1 -> r = fib n) = 
  if (n <= 0) then 0ul
  else 
    begin 
      put_i 0 0ul; // 0 has fib 0
      put_i 1 1ul; // 1 has fib 1
      for inv shift 1 n;
      get_i 1
    end

(* 
let lshift i = 
    lbind (lget_i 0) (fun x0 ->
    lbind #_ #fib_st #_ #fib_lens #mint #unit (lget_i 1) (fun x1 ->
    lbind (lput_i 0 x1) (fun _ ->  
    lbind #_ #fib_st #_ #fib_lens #unit #unit (lput_i 1 (x0 +%^ x1)) (fun _ -> 
    lreturn ()))))
    
    ()
    
let low_fib n = 
  if (n <= 0) then 0ul
  else 
    begin 
      lput_i 0 0ul; // 0 has fib 0
      lput_i 1 1ul; // 1 has fib 1
      lfor inv shift 1 n;
      get_i 1
    end

let low_fib n : low_p #_ #fib_st #_ #fib_lens mint (fun s0 -> True) (fun s0 r s1 -> r = fib n) (reify (fib_fast n)) = 
  morph_p #_ #fib_st #_ #fib_lens mint (fun s0 -> True) (fun s0 r s1 -> r = fib n) 
    (reify (fib_fast n))
 
*)
