module LowComp

open HighComp
open FStar.HyperStack
open FStar.HyperStack.ST
open LowStar.Buffer
open LowStar.BufferOps
open LowStar.Modifies
open Mem_eq

module H = FStar.Monotonic.Heap
module B = LowStar.Buffer
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module U32 = FStar.UInt32
module Map = FStar.Map
module M = LowStar.Modifies


type lstate = pointer mint * pointer mint

val well_formed : HS.mem -> lstate -> GTot Type0
let well_formed h = fun (r1, r2) -> live h r1 /\ live h r2 /\ disjoint r1 r2

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

(** Lens lows *)

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


// Low type variations

type lcomp 'a (c : comp 'a) =
    (ls:lstate) ->
    Stack 'a
      (requires (fun h -> well_formed h ls))
      (ensures  (fun h r h' ->
                   well_formed h' ls /\
                   //modifies (loc_union (loc_buffer (fst ls)) (loc_buffer (snd ls))) h h' /\
                   (let s0 = lstate_as_state h ls in
                    let (x, s1) = c s0 in
                    Map.equal (get_hmap h') (get_hmap (state_as_lstate h ls s1)) /\ x == r )))



let lcomp_wp1 (a:Type) (wp : hwp a{monotonic wp}) (c : comp_wp a wp) =
     ls:lstate ->
     Stack a
       (requires (fun h -> well_formed h ls /\ (let s0 = lstate_as_state h ls in wp s0 (fun _ -> True))))
       (ensures  (fun h r h' ->
                    well_formed h' ls /\
                    (let s0 = lstate_as_state h ls in
                     let (x, s1) = c s0 in 
                     h' == state_as_lstate h ls s1 /\ x == r )))

let lcomp_wp2 (a:Type) (wp : hwp a{monotonic wp}) (c : comp_wp a wp) =
   ls:lstate ->
    Stack a
      (requires (fun h -> well_formed h ls /\ (let s0 = lstate_as_state h ls in wp s0 (fun _ -> True))))
      (ensures  (fun h r h' ->
                   well_formed h' ls /\
                   (let s0 = lstate_as_state h ls in
                    let (x, s1) = c s0 in 
                     h' == state_as_lstate h ls s1 /\ x == r )))



(** DSL for low computations *)

let lreturn (#a:Type) (x:a) : lcomp_wp1 a (return_wp x) (return_elab x) = 
  fun (b1, b2) -> 
    let h0 = ST.get () in 
    let p1 = get_upd_eq h0 b1 0 (get h0 b1 0) in
    let p2 = get_upd_eq h0 b2 0 (get h0 b2 0) in
    x

(* TODO prove this spec *)
val upd : b:pointer mint -> v:mint -> 
           Stack unit (requires (fun h0 -> live h0 b)) (ensures (fun h0 _ h1 -> live h0 b /\ h1 == g_upd b 0 v h0))
[@expect_failure]
let upd b v = b.(0ul) <- v 
                     
val lwrite : i:nat{ i < 2 } -> v:mint -> lcomp_wp1 unit (write_wp i v) (hwrite' i v)
let lwrite i v (ls:lstate) =
  let (b1, b2) = ls in
  if i = 0 then 
      (* * ********************************************* *)
      let h0 = ST.get () in
      let p = 
        let p = g_upd_preserves_live h0 b1 b2 v in // Shows: live h1 b
        let g = get_upd_other h0 b1 b2 v (get h0 b2 0) in // Shows: get (g_upd b1 v h0) b2 = get h0 b2 
        assert (get (g_upd b1 0 v h0) b2 0 == get h0 b2 0);
        get_upd_eq (g_upd b1 0 v h0) b2 0 (get h0 b2 0) // Shows: g_upd b2 0 (get h0 b2 0) h1 == h1
      in
      assert (g_upd b2 0 (get h0 b2 0) (g_upd b1 0 v h0) == g_upd b1 0 v h0);
      (* ********************************************* *)
      
      b1.(0ul) <- v;
      
      (* * ********************************************* *)
      let h1 = ST.get () in 
      // Just sanity
      // XXX trying to bind something analogous in lbind doesn't work 
      let x, s1 = hwrite' 0 v (lstate_as_state h0 (b1, b2)) in
      assert (x == ());

      assume (h1 == g_upd b1 0 v h0) // TODO stronger type for get
      (* ********************************************* *)
    else 
      (* * ********************************************* *)
      let h0 = ST.get () in
      let p1 = get_upd_eq h0 b1 0 (get h0 b1 0) in
      assert (g_upd b2 0 v (g_upd b1 0 (get h0 b1 0) h0) == g_upd b2 0 v h0);
      (* ********************************************* *)

      b2.(0ul) <- v;

      (* * ********************************************* *)
      let h1 = ST.get () in 
      assume (h1 == g_upd b2 0 v h0) // TODO stronger type for get
      (* ********************************************* *)


val lread : i:nat{ i < 2 } -> lcomp_wp1 mint (read_wp i) (hread' i)
let lread i = fun (b1, b2) -> 
  let h0 = ST.get () in 
  let p1 = get_upd_eq h0 b1 0 (get h0 b1 0) in
  let p2 = get_upd_eq h0 b2 0 (get h0 b2 0) in
  if i = 0 then 
     b1.(0ul) 
  else 
    b2.(0ul)

let z = HIGH?.wp int

//Rather than get into trouble with applying `c` directly in a context
//where we have to think about the VC of the continuation, 
//let's factor this into a `run`, which makes things a lot more predictable
let run_high #a #wp (c:comp_wp a wp) (s0:_{wp s0 (fun _ -> True)}) : (a * state) = c s0


let lbind (#a:Type) (#b:Type)
  (#wp1: hwp a{monotonic wp1}) (#fwp2 : (a -> (wp2:hwp b{monotonic wp2}))) 
  (#c1:comp_wp a wp1) (#c2:(x:a -> comp_wp b (fwp2 x)))
  (m: lcomp_wp1 a wp1 c1) (f: (x:a) -> lcomp_wp1 b (fwp2 x) (c2 x)) :
  lcomp_wp1 b (bind_wp wp1 fwp2) (bind_elab c1 c2) =
  fun ls ->
    let (b1, b2) = ls in
    assert (HighComp.monotonic wp1);
    assert (forall x. HighComp.monotonic (fwp2 x));     
    assert (monotonic (bind_wp wp1 fwp2));

    (* ********************************************* *)
    
    let h0 = ST.get () in  // Initial heap

    (* ********************************************* *)
    let x_a = m ls in  //Run the first compuation
 
    
    let h1 = ST.get () in // Intermediate heap
    (* ********************************************* *)

    let high : Ghost.erased _ = 
      //In this block, we run the high computation
      //in ghost code and remember its intermediate states and result
      let s0 = lstate_as_state h0 ls in
      let x, s1 = run_high c1 s0 in
      assert (x == x_a);
      assert (h1 == state_as_lstate h0 ls s1);
      state_as_lstate_put_get h0 ls s1; //Get-Put: 1st lens law
      assert (lstate_as_state h1 ls == s1); //this assertion is key to running `f x_a ls` below
      let y, s2 = run_high (c2 x) s1 in
      assert (s2 == snd (run_high #b #(bind_wp wp1 fwp2) (bind_elab c1 c2) s0));
      Ghost.hide (s0, (x, s1), (y, s2))
    in

    (* ********************************************* *)
    let y_b = f x_a ls in
    let h2 = ST.get () in // final heap
    (* ********************************************* *)
    let _ : unit = 
      //In this block, we unpack the memoized result from earlier
      //and relate those values to the result and final heap
      let s0, (x, s1), (y, s2) = Ghost.reveal high in
      assert (x == x_a);
      assert (y == y_b);
      assert (h2 == state_as_lstate h1 ls s2);
      assert (h1 == state_as_lstate h0 ls s1);
      let p = state_as_lstate_put_put h0 ls s1 s2 in 
      assert (state_as_lstate h0 ls s2 == state_as_lstate (state_as_lstate h0 ls s1) ls s2);
      assert (state_as_lstate h0 ls s2 == state_as_lstate h1 ls s2)
    in
    y_b



let lite (#a:Type) (b:bool)
         (#wp1 : hwp_mon a) (#c1:comp_wp a wp1) (lc1: lcomp_wp1 a wp1 c1)
         (#wp2 : hwp_mon a) (#c2:comp_wp a wp2) (lc2: lcomp_wp1 a wp2 c2) : lcomp_wp1 a (ite_wp b wp1 wp2) (ite_elab b c1 c2) =
  fun ls -> if b then lc1 ls else lc2 ls



// Versions of the DSL with reif in spec

val lwrite' : i:nat{ i < 2 } -> v:mint -> lcomp_wp1 unit (write_wp i v) (reify (HIGH?.put i v))
let lwrite' i v ls =
  let (b1, b2) = ls in
  if i = 0 then 
     (* * ********************************************* *)
     let h0 = ST.get () in
     let p = 
       let p = g_upd_preserves_live h0 b1 b2 v in // Shows: live h1 b
       let g = get_upd_other h0 b1 b2 v (get h0 b2 0) in // Shows: get (g_upd b1 v h0) b2 = get h0 b2 
       assert (get (g_upd b1 0 v h0) b2 0 == get h0 b2 0);
        get_upd_eq (g_upd b1 0 v h0) b2 0 (get h0 b2 0) // Shows: g_upd b2 0 (get h0 b2 0) h1 == h1
     in
     assert (g_upd b2 0 (get h0 b2 0) (g_upd b1 0 v h0) == g_upd b1 0 v h0);
     (* ********************************************* *)
      
     b1.(0ul) <- v;
     
     (* * ********************************************* *)
     let h1 = ST.get () in 
     // Just sanity
     // XXX trying to bind something analogous in lbind doesn't work 
     let x, s1 = hwrite' 0 v (lstate_as_state h0 (b1, b2)) in
     assert (x == ());
     
     assume (h1 == g_upd b1 0 v h0) // TODO stronger type for get
     (* ********************************************* *)
   else 
     (* * ********************************************* *)
     let h0 = ST.get () in
     let p1 = get_upd_eq h0 b1 0 (get h0 b1 0) in
     assert (g_upd b2 0 v (g_upd b1 0 (get h0 b1 0) h0) == g_upd b2 0 v h0);
     (* ********************************************* *)
     
     b2.(0ul) <- v;
     
     (* * ********************************************* *)
     let h1 = ST.get () in 
     assume (h1 == g_upd b2 0 v h0) // TODO stronger type for get
     (* ********************************************* *)


val lread' : i:nat{ i < 2 } -> lcomp_wp1 mint (read_wp i) (reify (HIGH?.get i))
let lread' i = fun (b1, b2) -> 
  let h0 = ST.get () in 
  let p1 = get_upd_eq h0 b1 0 (get h0 b1 0) in
  let p2 = get_upd_eq h0 b2 0 (get h0 b2 0) in
  if i = 0 then b1.(0ul) else b2.(0ul)


let lcomp_respects_h_eq (a : Type) (wp1 : hwp a{monotonic wp1}) (wp2 : hwp a{monotonic wp2}) (hc1 : comp_wp a wp1) (hc2 : comp_wp a wp2)  
  (lc : lcomp_wp1 a wp1 hc1) (p : h_eq wp1 wp2 hc1 hc2) : lcomp_wp2 a wp2 hc2 = // 660 requires the lcomp_wp'
  lc 
  


