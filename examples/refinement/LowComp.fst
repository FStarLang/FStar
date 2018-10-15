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


(** ** Low computations and their WPs **)

let lcomp_wp (a:Type) (wp : hwp_mon a) (c : comp_wp a wp) =
  ls:lstate ->
  Stack a
     (requires (fun h -> well_formed h ls /\ (let s0 = lstate_as_state h ls in wp s0 (fun _ -> True))))
     (ensures  (fun h r h' ->
                  well_formed h' ls /\
                  (let s0 = lstate_as_state h ls in
                   let (x, s1) = c s0 in
                   h' == state_as_lstate h ls s1 /\ x == r )))

let lcomp (a : Type) pre post (c : comp_p a pre post) = 
  lcomp_wp a 
    (fun s0 p -> pre s0 /\ (forall r s1. post s0 r s1 ==> p (r, s1))) c

//Rather than get into trouble with applying `c` directly in a context
//where we have to think about the VC of the continuation,
//let's factor this into a `run`, which makes things a lot more predictable
let run_high #a #wp (c:comp_wp a wp) (s0:_{wp s0 (fun _ -> True)}) : (a * state) = c s0

type lwp a = lstate -> (mem -> (a * mem -> Type) -> Type)

let as_lwp #a #wp (c:comp_wp a wp) : lwp a =
    fun ls h0 post ->
      well_formed h0 ls /\
      (let s0 = lstate_as_state h0 ls in
       wp s0 (fun _ -> True) /\
       (let (x, s1) = c s0 in
        let h1 = state_as_lstate h0 ls s1 in post (x, h1)))

let sat #a (wp:lwp a) : Type = forall (h:HS.mem) (ls:lstate{well_formed h ls}). wp ls h (fun _ -> True)

let sat_as_lwp #a (wp:hwp a) : Type = forall (h:HS.mem) (ls:lstate{well_formed h ls}). wp (lstate_as_state h ls) (fun _ -> True)

let precise #a (wp:lwp a) =
  sat wp ==>
  (forall h0 (ls:lstate{well_formed h0 ls}).
     wp ls h0 (fun (r1, h1) ->
     wp ls h0 (fun (r2, h2) ->
     r1 == r2 /\ h1 == h2)))


(** ** Equality of low computations **)

let lwp_eq #a (wp1:lwp a) (wp2:lwp a) =
  precise wp1 /\
  precise wp2 /\
  (forall ls h0 post. wp1 ls h0 post <==> wp2 ls h0 post)

let l_eq #a (#wp1:hwp_mon a) (#c1:comp_wp a wp1) (lc1: lcomp_wp a wp1 c1)
         (#wp2:hwp_mon a) (#c2:comp_wp a wp2) (lc2 : lcomp_wp a wp2 c2) =
  lwp_eq (as_lwp c1) (as_lwp c2)

assume val l_eq_axiom : (#a:Type) -> (#wp1:hwp_mon a) -> (#c1:comp_wp a wp1) -> (lc1: lcomp_wp a wp1 c1) ->
                        (#wp2:hwp_mon a) -> (#c2:comp_wp a wp2) -> (lc2 : lcomp_wp a wp2 c2) ->
                        Lemma (requires (l_eq lc1 lc2)) (ensures (lc1 === lc2))

// Lifting of high programs to low programs
let morph (#a:Type) (wp:hwp_mon a) (c:comp_wp a wp) : lcomp_wp a wp c =
    fun (b1, b2) ->
      let s1 = b1.(0ul) in
      let s2 = b2.(0ul) in
      let h = ST.get () in
      assert (lstate_as_state h (b1, b2) == (s1, s2));
      let (x, (s1', s2')) = run_high c (s1, s2) in
      b1.(0ul) <- s1';
      let h' = ST.get () in
      let p = g_upd_preserves_live h b1 b2 s1' in
      assume (h' == g_upd b1 0 s1 h);
      b2.(0ul) <- s2';
      let h'' = ST.get () in
      let p = g_upd_preserves_live h' b2 b1 s2' in // Shows: live h1 b
      assume (h'' == g_upd b2 0 s2' (g_upd b1 0 s1' h));
      x

let morph_p  (#a : Type) (pre : hpre) (post : hpost a) (c : comp_p a pre post) : lcomp a pre post c =
  morph (as_wp pre post) c


(** ** DSL for low computations **)

let lreturn (#a:Type) (x:a) : lcomp_wp a (return_wp x) (return_elab x) =
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

val lwrite : i:nat{ i < 2 } -> v:mint -> lcomp_wp unit (write_wp i v) (hwrite_elab i v)
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
      let x, s1 = hwrite_elab 0 v (lstate_as_state h0 (b1, b2)) in
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


val lread : i:nat{ i < 2 } -> lcomp_wp mint (read_wp i) (hread_elab i)
let lread i = fun (b1, b2) ->
  let h0 = ST.get () in
  let p1 = get_upd_eq h0 b1 0 (get h0 b1 0) in
  let p2 = get_upd_eq h0 b2 0 (get h0 b2 0) in
  if i = 0 then
     b1.(0ul)
  else
    b2.(0ul)

let lbind (#a:Type) (#b:Type)
  (#wp1: hwp_mon a) (#fwp2 : (a -> hwp_mon b))
  (#c1:comp_wp a wp1) (#c2:(x:a -> comp_wp b (fwp2 x)))
  (m: lcomp_wp a wp1 c1) (f: (x:a) -> lcomp_wp b (fwp2 x) (c2 x)) :
  lcomp_wp b (bind_wp wp1 fwp2) (bind_elab c1 c2) =
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
         (#wp1 : hwp_mon a) (#c1:comp_wp a wp1) (lc1: lcomp_wp a wp1 c1)
         (#wp2 : hwp_mon a) (#c2:comp_wp a wp2) (lc2: lcomp_wp a wp2 c2) : lcomp_wp a (ite_wp b wp1 wp2) (ite_elab b c1 c2) =
  fun ls -> if b then lc1 ls else lc2 ls



let rec lfor (#wp : int -> hwp_mon unit) (#f : (i:int) -> comp_wp unit (wp i)) (lo : int) (hi : int{lo <= hi})
    (c : (z:int) -> lcomp_wp unit (wp z) (f z)) :
    Tot (lcomp_wp unit (for_wp wp lo hi) (for_elab #wp lo hi f)) (decreases (hi - lo)) =
  if lo = hi then (lreturn ())
  else (let (m : lcomp_wp unit (wp lo) (f lo)) = c lo in
        let c (u:unit) : lcomp_wp (unit) (for_wp wp (lo+1) hi) (for_elab #wp (lo + 1) hi f) =
          lfor #wp #f (lo + 1) hi c
        in
        let p = for_wp_unfold wp lo hi in
        assert (for_wp wp lo hi == bind_wp (wp lo) (fun _ -> for_wp wp (lo + 1) hi));
        let p' = for_elab_unfold #wp lo hi f in
        assert (for_elab #wp lo hi f ==
                (let (m : comp_wp unit (wp lo)) = f lo in
                 let cf (u:unit) : comp_wp (unit) (for_wp wp (lo+1) hi) = for_elab #wp (lo + 1) hi f in
                 let p = for_wp_unfold wp lo hi in
                 bind_elab m cf));
       lbind m c)


let rec lfor' (inv : state -> int -> Type0) (fh : (i:int) -> comp_p unit  (fun h0 -> inv h0 i) (fun h0 _ h1 -> inv h1 (i + 1)))
              (f : (i:int) -> lcomp unit (fun h0 -> inv h0 i)
                                      (fun h0 _ h1 -> inv h1 (i + 1)) (fh i)) 
              (lo : int) (hi : int{lo <= hi}) :
          Tot (lcomp unit (requires (fun h0 -> inv h0 lo))
                          (ensures (fun h0 _ h1 -> inv h1 hi))
                          (for_elab' inv fh lo hi)) (decreases (hi - lo)) = 
          if lo = hi then (lreturn ())
          else 
          begin 
            let k () = lfor' inv fh f (lo + 1) hi in 
            lbind (f lo) (fun _ -> 
            k ())
          end

(** The above should be translated to a C for loop. Propbably we should implement it with a Low* for combinator *)

// Versions of the DSL with reif in spec

val lwrite' : i:nat{ i < 2 } -> v:mint -> lcomp_wp unit (write_wp i v) (reify (HighComp.put_action i v))
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
     let x, s1 = hwrite_elab 0 v (lstate_as_state h0 (b1, b2)) in
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


val lread' : i:nat{ i < 2 } -> lcomp_wp mint (read_wp i) (reify (HighComp.get_action i))
let lread' i = fun (b1, b2) ->
  let h0 = ST.get () in
  let p1 = get_upd_eq h0 b1 0 (get h0 b1 0) in
  let p2 = get_upd_eq h0 b2 0 (get h0 b2 0) in
  if i = 0 then b1.(0ul) else b2.(0ul)


(** ** Equality properties *)


let lcast #a (#wp1 : hwp_mon a) (wp2: hwp_mon a{subsumes wp1 wp2}) (c : comp_wp a wp1) (l : lcomp_wp a wp1 c) : lcomp_wp a wp2 c = l

let as_lwp_precise (#a:Type) wp (c : comp_wp a wp) :
  Lemma
  (precise (as_lwp #a #wp c)) = ()

let h_eq_implies_l_eq (#a:Type) (wp1:hwp_mon a) (c1:comp_wp a wp1) (lc1:lcomp_wp a wp1 c1)
    (wp2:hwp_mon a) (c2:comp_wp a wp2) (lc2:lcomp_wp a wp2 c2) :
  Lemma (requires (h_eq wp1 wp2 c1 c2))
        (ensures (l_eq lc1 lc2)) = ()

let h_eq_refl (#a:Type) (wp:hwp_mon a) (c:comp_wp a wp) : Lemma (h_eq wp wp c c) = ()

let l_eq_refl (#a:Type) (wp:hwp_mon a) (c:comp_wp a wp) (l : lcomp_wp a wp c) :
  Lemma (l_eq l l) = ()

let lcomp_unique_inhabitant (#a:Type) (wp:hwp_mon a) (c:comp_wp a wp) (lc1 : lcomp_wp a wp c) (lc2 : lcomp_wp a wp c) :
  Lemma (l_eq lc1 lc2) = ()

let lcomp_respects_h_eq (a : Type)
                        (wp1 : hwp_mon a)
                        (wp2 : hwp_mon a)
                        (hc1 : comp_wp a wp1)
                        (hc2 : comp_wp a wp2)
                        (lc : lcomp_wp a wp1 hc1)
                        (p : squash (h_eq wp1 wp2 hc1 hc2)) : lcomp_wp a wp2 hc2 = lc

// Satisifability of WPs

let return_wp_sat (#a:Type) (x : a) : Lemma (sat_as_lwp (return_wp x)) = ()

let write_wp_sat (i:nat) (v:mint) : Lemma (sat_as_lwp (write_wp i v)) = ()

let read_wp_sat (i:nat) : Lemma (sat_as_lwp (read_wp i)) = ()

let subsumes_sat #a (wp1 wp2 : hwp_mon a) : Lemma (requires (subsumes wp1 wp2 /\ sat_as_lwp wp2))
                                                  (ensures (sat_as_lwp wp1)) = ()

(** ** Commutation of morphism **)

let morph_return #a (wp : hwp_mon a) (c : comp_wp a wp) (x : a) :
  Lemma
    (requires (c === return_elab x))
    (ensures (return_inv c x;
              morph wp c == lreturn x)) =
  let p = return_inv c x in
  assert (subsumes (return_wp x) wp);
  assert (l_eq #a
               #wp #(cast wp (return_elab x)) (morph wp c)
               #wp #(cast wp (return_elab x)) (lreturn x));
  let p' = l_eq_axiom #a
                      #wp #(cast wp (return_elab x)) (morph wp c)
                      #wp #(cast wp (return_elab x)) (lreturn x) in
  ()

(** Could we somehow work this such equalities? *)
let morph_return' #a (x : a) :
 Lemma
   (morph _ (return_elab x) == lreturn x) = admit ()

let morph_read (wp : hwp_mon mint) (c : comp_wp mint wp) (i : nat{i < 2}) :
  Lemma
    (requires (c === hread_elab i))
    (ensures (read_inv c i;
              morph wp c == lread' i)) =
  let p = read_inv c i in
  assert (subsumes (read_wp i) wp);
  assert (l_eq #mint
               #wp #(cast wp (hread_elab i)) (morph wp (cast wp (hread_elab i)))
               #wp #(cast wp (hread_elab i)) (lread' i));
  let p' = l_eq_axiom #mint
                      #wp #(cast wp (hread_elab i)) (morph wp c)
                      #wp #(cast wp (hread_elab i)) (lread' i) in
  ()


let morph_write (wp : hwp_mon unit) (c : comp_wp unit wp) (i : nat{i < 2}) (v : mint) :
  Lemma
    (requires (c === hwrite_elab i v))
    (ensures (write_inv c i v;
              morph wp c == lwrite' i v)) =
  let p = write_inv c i in
  assert (subsumes (write_wp i v) wp);
  assert (l_eq #unit
               #wp #(cast wp (hwrite_elab i v)) (morph wp (cast wp (hwrite_elab i v)))
               #wp #(cast wp (hwrite_elab i v)) (lwrite' i v));
  let p' = l_eq_axiom #unit
                      #wp #(cast wp (hwrite_elab i v)) (morph wp c)
                      #wp #(cast wp (hwrite_elab i v)) (lwrite' i v) in
  ()

let morph_bind #a #b (wp1 : hwp_mon a) (c1 : comp_wp a wp1)
    (wp2 : a -> hwp_mon b) (c2 : (x:a) -> comp_wp b (wp2 x))
    (wp : hwp_mon b) (c : comp_wp b wp) :
  Lemma (requires (c === bind_elab c1 c2))
        (ensures (bind_inv c1 c2 c;
                  morph wp c == lbind (morph wp1 c1) (fun x -> (morph (wp2 x) (c2 x))))) =
  let p = bind_inv c1 c2 c in
  assert (subsumes (bind_wp wp1 wp2) wp);
  assert (l_eq #b
               #wp #(cast wp (bind_elab c1 c2)) (morph wp (cast wp (bind_elab c1 c2)))
               #wp #(cast wp (bind_elab c1 c2)) (lcast wp (bind_elab c1 c2)
               (lbind (morph wp1 c1) (fun x -> (morph (wp2 x) (c2 x))))));
  let p' = l_eq_axiom #b
                      #wp #(cast wp (bind_elab c1 c2)) (morph wp (cast wp (bind_elab c1 c2)))
                      #wp #(cast wp (bind_elab c1 c2)) (lcast wp (bind_elab c1 c2)
                      (lbind (morph wp1 c1) (fun x -> (morph (wp2 x) (c2 x))))) in
  ()


let morph_for (wp1 : int -> hwp_mon unit) (lo : int) (hi : int{lo <= hi}) (f : (i:int) -> comp_wp unit (wp1 i))
    (wp : hwp_mon unit) (c : comp_wp unit wp) :
  Lemma (requires (c === for_elab lo hi f))
        (ensures (for_inv lo hi f c;
                  morph wp c == lfor lo hi (fun i -> morph (wp1 i) (f i)))) =
  let p = for_inv lo hi f c in
  assert (subsumes (for_wp wp1 lo hi) wp);
  assert (l_eq #unit
               #wp #(cast wp (for_elab lo hi f)) (morph wp (cast wp (for_elab lo hi f)))
               #wp #(cast wp (for_elab lo hi f)) (lcast wp (for_elab lo hi f)
               (lfor lo hi (fun i -> morph (wp1 i) (f i)))));
  let p' = l_eq_axiom #unit
                      #wp #(cast wp (for_elab lo hi f)) (morph wp (cast wp (for_elab lo hi f)))
                      #wp #(cast wp (for_elab lo hi f)) (lcast wp (for_elab lo hi f)
                      (lfor lo hi (fun i -> morph (wp1 i) (f i)))) in

  ()


let morph_for' (inv : state -> int -> Type0) (f : (i:int) -> comp_p unit (fun h0 -> inv h0 i) (fun h0 _ h1 -> inv h1 (i + 1)))
               (lo : int) (hi : int{lo <= hi})
               (wp : hwp_mon unit) (c : comp_wp unit wp) :
  Lemma (requires (c === for_elab' inv f lo hi))
        (ensures (for_inv' inv f lo hi c;
                  morph wp c == lfor' inv f (fun i -> morph _ (f i)) lo hi)) = 
  let p = for_inv' inv f lo hi c in
  assert (l_eq #unit
               #wp #(cast wp (for_elab' inv f lo hi)) (morph wp (cast wp (for_elab' inv f lo hi)))
               #wp #(cast wp (for_elab' inv f lo hi)) (lcast wp (for_elab' inv f lo hi)
               (lfor' inv f (fun i -> morph _ (f i)) lo hi)));
  let p' = l_eq_axiom #unit
                      #wp #(cast wp (for_elab' inv f lo hi)) (morph wp (cast wp (for_elab' inv f lo hi)))
                      #wp #(cast wp (for_elab' inv f lo hi)) (lcast wp (for_elab' inv f lo hi)
                      (lfor' inv f (fun i -> morph _ (f i)) lo hi)) in

  ()
    
  
let morph_ite #a (b : bool) (wp1 : hwp_mon a) (c1 : comp_wp a wp1)
    (wp2 : hwp_mon a) (c2 : comp_wp a wp2)
    (wp : hwp_mon a) (c : comp_wp a wp):
  Lemma (requires (c === ite_elab b c1 c2))
        (ensures (ite_inv b c1 c2 c;
                  morph wp c == lite b (morph wp1 c1) (morph wp2 c2))) =
  let p = ite_inv b c1 c2 c in
  assert (subsumes (ite_wp b wp1 wp2) wp);
  assert (l_eq #a
               #wp #(cast wp (ite_elab b c1 c2)) (morph wp (cast wp (ite_elab b c1 c2)))
               #wp #(cast wp (ite_elab b c1 c2)) (lcast wp (ite_elab b c1 c2)
               (lite b (morph wp1 c1) (morph wp2 c2))));
  let p' = l_eq_axiom #a
                      #wp #(cast wp (ite_elab b c1 c2)) (morph wp (cast wp (ite_elab b c1 c2)))
                      #wp #(cast wp (ite_elab b c1 c2)) (lcast wp (ite_elab b c1 c2)
                      (lite b (morph wp1 c1) (morph wp2 c2))) in
  ()
