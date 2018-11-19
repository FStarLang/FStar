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
type hwp hstate a = hstate -> (a * hstate -> Type) -> GTot Type

let monotonic #hstate #a (wp:hwp hstate a) =
  forall p1 p2 s. {:pattern wp s p1; wp s p2}
    (forall x.{:pattern (p1 x) \/ (p2 x)} p1 x ==> p2 x) ==>
    wp s p1 ==>
    wp s p2

type hwp_mon #hstate 'a = (wp:hwp hstate 'a{monotonic wp})

(* High compuations *)
type high #hstate a (wp : hwp_mon #hstate a) = s0:hstate -> PURE (a * hstate) (wp s0)

(* Low computations *)
type low #lstate #hstate (#p: state_lens lstate hstate)
         (a:Type) (wp : hwp_mon a) (c : high #hstate a wp) =
         ls:lstate ->
         Stack a
           (requires (fun h -> wf #_ #_ #p h ls /\ (let s0 = to_high #_ #_ #p h ls in wp s0 (fun _ -> True))))
           (ensures  (fun h r h' ->
                       wf h' ls /\
                      (let s0 = to_high #_ #_ #p h ls in
                       let (x, s1) = c s0 in
                       h' == to_low #_ #_ #p h ls s1 /\ x == r )))

let run_high #hstate #a #wp (c:high #hstate a wp) (s0:_{wp s0 (fun _ -> True)}) : (a * hstate) = c s0

// Lifting of high programs to low programs
let morph #lstate #hstate (#p: state_lens lstate hstate)
           (a:Type) (wp : hwp_mon a) (c : high #hstate a wp) : low #lstate #hstate #p a wp c =
  fun ls ->
    let hs = to_high' #_ #_ #p ls in 
    let (x, hs') = run_high c hs in
    to_low' #_ #_ #p ls hs'; x


(* High WPS *)
unfold
let return_wp #hstate (#a:Type) (x : a) : hwp_mon a = fun (s0 : hstate) p -> p (x, s0)

unfold
let bind_wp #hstate #a #b (wp1:hwp_mon a) (fwp2 : (a -> hwp_mon b)) : (wp:hwp_mon b) =
    fun (s0:hstate) p -> wp1 s0 (fun ((x, s1) : (a * hstate)) -> fwp2 x s1 p)

unfold 
let read_wp #hstate : hwp_mon hstate = fun (s: hstate) p -> p (s, s)

unfold 
let write_wp #hstate (s : hstate) : hwp_mon unit = fun (s0: hstate) p -> p ((), s)


(* High combinatoers *)
let return_elab (#hstate:Type) (#a:Type) (x : a) : high #hstate a (return_wp x) = fun (s0 : hstate) -> (x, s0)

let bind_elab #hstate #a #b #f_w (f:high #hstate a f_w) #g_w ($g:(x:a) -> high #hstate b (g_w x)) 
: high #hstate b (bind_wp f_w g_w) = fun s0 -> let (r1, s1) = run_high f s0 in run_high (g r1) s1

let read_elab #hstate : high hstate read_wp = fun (s : hstate) -> (s, s) 

let write_elab #hstate (s : hstate) : high unit (write_wp s) = fun (s0 : hstate) -> ((), s) 


(* Low combinators *)
let lreturn #lstate #state (#p: state_lens lstate state) (a:Type) (x : a)
: low #_ #_ #p a (return_wp x) (return_elab x) = 
  fun ls -> 
     let h0 = ST.get () in
     let p = high_low #_ #_ #p h0 ls in (* 1st lens law *)
     assert (h0 == to_low h0 ls (to_high h0 ls));
     x

let lbind #lstate #state (#p: state_lens lstate state) #a #b
    (#wp1:hwp_mon a) (#fwp2:(a -> hwp_mon #state b))
    (#c1:high #state a wp1) (#c2:(x:a -> high #state b (fwp2 x)))
    (m:low #lstate #state #p a wp1 c1) (f:(x:a) -> low #lstate #state #p b (fwp2 x) (c2 x)) :
    low #lstate #state #p b (bind_wp wp1 fwp2) (bind_elab c1 c2) =
  fun ls -> 
    (* almost verbatim from specialized [lbind] *)
    (* ********************************************* *)

    let h0 = ST.get () in // initial heap

    (* ********************************************* *)

    let x_a = m ls in 

    (* ********************************************* *)

    let h1 = ST.get () in // intermediate heap

    let hc : Ghost.erased _ =
      //In this block, we run the high computation
      //in ghost code and remember its intermediate states and result
      let s0 = to_high #_ #_ #p h0 ls in
      let x, s1 = run_high c1 s0 in
      assert (x == x_a);
      assert (h1 == to_low #_ #_ #p h0 ls s1);
      low_high h0 ls s1; //Get-Put: 1st lens law
      assert (to_high  #_ #_ #p h1 ls == s1); //this assertion is key to running `f x_a ls` below
      let y, s2 = run_high (c2 x) s1 in
      assert (s2 == snd (run_high #state #b #(bind_wp wp1 fwp2) (bind_elab c1 c2) s0));
      Ghost.hide (s0, (x, s1), (y, s2))
    in
  
    (* ********************************************* *)
    
    let y_b = f x_a ls in
    
    (* ********************************************* *)
    
    let h2 = ST.get () in // final heap
    let _ : unit =
      //In this block, we unpack the memoized result from earlier
      //and relate those values to the result and final heap
      let s0, (x, s1), (y, s2) = Ghost.reveal hc in
      assert (x == x_a);
      assert (y == y_b);
      assert (h2 == to_low #_ #_ #p h1 ls s2);
      assert (h1 == to_low #_ #_ #p h0 ls s1);
      let _ = low_low #_ #_ #p h0 ls s1 s2 in
      assert (to_low #_ #_ #p h0 ls s2 == to_low #_ #_ #p (to_low #_ #_ #p h0 ls s1) ls s2);
      assert (to_low #_ #_ #p h0 ls s2 == to_low #_ #_ #p h1 ls s2)
    in
  
    (* ********************************************* *)
    y_b
  



