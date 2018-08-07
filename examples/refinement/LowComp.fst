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



type lstate = pointer mint * pointer mint

val well_formed : HS.mem -> lstate -> GTot Type0
let well_formed h = fun (r1, r2) -> live h r1 /\ live h r2 /\ disjoint r1 r2

// To and from high- and low-level state
val lstate_as_state : HS.mem -> lstate -> GTot state
let lstate_as_state h  = fun (b1, b2) -> (B.get h b1 0, B.get h b2 0)


val g_upd_preserves_well_formed : #a:Type -> h:HS.mem -> b1:pointer a{live h b1} -> b2:pointer a{live h b2} -> v:a ->
   Lemma (let h' = g_upd b1 0 v h in modifies (loc_buffer b1) h h' /\ live h b1 /\ live h' b2)
                                
let g_upd_preserves_well_formed #a h b1 b2 v = 
  let p = g_upd_seq_as_seq b1 (Seq.upd (as_seq h b1) 0 v) h in ()

val state_as_lstate : h:HS.mem -> ls:lstate{well_formed h ls} -> state -> GTot HS.mem 
let state_as_lstate h =
  function (r1, r2) -> function (v1, v2) ->
    let h' = g_upd r1 0 v1 h in
    let p = g_upd_preserves_well_formed h r1 r2 v1 in
    g_upd r2 0 v2 h'

type lcomp 'a (c : comp 'a) =
    (ls:lstate) ->
    Stack 'a
      (requires (fun h -> well_formed h ls))
      (ensures  (fun h r h' ->
                   well_formed h' ls /\
                   //modifies (loc_union (loc_buffer (fst ls)) (loc_buffer (snd ls))) h h' /\
                   (let s0 = lstate_as_state h ls in
                    let (x, s1) = c s0 in
                    h' == state_as_lstate h ls s1 /\ x == r )))


let lcomp_wp (a:Type) (wp : state -> (a * state -> Type) -> Type) (c : comp_wp a wp) =
     (ls:lstate) ->
     Stack a
       (requires (fun h -> well_formed h ls))
       (ensures  (fun h r h' ->
                    well_formed h' ls /\
                    (let s0 = lstate_as_state h ls in
                     wp s0 (fun _ -> True) /\ 
                     (let tls = state_as_lstate h ls in // XXX fails otherwise
                      let (x, s1) = c s0 in 
                      h' == tls s1 /\ x == r ))))
                    
let lcomp_wp' (a:Type) (wp : state -> (a * state -> Type) -> Type) (c : comp_wp a wp) =
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
  comp_wp a wp = reify (c ())


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

val lwrite : i:nat{ i < 2 } -> v:mint -> lcomp_wp unit (write_wp i v) (hwrite' i v)
let lwrite i v = fun (b1, b2) -> if i = 0 then b1.(0ul) <- v else b2.(0ul) <- v

val lread : i:nat{ i < 2 } -> lcomp_wp mint (read_wp i) (hread' i)
let lread i = fun (b1, b2) -> if i = 0 then b1.(0ul) else b2.(0ul)

let monotonic (#a: Type) (wp: hwp a) = forall (s: state) p1 p2. (forall x. p1 x ==> p2 x) ==>
  wp s p1 ==> wp s p2

let lbind (#a:Type) (#b:Type)
  (#wp1: state -> (a * state -> Type) -> Type)
  (#wp2: a -> state -> (b * state -> Type) -> Type)
  (#c1:comp_wp a wp1) (#c2:(x:a -> comp_wp b (wp2 x)))
  (m: lcomp_wp a wp1 c1) (f: (x:a) -> lcomp_wp b (wp2 x) (c2 x)):
    lcomp_wp b (bind_wp wp1 wp2) (hbind' c1 c2) =
      fun s ->
        assume (monotonic wp1);
        let a = m s in let r = f a s in r


