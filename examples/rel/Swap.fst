module Swap
open FStar.List.Tot
open FStar.DM4F.Heap
open FStar.DM4F.Heap.ST
#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3rlimit 100"

// Heap relies on sets with decidable equality... we follow suit.
module S = FStar.Set

// We reason about a set of addresses so as to reuse the [modifies] clause.
type addr_set = S.set nat

let heap_equiv_on (h_0:heap) (h_1:heap) (rs:addr_set) =
  forall (a:Type0). forall (r: ref a).
    S.mem (addr_of r) rs /\
    h_0 `contains` r /\
    h_1 `contains` r ==>
    sel h_0 r == sel h_1 r

let heap_eq (h:heap) (h_0:heap) (h_1:heap) =
   forall (a:Type) (r:ref a).  h `contains` r ==> sel h_0 r == sel h_1 r

type command = unit -> STNull unit

let no_alloc (h:heap) (h':heap) = forall (a:Type0). forall (r: ref a). h `contains` r <==> h' `contains` r

(** [fp_body f rs ws h_0 h_1] means as long as h_0 and h_1 coincide on [rs], then the
    resulting heaps coincide on [ws]. *)
let fp_body (f: command) (rs: addr_set) (ws: addr_set) (h_0:heap) (h_1:heap) = // /\ heap_contains h_0 (rs `S.union` ws) /\ heap_contains h_1 (rs `S.union` ws)}) =
  let (), h'_0 = reify (f ()) h_0 in
  let (), h'_1 = reify (f ()) h_1 in
  modifies ws h_0 h'_0 /\
  modifies ws h_1 h'_1 /\
  no_alloc h_0 h'_0 /\
  no_alloc h_1 h'_1 /\  
  (heap_equiv_on h_0 h_1 rs ==> heap_equiv_on h'_0 h'_1 ws)

(** [footprint f rs ws] generalizes the heaps in fp_body **)
let footprint (f: command) (rs: addr_set) (ws: addr_set) =
  forall (h_0: heap) (h_1: heap).{:pattern (reify (f ()) h_0);
                                    (reify (f ()) h_1)} fp_body f rs ws h_0 h_1

(* [cmd r w] is a command whose footprint is r,w  *)
type cmd (r:addr_set) (w:addr_set) = c:command{footprint c r w}


let seq' (#r1 #w1 #r2 #w2 : addr_set) (c1:cmd r1 w1) (c2:cmd r2 w2) (_:unit) : STNull unit =
  (c1 <: command) (); (c2 <: command) ()

let seq'_lem (#r1 #w1 #r2 #w2 : addr_set) (c1:cmd r1 w1) (c2:cmd r2 w2) 
 : Lemma (footprint (seq' c1 c2) (r1 `S.union` r2) (w1 `S.union` w2))
 = let aux (h:heap) (h':heap)
      : Lemma (fp_body (seq' c1 c2) (r1 `S.union` r2) (w1 `S.union` w2) h h') 
      = let c1 = c1 <: command in
        let c2 = c2 <: command in  
        let _, h1 = reify (c1 ()) h in 
        let _, h2 = reify (c2 ()) h1 in 
        let _, h1' = reify (c1 ()) h' in 
        let _, h2' = reify (c2 ()) h1' in 
        () in
   FStar.Classical.forall_intro_2 aux

let (>>) (#r1 #w1 #r2 #w2 : addr_set) (c1:cmd r1 w1) (c2:cmd r2 w2) 
  : cmd (r1 `S.union` r2) (w1 `S.union` w2)
  = seq'_lem c1 c2;
    seq' c1 c2

let equiv_on_h (c_0:command) (c_1:command) (h:heap) = 
       let (), h_0 = reify (c_0 ()) h in
       let (), h_1 = reify (c_1 ()) h in
       no_alloc h h_0 /\
       no_alloc h h_1 /\
       heap_eq h h_0 h_1

(** [equiv c_0 c_1] : c_0 and c_1 are equivalent if when run in identical initial heaps, 
                    result in equivalent final heaps, 
                    and do not allocate **)
let equiv (c_0:command) (c_1:command) = forall h. equiv_on_h c_0 c_1 h

(** A relational example. Consider two functions f1 and f2, who read
    (resp. write) disjoint sets of references in the heap. Then, calling 
    [f1 (); f2 ()] should be the same as calling [f2 (); f1 ()]. *)
let swap (#rs1 #rs2 #ws1 #ws2: addr_set) 
         (f1: cmd rs1 ws1)
         (f2: cmd rs2 ws2) : 
  Lemma
    (requires (S.disjoint ws1 ws2 /\ S.disjoint rs1 ws2 /\ S.disjoint rs2 ws1))
    (ensures (equiv (f1 >> f2) (f2 >> f1)))
  = let aux (h:heap) : Lemma (equiv_on_h (f1 >> f2) (f2 >> f1) h) =
      let f1 = f1 <: command in
      let f2 = f2 <: command in      
      let (), h_1 = reify (f1 ()) h in //Strange that we seem to need these to trigger
      let (), h_2 = reify (f2 ()) h in //the same terms in the post-condition don't seem to be sufficient
      () in                              //Also strange that the other two terms don't seem necessary
    FStar.Classical.forall_intro aux


(** If whatever [f] writes only depends on [rs], then calling a [f] a second
    time should write the same values into the heap. *)
let idem (#rs #ws:addr_set) (f:cmd rs ws)
  : Lemma (requires (S.disjoint rs ws))
          (ensures (equiv (f >> f) f))
  = let aux (h:heap) : Lemma (equiv_on_h (f >> f) f h) =
      let f = f <: command in
      let (), h_1 = reify (f ()) h in
      let (), h_2 = reify (f ()) h_1 in
      () in                         
    FStar.Classical.forall_intro aux

type guard' = unit -> STNull bool

let guard_is_readonly (c:guard') =
  forall (h:heap).
    let _, h1 = reify ((c <: guard') ()) h in
    h == h1

type guard = f:(unit -> STNull bool){forall (h:heap). h == snd (reify (f ()) h)}

 let cond (c:guard) (c1:command) (c2:command) (_:unit) :STNull unit
  = let b = (c <: guard) () in
    if b then (c1 <: command) () else (c2 <: command) ()

let lemma_replace_cond (c:guard) (c1:command) (c2:command)
  :Lemma (requires (guard_is_readonly c /\ equiv c1 c2))
         (ensures  (equiv (cond c c1 c2) c1 /\
	            equiv (cond c c1 c2) c2))
  = let aux (h:heap) :Lemma (equiv_on_h (cond c c1 c2) c1 h /\ equiv_on_h (cond c c1 c2) c2 h)
      = let (), _ = reify ((c1 <: command) ()) h in
        let (), _ = reify ((c2 <: command) ()) h in
        ()
    in
    FStar.Classical.forall_intro aux

let lemma_skip_c1 (#r1 #w1 #r2 #w2:addr_set) (c1:cmd r1 w1) (c2:cmd r2 w2)
  :Lemma (requires (S.disjoint w1 r2 /\ S.subset w1 w2))
         (ensures  (equiv (c1 >> c2) c2))
  = let aux (h:heap) :Lemma (equiv_on_h (c1 >> c2) c2 h) =  
      let (), h1 = reify ((c1 <: command) ()) h in
      let (), h2 = reify ((c2 <: command) ()) h in
      ()
    in
    FStar.Classical.forall_intro aux

(*** OLD ***)


(** [footprint2 f rs ws] means as long as two heaps coincide on [rs], then the
    resulting heaps coincide on [ws]. *)
let footprint2 (f: command) (rs: addr_set) (ws: addr_set) =
  forall (h_0: heap) (h_1: heap).{:pattern (reify (f ()) h_0);
                                    (reify (f ()) h_1)} 
  let (), h'_0 = reify (f ()) h_0 in
  let (), h'_1 = reify (f ()) h_1 in
  modifies ws h_0 h'_0 /\
  modifies ws h_1 h'_1 /\
  no_alloc h_0 h'_0 /\
  no_alloc h_1 h'_1 /\
  (heap_equiv_on h_0 h_1 rs ==> heap_equiv_on h'_0 h'_1 ws)

(** A relational example. Consider two functions f1 and f2, who read
    (resp. write) disjoint sets of references in the heap. Then, calling [f1
    (); f2 ()] should be the same as calling [f2 (); f1 ()]. *)
val swap_old (rs1: addr_set) (ws1: addr_set) (f1: unit -> STNull unit)
  (rs2: addr_set) (ws2: addr_set) (f2: unit -> STNull unit)
  (h_0: heap) :
  Lemma
    (requires (S.disjoint ws1 ws2 /\ S.disjoint rs1 ws2 /\ S.disjoint rs2 ws1 /\
      footprint2 f1 rs1 ws1 /\ footprint2 f2 rs2 ws2))
    (ensures (
      let (), h_1 = reify (f1 ()) h_0 in
      let (), h'_1 = reify (f2 ()) h_1 in
      let (), h_2 = reify (f2 ()) h_0 in
      let (), h'_2 = reify (f1 ()) h_2 in
      (* no_alloc h_0 h'_1 /\ *)
      (* no_alloc h_0 h'_2 /\       *)
      heap_eq h_0 h'_1 h'_2))
let swap_old rs1 ws1 f1 rs2 ws2 f2 h_0 =
  let (), h_1 = reify (f1 ()) h_0 in //Strange that we seem to need these to trigger
  let (), h_2 = reify (f2 ()) h_0 in //the same terms in the post-condition don't seem to be sufficient
  ()                              //Also strange that the other two terms don't seem necessary


(** If whatever [f] writes only depends on [rs], then calling a [f] a second
    time should write the same values into the heap. *)
let idem_old (rs ws:addr_set) (f:unit -> STNull unit)  (h0:heap)
  : Lemma (requires (S.disjoint rs ws /\
                     footprint2 f rs ws))
          (ensures (let _, h1 = reify (f ()) h0 in
                    let _, h2 = reify (f ()) h1 in
                    heap_eq h0 h1 h2))
  = let _, h1 = reify (f ()) h0 in
    let _, h2 = reify (f ()) h1 in
    ()
