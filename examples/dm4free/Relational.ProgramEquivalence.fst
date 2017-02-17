module Relational.ProgramEquivalence

open FStar.List.Tot
open FStar.DM4F.Heap
open FStar.DM4F.Heap.ST

(* reifiable let f () :STNull unit = *)
(*   let r = alloc_weak 0 in *)
(*   () *)

(* let f_obs (h0:heap) = *)
(*   let _, h1 = reify (f ()) h0 in *)
(*   assert (forall (a:Type) (r:ref a). h0 `contains_a_well_typed` r ==> sel h0 r == sel h1 r) *)

(* reifiable let f_1 () :STNull int = *)
(*   let r_1 = alloc_weak 1 in *)
(*   let r_2 = alloc_weak 1 in *)
(*   read_weak r_1 + read_weak r_2 *)

(* reifiable let f_2 () :STNull int = *)
(*   let r_1 = alloc_weak 2 in *)
(*   read_weak r_1 *)

(* let f_1_f_2_obs (h_0:heap) :unit = *)
(*   let r_1, h_1 = reify (f_1 ()) h_0 in *)
(*   let r_2, h_2 = reify (f_1 ()) h_0 in *)
(*   assert (r_1 = r_2 /\ *)
(*           (forall (a:Type) (r:ref a). h_0 `contains` r ==> *)
(* 	                         (sel h_1 r == sel h_0 r /\ *)
(* 				  sel h_2 r == sel h_0 r))) *)

private let contains_well_typed_refs (h:heap) (s:list (ref nat)) =
  forall (r:ref nat). memP r s ==> h `contains_a_well_typed` r

private type fp = l:list (ref nat)

private type incr_t (inv:heap -> fp -> Type0) =
  s:fp -> ST unit (requires (fun h0       -> inv h0 s))
                 (ensures  (fun h0 _ h1  -> inv h1 s))

private type get_t (inv:heap -> fp -> Type0) =
  s:fp -> ST nat (requires (fun h0       -> inv h0 s))
               (ensures  (fun h0 _ h1  -> inv h1 s))

private type ctr_t (inv:heap -> fp -> Type0) = incr_t inv * get_t inv

(*
 * main counter type exported to the client, but abstract
 * TODO: marking it as abstract fails in the batch mode but not in the interactive mode ...
 *)
noeq type counter =
  | C: inv:(heap -> fp -> Type0) -> fp:fp -> c:(ctr_t inv) -> counter

abstract let live (c:counter) (h:heap) = (C?.inv c) h (C?.fp c)

(*
 * TODO: make this abstract, reifiable should be allowed with abstract
 *)
reifiable let increment
  (c:counter) :ST unit (fun h0 -> live c h0) (fun h0 _ h1 -> live c h1)
  = match c with
    | C _ fp f ->
      let i, _ = f in
      i fp

reifiable let get
  (c:counter) :ST nat (fun h0 -> live c h0) (fun h0 _ h1 -> live c h1)
  = match c with
    | C _ fp f ->
      let _, g = f in
      g fp
(*
 * first implementation of the counter uses a single reference
 *)
private let inv_0 (h:heap) (fp:fp) :Type0 =
  h `contains_well_typed_refs` fp /\ length fp = 1

reifiable private let incr_0 :(incr_t inv_0) =
  fun s ->
   let r = hd s in
   let c = read_weak r in
   write_weak r (c + 2)

reifiable private let get_0 :(get_t inv_0) =
  fun s ->
    let r = hd s in
    read_weak r

reifiable let init_counter_0 () :ST counter (requires (fun h0 -> True)) (ensures (fun _ r h1 -> live r h1))
  = let r = alloc_weak 2 in
    C inv_0 [r] (incr_0, get_0)

(*
 * second implementation of the counter uses two references
 *)
private let inv_1 (h:heap) (fp:fp) :Type0 =
  h `contains_well_typed_refs` fp /\ length fp = 2

reifiable private let incr_1 :(incr_t inv_1) =
  fun s ->
    let r_1 = hd s in
    let r_2 = hd (tl s) in
    let c_1 = read_weak r_1 in
    let c_2 = read_weak r_2 in
    write_weak r_1 (c_1 + 1);
    write_weak r_2 (c_2 + 1)

reifiable private let get_1 :(get_t inv_1) =
  fun s ->
    let r_1 = hd s in
    let r_2 = hd (tl s) in
    read_weak r_1 + read_weak r_2

reifiable let init_counter_1 (): ST counter (requires (fun h0 -> True)) (ensures (fun _ r h1 -> live r h1))
  = let r_1 = alloc_weak 1 in
    let r_2 = alloc_weak 1 in
    C inv_1 [r_1; r_2] (incr_1, get_1)

(* let ctr0_ctr1_obs (h:heap) :unit = *)
(*   let c0, h0 = reify (ctr_0 ()) h in *)
(*   let c1, h1 = reify (ctr_1 ()) h in *)

(*   let n, h0 = *)
(*     match c0 with *)
(*     | C _ s f -> *)
(*       let i, g = f in *)
(*       reify (let _ = i s in g s) h0 *)
(*   in *)
(*   assert (n = 4);  *)
(*   let m, h1 = *)
(*     match c1 with *)
(*     | C _ s f -> *)
(*       let i, g = f in *)
(*       reify (let _ = i s in g s) h1 *)
(*   in *)
(*   assert (n = m /\ *)
(*           (forall (a:Type) (r:ref a). h `contains` r ==> (sel h r == sel h0 r /\ *)
(* 	                                             sel h r == sel h1 r))) *)

(* let lemma_0 (s_0:fp) (s_1:fp) (h:heap{inv_0 h s_0 /\ inv_1 h s_1}) *)
(*   :Lemma (requires (fst (reify (get_0 s_0) h) = fst (reify (get_1 s_1) h))) *)
(*          (ensures  (let _, h0 = reify (incr_0 s_0) h in *)
(* 	            let _, h1 = reify (incr_1 s_1) h in *)
(* 		    fst (reify (get_0 s_0) h0) = fst (reify (get_1 s_1) h1) /\ *)
(* 		    (forall (a:Type) (r:ref a). (~ (memP r s_0 \/ memP r s_1)) ==> *)
(* 		                           (sel h r == sel h0 r /\ *)
(* 					    sel h r == sel h1 r)))) *)
(*   = () *)

reifiable let rec increment_m
  (m:nat) (c:counter)
  :ST nat (fun h0      -> live c h0) (fun h0 _ h1 -> live c h1)
  = if m = 0 then get c
    else
      let _ = increment c in
      increment_m (m - 1) c

type counter_0 = c:counter{C?.inv c == inv_0 /\ C?.c c == (incr_0, get_0)}
type counter_1 = c:counter{C?.inv c == inv_1 /\ C?.c c == (incr_1, get_1)}

private let ref_not_in_fp (#a:Type) (r:ref a) (s:fp) =
  forall (r':ref nat). memP r' s ==> ~ (eq3 r r')

private let equal_heaps_except_fp (h0:heap) (h1:heap) (s:fp) =
  forall (a:Type) (r:ref a). ref_not_in_fp r s ==> sel h0 r == sel h1 r

(*
 * we prove that if c_0 and c_1 have equal values,
 * then calling them m times gives the same counter value, and the output heaps are equivalent except at footprints
 *)
let rec observational_equivalence (c_0:counter_0) (c_1:counter_1) (h:heap{live c_0 h /\ live c_1 h}) (m:nat)
  :Lemma (requires (fst (reify (get c_0) h) = fst (reify (get c_1) h)))
	 (ensures  (let n_0, h0 = reify (increment_m m c_0) h in
		    let n_1, h1 = reify (increment_m m c_1) h in
                    n_0 = n_1 /\ equal_heaps_except_fp h0 h1 (append (C?.fp c_0) (C?.fp c_1))))
 = if m = 0 then ()
   else observational_equivalence c_0 c_1 h (m - 1)

let rec observational_equivalence'
  (c_0:counter_0) (c_1:counter_1)
  (h0:heap{live c_0 h0})
  (h1:heap{live c_1 h1})  
  (m:nat)
  :Lemma (requires (equal_heaps_except_fp h0 h1 (append (C?.fp c_0) (C?.fp c_1)) /\
                    fst (reify (get c_0) h0) = fst (reify (get c_1) h1)))
	 (ensures  (let n_0, h0 = reify (increment_m m c_0) h0 in
		    let n_1, h1 = reify (increment_m m c_1) h1 in
                    n_0 = n_1 /\ equal_heaps_except_fp h0 h1 (append (C?.fp c_0) (C?.fp c_1))))
         (decreases m)
 = if m = 0 then ()
   else
     let _, h0 = reify (increment c_0) h0 in
     let _, h1 = reify (increment c_1) h1 in
     observational_equivalence' c_0 c_1 h0 h1 (m - 1)

reifiable 
let rec increment_m'
  (m:nat) (c:counter)
  :ST nat (fun h0      -> live c h0) (fun h0 _ h1 -> live c h1)
  = if m = 0 then get c
    else let _ = increment_m' (m - 1) c in
         increment c;
         get c

(* Proving that m invocations of counter_0 returns the m'th even number
      This is a relation between n invocations of incr 
                        and a single invocation of get
 *)
#set-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"
let rec counts_even_numbers (c_0:counter_0) (h:heap{live c_0 h}) (m:nat)
  :Lemma (requires True)
	 (ensures  (let n, h' = reify (increment_m' m c_0) h in
                    n = op_Multiply 2 m + fst (reify (get c_0) h)))
         (decreases m)
 = admit ()
   (* let init = fst (reify (get c_0) h) in *)
   (* if m = 0  *)
   (* then () *)
   (* else counts_even_numbers c_0 h (m - 1) *)
