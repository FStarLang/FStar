module ProgramEquivalence

open FStar.List.Tot
open FStar.DM4F.Heap
open FStar.DM4F.Heap.ST

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

(*
 * AR: 06/03: proofs below rely on this being non-abstract
 *)
let live (c:counter) (h:heap) = (C?.inv c) h (C?.fp c)

(*
 * TODO: make this abstract,  should be allowed with abstract
 *)
 let increment
  (c:counter) :ST unit (fun h0 -> live c h0) (fun h0 _ h1 -> live c h1)
  = match c with
    | C _ fp f ->
      let i, _ = f in
      i fp

 let get
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

 private let incr_0 :(incr_t inv_0) =
  fun s ->
   let r = hd s in
   let c = read_weak r in
   write_weak r (c + 2)

 private let get_0 :(get_t inv_0) =
  fun s ->
    let r = hd s in
    read_weak r

 let init_counter_0 () :ST counter (requires (fun h0 -> True)) (ensures (fun _ r h1 -> live r h1))
  = let r = alloc_weak 2 in
    C inv_0 [r] (incr_0, get_0)

(*
 * second implementation of the counter uses two references
 *)
private let inv_1 (h:heap) (fp:fp) :Type0 =
  h `contains_well_typed_refs` fp /\ length fp = 2 /\ (addr_of (hd fp) <> addr_of (hd (tl fp)))

 private let incr_1 :(incr_t inv_1) =
  fun s ->
    let r_1 = hd s in
    let r_2 = hd (tl s) in
    let c_1 = read_weak r_1 in
    let c_2 = read_weak r_2 in
    write_weak r_1 (c_1 + 1);
    write_weak r_2 (c_2 + 1)

 private let get_1 :(get_t inv_1) =
  fun s ->
    let r_1 = hd s in
    let r_2 = hd (tl s) in
    let x = read_weak r_1 in
    let y = read_weak r_2 in
    x + y

type counter_0 = c:counter{C?.inv c == inv_0 /\ C?.c c == (incr_0, get_0)}
type counter_1 = c:counter{C?.inv c == inv_1 /\ C?.c c == (incr_1, get_1)}

(*
 * this proof goes through if get_1 is just returns read_weak r_1 + read_weak r_2,
 * instead of the explicit let binding with nat annotation
 *)
(*let false_proof (c:counter_1) (h:heap{live c h /\ fst (reify (get c) h) = 2}) :unit =
  assert False*)

 let init_counter_1 (): ST counter (requires (fun h0 -> True)) (ensures (fun _ r h1 -> live r h1))
  = let r_1 = alloc_weak 1 in
    let r_2 = alloc_weak 1 in
    assume (addr_of r_1 <> addr_of r_2);
    C inv_1 [r_1; r_2] (incr_1, get_1)

 let rec increment_m
  (m:nat) (c:counter)
  :ST nat (fun h0      -> live c h0) (fun h0 _ h1 -> live c h1)
  = if m = 0 then get c
    else
      let _ = increment c in
      increment_m (m - 1) c

private let ref_not_in_fp (#a:Type) (r:ref a) (s:fp) =
  forall (r':ref nat). memP r' s ==> addr_of r' <> addr_of r

private let equal_heaps_except_fp (h0:heap) (h1:heap) (s:fp) =
  forall (a:Type) (r:ref a). ref_not_in_fp r s ==> sel h0 r == sel h1 r

(*
 * we prove that if c_0 and c_1 have equal values,
 * then calling them m times gives the same counter value, and the output heaps are equivalent except at footprints
 *)
#set-options "--z3rlimit 50"
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
     let _, h0' = reify (increment c_0) h0 in
     let _, h1' = reify (increment c_1) h1 in
     observational_equivalence' c_0 c_1 h0' h1' (m - 1)

(* Proving that m invocations of counter_0 returns the m'th even number
      This is a relation between n invocations of incr 
                        and a single invocation of get
 *)
#set-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0 --z3rlimit 20"
let rec counts_even_numbers (c_0:counter_0) (h:heap{live c_0 h}) (m:nat)
  :Lemma (requires True)
	 (ensures  (let n, h' = reify (increment_m m c_0) h in
                    n = op_Multiply 2 m + fst (reify (get c_0) h)))
         (decreases m)
 = if m = 0 then ()
   else
     let _, h = reify (increment c_0) h in
     counts_even_numbers c_0 h (m - 1)
