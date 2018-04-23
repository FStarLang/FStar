module Point

open FStar.List.Tot
open FStar.DM4F.Heap
open FStar.DM4F.Heap.ST

private let contains_well_typed_refs (h:heap) (s:list (ref nat)) =
  forall (r:ref nat). memP r s ==> h `contains_a_well_typed` r

private type fp = l:list (ref nat)

private type move_t (inv:heap -> fp -> Type0) =
  s:fp -> ST unit (requires (fun h0       -> inv h0 s))
                 (ensures  (fun h0 _ h1  -> inv h1 s))

private type get_t (inv:heap -> fp -> Type0) =
  s:fp -> ST (nat * nat) (requires (fun h0       -> inv h0 s))
                     (ensures  (fun h0 _ h1  -> inv h1 s))

private type point_t (inv:heap -> fp -> Type0) = move_t inv * get_t inv

noeq type point =
  | C: inv:(heap -> fp -> Type0) -> fp:fp -> p:(point_t inv) -> point

(*
 * AR: 06/03: proofs below rely on this being non-abstract
 *)
let live (p:point) (h:heap) = (C?.inv p) h (C?.fp p)

 let move
  (p:point) :ST unit (fun h0 -> live p h0) (fun h0 _ h1 -> live p h1)
  = match p with
    | C _ fp f ->
      let m, _ = f in
      m fp

 let get
  (p:point) :ST (nat * nat) (fun h0 -> live p h0) (fun h0 _ h1 -> live p h1)
  = match p with
    | C _ fp f ->
      let _, g = f in
      g fp

private let inv_point (h:heap) (fp:fp) :Type0 =
  h `contains_well_typed_refs` fp /\ List.Tot.length fp = 2 /\
  addr_of (List.Tot.hd fp) <> addr_of (List.Tot.hd (List.Tot.tl fp))
  (* match fp with *)
  (* | [r1; r2] -> addr_of r1 <> addr_of r2 /\  *)
  (* | _        -> False *)

 private let get_point :(get_t inv_point) =
  fun s ->
    let r1 = hd s in
    let r2 = hd (tl s) in
    let x = read_weak r1 in let y = read_weak r2 in
    (x, y)

 private let move_point :(move_t inv_point) =
  fun s ->
   let r1 = hd s in
   let r2 = hd (tl s) in
   let x = read_weak r1 in
   let y = read_weak r2 in
   write_weak r1 (x + 1);
   write_weak r2 (y + 1)

 let init_point () :ST point (requires (fun h0 -> True)) (ensures (fun _ r h1 -> live r h1))
  = let r1 = alloc 1 in
    let r2 = alloc 1 in
    C inv_point [r1; r2] (move_point, get_point)

private let inv_colored_point (h:heap) (fp:fp) :Type0 =
  h `contains_well_typed_refs` fp /\ length fp = 3 /\
  (let r1 = hd fp in let r2 = hd (tl fp) in let r3 = hd (tl (tl fp)) in
   addr_of r1 <> addr_of r2 /\ addr_of r2 <> addr_of r3 /\ addr_of r3 <> addr_of r1)
   
 private let move_colored_point :(move_t inv_colored_point) =
  fun s ->
   let r1 = hd s in
   let r2 = hd (tl s) in
   let x = read_weak r1 in
   let y = read_weak r2 in
   write_weak r1 (x + 1);
   write_weak r2 (y + 1)

 private let get_colored_point :(get_t inv_colored_point) =
  fun s ->
    let r1 = hd s in
    let r2 = hd (tl s) in
    let x = read_weak r1 in let y = read_weak r2 in
    (x, y)

 let init_colored_point (): ST point (requires (fun h0 -> True)) (ensures (fun _ r h1 -> live r h1))
  = let r_1 = alloc 1 in
    let r_2 = alloc 1 in
    let r_3 = alloc 1 in
    C inv_colored_point [r_1; r_2; r_3] (move_colored_point, get_colored_point)

private let ref_not_in_fp (#a:Type) (r:ref a) (s:fp) =
  forall (r':ref nat). memP r' s ==> addr_of r' <> addr_of r

private let equal_heaps_except_fp (h0:heap) (h1:heap) (s:fp) =
  forall (a:Type) (r:ref a). ref_not_in_fp r s ==> sel h0 r == sel h1 r

#set-options "--z3rlimit 20"
let lemma (h:heap) =
  let p, h1 = reify (init_point ()) h in
  let cp, h2 = reify (init_colored_point ()) h in

  let _, h3 = reify (move p) h1 in
  let _, h4 = reify (move cp) h2 in

  let v3, _ = reify (get p) h3 in
  let v4, _ = reify (get cp) h4 in

  assert (v3 == v4);
  assert (equal_heaps_except_fp h3 h4 (append (C?.fp p) (C?.fp cp)))

(*  let rec increment_m *)
(*   (m:nat) (c:counter) *)
(*   :ST nat (fun h0      -> live c h0) (fun h0 _ h1 -> live c h1) *)
(*   = if m = 0 then get c *)
(*     else *)
(*       let _ = increment c in *)
(*       increment_m (m - 1) c *)

(* (\* *)
(*  * we prove that if c_0 and c_1 have equal values, *)
(*  * then calling them m times gives the same counter value, and the output heaps are equivalent except at footprints *)
(*  *\) *)
(* #set-options "--z3rlimit 50" *)
(* let rec observational_equivalence' *)
(*   (c_0:counter_0) (c_1:counter_1) *)
(*   (h0:heap{live c_0 h0}) *)
(*   (h1:heap{live c_1 h1})   *)
(*   (m:nat) *)
(*   :Lemma (requires (equal_heaps_except_fp h0 h1 (append (C?.fp c_0) (C?.fp c_1)) /\ *)
(*                     fst (reify (get c_0) h0) = fst (reify (get c_1) h1))) *)
(* 	 (ensures  (let n_0, h0 = reify (increment_m m c_0) h0 in *)
(* 		    let n_1, h1 = reify (increment_m m c_1) h1 in *)
(*                     n_0 = n_1 /\ equal_heaps_except_fp h0 h1 (append (C?.fp c_0) (C?.fp c_1)))) *)
(*          (decreases m) *)
(*  = if m = 0 then () *)
(*    else *)
(*      let _, h0' = reify (increment c_0) h0 in *)
(*      let _, h1' = reify (increment c_1) h1 in *)
(*      observational_equivalence' c_0 c_1 h0' h1' (m - 1) *)

(* (\* Proving that m invocations of counter_0 returns the m'th even number *)
(*       This is a relation between n invocations of incr  *)
(*                         and a single invocation of get *)
(*  *\) *)
(* #set-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0 --z3rlimit 20" *)
(* let rec counts_even_numbers (c_0:counter_0) (h:heap{live c_0 h}) (m:nat) *)
(*   :Lemma (requires True) *)
(* 	 (ensures  (let n, h' = reify (increment_m m c_0) h in *)
(*                     n = op_Multiply 2 m + fst (reify (get c_0) h))) *)
(*          (decreases m) *)
(*  = if m = 0 then () *)
(*    else *)
(*      let _, h = reify (increment c_0) h in *)
(*      counts_even_numbers c_0 h (m - 1) *)
