module Graph.Elementary

module S = FStar.Seq
module L = FStar.List.Tot
open FStar.Fin
open Seq.Complements
module C = FStar.Classical
open Graph.Base

let lemma_elementary_slice (#n:nat) (p:prepath n) (i j : k:nat{k <= S.length p})
  : Lemma (requires (i <= j /\ elementary p))
    (ensures (i <= j /\ elementary (S.slice p i j)))
= let p' = S.slice p i j in
  assert (forall (i0 j0: _in p'). p @^ (i+i0) == p @^ (i+j0) ==> i0 == j0)


let lemma_snoc_elementary (#n:nat) (p:prepath n) (e:fin n)
 : Lemma(requires (elementary p /\ index_of e p == None))
   (ensures (elementary (S.snoc p e)))
= let p' = S.append p (S.create 1 e) in
  S.lemma_eq_elim (S.snoc p e) (S.append p (S.create 1 e));
  assert(forall (i0 j0 : k:nat{k<S.length p}). p @^ i0 == p @^ j0 ==> i0 == j0);
  assert(forall (i0 j0 : k:nat{k<S.length p}). p' @^ i0 == p' @^ j0 ==> i0 == j0);
  count_zero_none e p;
  assert(forall (i0 : k:nat{k<S.length p}) . ~(p' @^ i0 == p' @^ (S.length p' - 1)))

let lemma_snoc_elementary_without_count (#n:nat) (p:prepath n) (e:fin n)
 : Lemma(requires (elementary p /\ (forall (i : _in p) . ~(p @^ i == e))))
   (ensures (elementary (S.snoc p e)))
= let p' = S.append p (S.create 1 e) in
  assert(forall (i0 j0 : k:nat{k<S.length p}). p @^ i0 == p @^ j0 ==> i0 == j0);
  assert(forall (i0 j0 : k:nat{k<S.length p}). p' @^ i0 == p' @^ j0 ==> i0 == j0);
  assert(forall (i0 : k:nat{k<S.length p}) . ~(p' @^ i0 == p' @^ (S.length p' - 1)))


(*TODO: Prove that this holds for any ordering *)
val lemma_mutually_exclusive_elementary_append : (#n:nat) -> (p1:prepath n) -> (p2:prepath n) ->
 Lemma (requires (disjoint p1 p2 /\ elementary p1 /\ elementary p2))
  (ensures (elementary (S.append p1 p2)))
let lemma_mutually_exclusive_elementary_append #n p1 p2 =
  let p = S.append p1 p2 in
  let aux (i j : _in p) : Lemma (requires (p @^ i == p @^j)) (ensures (i == j)) =
    let to_p2 (i:_in p{i >= S.length p1}) : _in p2 = i - S.length p1 in
    if i < S.length p1 then
      if j < S.length p1 then
        assert (p1 @^ (i <: nat) == p1 @^ (j <: nat))
      else
        (assert (p1 @^ (i <: nat) == p2 @^ to_p2 j) ; assert (False))
    else
      if j < S.length p1 then
        (assert (p2 @^ to_p2 i == p1 @^ (j <: nat)) ; assert (False))
      else
        assert (p2 @^ to_p2 i == p2 @^ to_p2 j)
  in
  let aux (i j:_in p) : Lemma (p @^ i == p @^ j ==> i == j) = C.move_requires #(_in p) (aux i) j in
  C.forall_intro_2 aux

let lemma_valid_graph_snoc  (#n:nat) (g:graph0 n) (p:prepath n) (e:fin n)
 : Lemma (requires (S.length p == 0 \/ (is_in_graph (S.last p) e g /\ valid_path g p)))
   (ensures (valid_path g (S.snoc p e)))
   = ()

let end_index (#n:nat) (p:prepath n) = S.length p - 1
let subpath (#n:nat) (#g:graph0 n) (p:path g) (i j:_in p)
  : Pure (path g) (requires (i <= j)) (ensures (fun _ -> True))
=
  let r = S.slice p i (j+1) in
  lemma_valid_csubpath_is_valid g p i j ;
  r

#set-options "--max_fuel 0 --max_ifuel 0 --initial_fuel 0 --initial_ifuel 0"

let rec to_elementary_path_aux (#n:nat) (g:graph0 n) (p:path g) (pn : prepath n)
  : Pure (path g)
  (requires (elementary pn /\
    (disjoint p pn) /\
    (S.length pn == 0 \/ (is_in_graph (S.last pn) (S.head p) g /\ valid_path g pn))))
  (ensures (fun p' -> elementary p'))
  (decreases (S.length p ))
=
  if S.length p <= 1 then
    (lemma_mutually_exclusive_elementary_append pn p; S.append pn p)
  else
   let h = S.head p in
   let remaining = S.tail p in
   let f ind = ind = h in
   index_of_l_spec f remaining ;
   match index_of_l f remaining with
   | None ->
     let pn' = S.snoc pn h in
     assert (~(S.length pn' == 0));
     let head_seq = S.create 1 h in
     lemma_mutually_exclusive_elementary_append pn head_seq;
     lemma_disjoint_append pn head_seq remaining;
     assert(elementary pn');
     assert(disjoint pn' remaining);
     assert(is_in_graph (S.last pn') (S.head remaining) g);
     lemma_valid_graph_snoc g pn h ;
     assert(valid_path g pn');
     to_elementary_path_aux g remaining pn'
   | Some v ->
     let v' = v+1 in
     let remaining = subpath p v' (end_index p) in
     lemma_disjoint_slice pn p v' (S.length p);
     assert(elementary pn);
     assert(disjoint remaining pn);
     to_elementary_path_aux g remaining pn

#reset-options

let to_elementary_path (#n:nat) (g:graph0 n) (p:path g)
 : Pure (path g)
 (requires (True))
 (ensures (fun p' -> elementary p'))
 = to_elementary_path_aux #n g p (S.createEmpty)


(* let rec lemma_elementary_path_eq_to_from (#n:nat) (g:graph0 n) (p:path g) *)
(*  : Lemma (requires True) *)
(*    (ensures (from (to_elementary_path g p) == from p /\ to (to_elementary_path g p) = to p)) *)
(*    = *)
(*    begin match S.length p with *)
(*    | 1 -> () *)
(*    | x -> *)
(*     begin match index_of_l (fun ind -> ind = (S.head p)) (S.tail p) with *)
(*     | None -> *)
(*      let pn' = (S.snoc pn (S.head p)) in *)
(*      let remaining' = S.tail remaining in *)
(*      lemma_elementary_path_eq_to_from g *)
(*     | Some v -> admit(); *)
(*       assert(from (to_elementary_path g p) == from p); *)
(*       assume(to (to_elementary_path g p) == to p) *)
(*     end *)
(*    end *)

(* let lemma_elementary_path_maintains_all_elements (#n:nat) (g:graph0 n) (p:path g) *)
(*  : Lemma (requires True) *)
(*    (ensures (exists (i : _in p) . forall (j : _in (to_elementary_path g p)) . *)
(*     (to_elementary_path g p) @^ j == p @^ i)) *)
(*    = let pn = to_elementary_path g p in *)
(*    assert(pn @^ 0 == p @^ 0); admit(); *)
(*    match S.length p with *)
(*    |1 -> assert(pn @^ 0 == p @^ 0) *)
(*    |x -> admit() *)
