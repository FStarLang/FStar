module Graph.Elementary

module S = FStar.Seq
module L = FStar.List.Tot
open FStar.Fin
open Seq.Complements
module C = FStar.Classical
open Graph.Base

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

let lemma_valid_graph_append_empty_path (#n:nat) (g:graph0 n) (q p:prepath n) (e:fin n)
  : Lemma (requires (q == (p `S.append` empty_path_at g e)) /\
    (S.length p == 0 \/ (is_in_graph (S.last p) e g /\ valid_path g p)))
   (ensures (valid_path g q))
= ()

let end_index (#n:nat) (p:prepath n) = S.length p - 1
let subpath (#n:nat) (#g:graph0 n) (p:path g) (i j:_in p)
  : Pure (path g) (requires (i <= j)) (ensures (fun _ -> True))
=
  let r = S.slice p i (j+1) in
  lemma_valid_csubpath_is_valid g p i j ;
  r

let lemma_subpath_disjoint (#n:nat) (g:graph0 n) (p1 : path g) (p2:prepath n) (i j:_in p1) :
  Lemma (requires (i <= j /\ disjoint p1 p2)) (ensures ( i <= j /\ disjoint (subpath p1 i j) p2))
=
  lemma_disjoint_slice p2 p1 (i <: nat) (j+1 <: nat) ;
  lemma_disjoint_symmetric p2 (subpath p1 i j)

let pre (#n:nat) (g:graph0 n) (p:path g) (pn : prepath n) =
  elementary pn /\
  disjoint p pn /\
  (
    S.length pn == 0 \/
    (is_in_graph (S.last pn) (S.head p) g /\ valid_path g pn)
  )

let lemma_append_last (#a:Type) (s1 s2:S.seq a) : Lemma (requires (S.length s2 > 0)) (ensures (S.length s2 > 0 /\ S.last (s1 `S.append` s2) == S.last s2)) = ()

let maybe_trim_path (#n:nat) (g:graph0 n) (p:path g) (pn : prepath n)
  : Pure (path g * prepath n)
    (requires (pre g p pn /\ S.length p > 1))
    (ensures (fun (p', pn') -> pre g p' pn' /\ S.length p' < S.length p))
=
  let h = S.head p in
  let remaining = S.tail p in
  let f ind = ind = h in
  index_of_l_spec f remaining ;
  match index_of_l f remaining with
  | None ->
    let head_seq = empty_path_at g h in
    lemma_empty_path_elementary g h ;
    assert (disjoint head_seq remaining /\ disjoint pn head_seq) ;
    if S.length pn = 0 then
      remaining, head_seq
    else
      let pn' = pn `S.append` head_seq in
      lemma_mutually_exclusive_elementary_append pn head_seq;
      (* KM : I don't understand why but adding this intermediate step makes the proof go smoother *)
      assert(elementary (S.append pn head_seq));
      assert(elementary pn');
      lemma_disjoint_append pn head_seq remaining;
      assert(disjoint (S.append pn head_seq) remaining);
      assert(disjoint pn' remaining);
      lemma_append_last pn head_seq ;
      assert (S.last pn' == h) ;
      assert(is_in_graph (S.last pn') (S.head remaining) g);
      assert (head_seq == empty_path_at g h) ;
      assert(pn' == pn `S.append` empty_path_at g h) ;
      lemma_valid_graph_append_empty_path g pn'  pn h ;
      remaining, pn'
  | Some v ->
    let v' = v+1 in
    let remaining = subpath p v' (end_index p) in
    lemma_subpath_disjoint g p pn v' (end_index p) ;
    assert(disjoint remaining pn);
    remaining, pn

let rec to_elementary_path_aux (#n:nat) (g:graph0 n) (p:path g) (pn : prepath n)
  : Pure (path g)
  (requires (pre g p pn))
  (ensures (fun p' -> elementary p'))
  (decreases (S.length p ))
=
  if S.length p <= 1 then
    (lemma_mutually_exclusive_elementary_append pn p; S.append pn p)
  else
   let remaining, pn = maybe_trim_path g p pn in
   to_elementary_path_aux g remaining pn


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
