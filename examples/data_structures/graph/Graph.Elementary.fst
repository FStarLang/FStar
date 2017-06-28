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
  (decreases (S.length p2))
let rec lemma_mutually_exclusive_elementary_append #n p1 p2 =
 match S.length p2 with
 | 0 -> S.lemma_eq_elim p1 (S.append p1 p2)
 | x ->
   let p1' = (S.snoc p1 (S.head p2)) in
   let p2' = S.tail p2 in
   assert(forall (j: k:_in p2{k>0}) . ~(p2 @^ j == p2 @^ 0));
   assert(forall (j:_in p2'). (p2' @^ j == p2 @^ (j + 1)));
   lemma_disjoint_append p1 (S.create 1 (S.head p2)) p2';
   disjoint_not_eq_head p2 p1;
   lemma_snoc_elementary_without_count p1 (S.head p2);
   S.lemma_eq_elim (S.append p1 p2) (S.append p1' p2');
   lemma_mutually_exclusive_elementary_append p1' p2'

let lemma_valid_graph_snoc  (#n:nat) (g:graph0 n) (p:prepath n) (e:fin n)
 : Lemma (requires (S.length p == 0 \/ (is_in_graph (S.last p) e g /\ valid_path g p)))
   (ensures (valid_path g (S.snoc p e)))
   = ()

let rec to_elementary_path_aux (#n:nat) (g:graph0 n) (p:path g) (pn : prepath n)
 : Pure (path g)
 (requires (elementary pn /\ 
  (disjoint p pn) /\
  (S.length pn == 0 \/ (is_in_graph (S.last pn) (S.head p) g /\ valid_path g pn))))
 (ensures (fun p' -> elementary p'))
 (decreases (S.length p )) =
 let remaining = p in
 begin match S.length remaining with
 | 1 ->
   lemma_mutually_exclusive_elementary_append pn remaining;
   S.append pn remaining
 | x ->
   begin match index_of_l (fun ind -> ind = (S.head remaining)) (S.tail remaining) with
   | None ->
     let pn' = (S.snoc pn (S.head remaining)) in
     assert (~(S.length pn' == 0));
     let remaining' = S.tail remaining in
     let head_seq = S.create 1 (S.head remaining) in
     lemma_mutually_exclusive_elementary_append pn head_seq;
     index_of_l_spec (fun ind -> ind = (S.head remaining)) (S.tail remaining);
     lemma_disjoint_append pn head_seq remaining';
     assert(elementary pn');
     assert(disjoint pn' remaining');
     assert(is_in_graph (S.last pn') (S.head remaining') g);
     assert(valid_path g pn');
     to_elementary_path_aux g remaining' pn'
   | Some v -> 
     let v' = (v+1) in
     let remaining' = S.slice p v' (S.length p) in
     lemma_disjoint_slice pn remaining (v+1) (S.length remaining);
     index_of_l_spec (fun ind -> ind = (S.head remaining)) (S.tail remaining);
     lemma_valid_csubpath_is_valid g p v' (S.length p - 1);
     assert(elementary pn);
     assert(disjoint remaining' pn);


     assert(S.length pn == 0 \/ is_in_graph (S.last pn) (S.head remaining') g);
     assert(S.length pn == 0 \/ valid_path g pn);
     assert(S.length pn == 0 \/ (is_in_graph (S.last pn) (S.head remaining') g /\ valid_path g pn));
     assert(valid_path g remaining');
     assert(S.length remaining' < S.length remaining);
     to_elementary_path_aux g remaining' pn
   end
 end


let to_elementary_path (#n:nat) (g:graph0 n) (p:path g)
 : Pure (path g)
 (requires (True))
 (ensures (fun p' -> elementary p'))
 = to_elementary_path_aux #n g p (S.createEmpty)


(*let rec lemma_elementary_path_eq_to_from (#n:nat) (g:graph0 n) (p:path g)
 : Lemma (requires True)
   (ensures (from (to_elementary_path g p) == from p /\ to (to_elementary_path g p) = to p))
   = 
   begin match S.length p with
   | 1 -> ()
   | x -> 
    begin match index_of_l (fun ind -> ind = (S.head p)) (S.tail p) with
    | None -> 
     let pn' = (S.snoc pn (S.head p)) in
     let remaining' = S.tail remaining in
     lemma_elementary_path_eq_to_from g 
    | Some v -> admit();
      assert(from (to_elementary_path g p) == from p);
      assume(to (to_elementary_path g p) == to p)
    end
   end

let lemma_elementary_path_maintains_all_elements (#n:nat) (g:graph0 n) (p:path g)
 : Lemma (requires True)
   (ensures (exists (i : _in p) . forall (j : _in (to_elementary_path g p)) . 
    (to_elementary_path g p) @^ j == p @^ i))
   = let pn = to_elementary_path g p in
   assert(pn @^ 0 == p @^ 0); admit();
   match S.length p with
   |1 -> assert(pn @^ 0 == p @^ 0)
   |x -> admit() 
*)
