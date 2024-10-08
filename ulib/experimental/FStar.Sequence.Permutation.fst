(*
   Copyright 2021 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Author: N. Swamy
*)
module FStar.Sequence.Permutation
open FStar.Sequence
open FStar.Calc
open FStar.Sequence.Util
module S = FStar.Sequence

////////////////////////////////////////////////////////////////////////////////
[@@"opaque_to_smt"]
let is_permutation (#a:Type) (s0:seq a) (s1:seq a) (f:index_fun s0) =
  S.length s0 == S.length s1 /\
  (forall x y. // {:pattern f x; f y}
  x <> y ==> f x <> f y) /\
  (forall (i:nat{i < S.length s0}). // {:pattern (S.index s1 (f i))}
      S.index s0 i == S.index s1 (f i))

let reveal_is_permutation #a (s0 s1:seq a) (f:index_fun s0)
  = reveal_opaque (`%is_permutation) (is_permutation s0 s1 f)

let reveal_is_permutation_nopats (#a:Type) (s0 s1:seq a) (f:index_fun s0)
  : Lemma (is_permutation s0 s1 f <==>

           S.length s0 == S.length s1 /\

           (forall x y. x <> y ==> f x <> f y) /\

           (forall (i:nat{i < S.length s0}).
              S.index s0 i == S.index s1 (f i)))
   = reveal_is_permutation s0 s1 f


let split3_index (#a:eqtype) (s0:seq a) (x:a) (s1:seq a) (j:nat)
  : Lemma
    (requires j < S.length (S.append s0 s1))
    (ensures (
      let s = S.append s0 (cons x s1) in
      let s' = S.append s0 s1 in
      let n = S.length s0 in
      if j < n then S.index s' j == S.index s j
      else S.index s' j == S.index s (j + 1)
    ))
  = let n = S.length (S.append s0 s1) in
    if j < n then ()
    else ()

let rec find (#a:eqtype) (x:a) (s:seq a{ count x s > 0 })
  : Tot (frags:(seq a & seq a) {
      let s' = S.append (fst frags) (snd frags) in
      let n = S.length (fst frags) in
      s `S.equal` S.append (fst frags) (cons x (snd frags))
    }) (decreases (S.length s))
  = reveal_opaque (`%count) (count #a);
    if head s = x
    then S.empty, tail s
    else (
      let pfx, sfx = find x (tail s) in
      assert (S.equal (tail s)
                        (S.append pfx (cons x sfx)));
      assert (S.equal s
                        (cons (head s) (tail s)));
      cons (head s) pfx, sfx
    )

let count_singleton_one (#a:eqtype) (x:a)
  : Lemma (count x (singleton x) == 1)
  = reveal_opaque (`%count) (count #a)
let count_singleton_zero (#a:eqtype) (x y:a)
  : Lemma (x =!= y ==> count x (singleton y) == 0)
  = reveal_opaque (`%count) (count #a)
let equal_counts_empty (#a:eqtype) (s0 s1:seq a)
  : Lemma
    (requires S.length s0 == 0 /\ (forall x. count x s0 == count x s1))
    (ensures  S.length s1 == 0)
  = reveal_opaque (`%count) (count #a);
    if S.length s1 > 0 then
    assert (count (head s1) s1 > 0)
let count_head (#a:eqtype) (x:seq a{ S.length x > 0 })
  : Lemma (count (head x) x > 0)
  = reveal_opaque (`%count) (count #a)

#restart-solver
#push-options "--fuel 0 --ifuel 0 --z3rlimit_factor 4"
let rec permutation_from_equal_counts (#a:eqtype) (s0:seq a) (s1:seq a{(forall x. count x s0 == count x s1)})
  : Tot (seqperm s0 s1)
        (decreases (S.length s0))
  = if S.length s0 = 0
    then (
      count_empty s0;
      assert (forall x. count x s0 = 0);
      let f : index_fun s0 = fun i -> i in
      reveal_is_permutation_nopats s0 s1 f;
      equal_counts_empty s0 s1;
      f
    )
    else (
      count_head s0;
      let pfx, sfx = find (head s0) s1 in
      introduce forall x. count x (tail s0) == count x (S.append pfx sfx)
      with
      (
        if x = head s0
        then  (
          calc (eq2 #int) {
            count x (tail s0) <: int;
          (==) {
                 assert (s0 `S.equal` cons (head s0) (tail s0));
                 lemma_append_count_aux (head s0) (S.singleton (head s0)) (tail s0);
                 count_singleton_one x
               }
            count x s0 - 1 <: int;
          (==) {}
            count x s1 - 1 <: int;
          (==) {}
            count x (S.append pfx (cons (head s0) sfx)) - 1 <: int;
          (==) { lemma_append_count_aux x pfx (cons (head s0) sfx) }
            count x pfx + count x (cons (head s0) sfx) - 1 <: int;
          (==) { lemma_append_count_aux x (S.singleton (head s0)) sfx }
            count x pfx + (count x (S.singleton (head s0)) + count x sfx) - 1 <: int;
          (==) { count_singleton_one x }
            count x pfx + count x sfx <: int;
          (==) { lemma_append_count_aux x pfx sfx }
            count x (S.append pfx sfx) <: int;
          }
        )
        else (
          calc (==) {
            count x (tail s0);
           (==) {
                  assert (s0 `S.equal` cons (head s0) (tail s0));
                  lemma_append_count_aux x (S.singleton (head s0)) (tail s0);
                  count_singleton_zero x (head s0)
                }
            count x s0;
           (==) { }
            count x s1;
           (==) { }
            count x (S.append pfx (cons (head s0) sfx));
           (==) { lemma_append_count_aux x pfx (cons (head s0) sfx) }
            count x pfx + count x (cons (head s0) sfx);
          (==) { lemma_append_count_aux x (S.singleton (head s0)) sfx }
            count x pfx + (count x (S.singleton (head s0)) + count x sfx) ;
          (==) { count_singleton_zero x (head s0) }
            count x pfx + count x sfx;
          (==) { lemma_append_count_aux x pfx sfx }
            count x (S.append pfx sfx);
          }
        )
      );
      let s1' = (S.append pfx sfx) in
      let f' = permutation_from_equal_counts (tail s0) s1'  in
      reveal_is_permutation_nopats (tail s0) s1' f';
      let n = S.length pfx in
      let f : index_fun s0 =
          fun i -> if i = 0
                then n
                else if f' (i - 1) < n
                then f' (i - 1)
                else f' (i - 1) + 1
      in
      assert (S.length s0 == S.length s1);
      assert (forall x y. x <> y ==> f' x <> f' y);
      introduce forall x y. x <> y ==> f x <> f y
      with (introduce _ ==> _
            with _. (
              if f x = n || f y = n
              then ()
              else if f' (x - 1) < n
              then (
                assert (f x == f' (x - 1));
                if f' (y - 1) < n
                then assert (f y == f' (y - 1))
                else assert (f y == f' (y - 1) + 1)
              )
              else (
                assert (f x == f' (x - 1) + 1);
                if f' (y - 1) < n
                then assert (f y == f' (y - 1))
                else assert (f y == f' (y - 1) + 1)
              )
            )
      );
      reveal_is_permutation_nopats s0 s1 f; f)
#pop-options

#restart-solver

module CM = FStar.Algebra.CommMonoid
let elim_monoid_laws #a (m:CM.cm a)
  : Lemma (
          (forall x y. {:pattern m.mult x y}  m.mult x y == m.mult y x) /\
          (forall x y z.{:pattern (m.mult x (m.mult y z))} m.mult x (m.mult y z) == m.mult (m.mult x y) z) /\
          (forall x.{:pattern (m.mult x m.unit)} m.mult x m.unit == x)
    )
  = introduce forall x y. m.mult x y == m.mult y x
    with ( m.commutativity x y );

    introduce forall x y z. m.mult x (m.mult y z) == m.mult (m.mult x y) z
    with ( m.associativity x y z );

    introduce forall x. m.mult x m.unit == x
    with ( m.identity x )

#restart-solver
#push-options "--fuel 1 --ifuel 0"
let rec foldm_back_append #a (m:CM.cm a) (s1 s2: seq a)
  : Lemma
    (ensures foldm_back m (append s1 s2) == m.mult (foldm_back m s1) (foldm_back m s2))
    (decreases (S.length s2))
  = elim_monoid_laws m;
    if S.length s2 = 0
    then (
      assert (S.append s1 s2 `S.equal` s1);
      assert (foldm_back m s2 == m.unit)
    )
    else (
      let s2', last = un_build s2 in
      calc (==)
      {
        foldm_back m (append s1 s2);
        (==) { assert (S.equal (append s1 s2)
                                 (S.build (append s1 s2') last)) }
        foldm_back m (S.build (append s1 s2') last);
        (==) {}
        fold_back m.mult (S.build (append s1 s2') last) m.unit;
        (==) {}
        m.mult ((S.build (append s1 s2') last) $@ (length s1 + length s2'))
               (fold_back m.mult (take (S.build (append s1 s2') last) (length s1 + length s2')) m.unit);
        (==) { }
        m.mult last
               (fold_back m.mult (take (S.build (append s1 s2') last) (length s1 + length s2')) m.unit);
        (==) {  
          assert (S.equal (take (S.build (append s1 s2') last) (length s1 + length s2')) (append s1 s2'))
        }
        m.mult last (foldm_back m (append s1 s2'));
        (==) { foldm_back_append m s1 s2' }
        m.mult last (m.mult (foldm_back m s1) (foldm_back m s2'));
        (==) { }
        m.mult (foldm_back m s1) (m.mult last (foldm_back m s2'));
        (==) { }
        m.mult (foldm_back m s1) (foldm_back m s2);
      }
    )
#pop-options

let foldm_back_sym #a (m:CM.cm a) (s1 s2: seq a)
  : Lemma
    (ensures foldm_back m (append s1 s2) == foldm_back m (append s2 s1))
  = elim_monoid_laws m;
    foldm_back_append m s1 s2;
    foldm_back_append m s2 s1

#push-options "--fuel 2"
let foldm_back_singleton (#a:_) (m:CM.cm a) (x:a)
  : Lemma (foldm_back m (singleton x) == x)
  = elim_monoid_laws m
#pop-options

#push-options "--fuel 0"
let foldm_back3 #a (m:CM.cm a) (s1:seq a) (x:a) (s2:seq a)
  : Lemma (foldm_back m (S.append s1 (cons x s2)) ==
           m.mult x (foldm_back m (S.append s1 s2)))
  = calc (==)
    {
      foldm_back m (S.append s1 (cons x s2));
      (==) { foldm_back_append m s1 (cons x s2) }
      m.mult (foldm_back m s1) (foldm_back m (cons x s2));
      (==) { foldm_back_append m (singleton x) s2 }
      m.mult (foldm_back m s1) (m.mult (foldm_back m (singleton x)) (foldm_back m s2));
      (==) { foldm_back_singleton m x }
      m.mult (foldm_back m s1) (m.mult x (foldm_back m s2));
      (==) { elim_monoid_laws m }
      m.mult x (m.mult (foldm_back m s1) (foldm_back m s2));
      (==) { foldm_back_append m s1 s2 }
      m.mult x (foldm_back m (S.append s1 s2));
    }
#pop-options


let remove_i #a (s:seq a) (i:nat{i < S.length s})
  : a & seq a
  = let s0, s1 = split s i in
    head s1, append s0 (tail s1)

let shift_perm' #a
               (s0 s1:seq a)
               (_:squash (S.length s0 == S.length s1 /\ S.length s0 > 0))
               (p:seqperm s0 s1)
  : Tot (seqperm (fst (un_build s0))
                 (snd (remove_i s1 (p (S.length s0 - 1)))))
  = reveal_is_permutation s0 s1 p;
    let s0', last = un_build s0 in
    let n = S.length s0' in
    let p' (i:nat{ i < n })
        : j:nat{ j < n }
       = if p i < p n then p i else p i - 1
    in
    let _, s1' = remove_i s1 (p n) in
    reveal_is_permutation_nopats s0' s1' p';
    p'

let shift_perm #a
               (s0 s1:seq a)
               (_:squash (S.length s0 == S.length s1 /\ S.length s0 > 0))
               (p:seqperm s0 s1)
  : Pure (seqperm (fst (un_build s0))
                  (snd (remove_i s1 (p (S.length s0 - 1)))))
         (requires True)
         (ensures fun _ -> let n = S.length s0 - 1 in
                        S.index s1 (p n) ==
                        S.index s0 n)
  = reveal_is_permutation s0 s1 p;
    shift_perm' s0 s1 () p

let seqperm_len #a (s0 s1:seq a)
                   (p:seqperm s0 s1)
  : Lemma
    (ensures S.length s0 == S.length s1)
  = reveal_is_permutation s0 s1 p

let rec foldm_back_perm #a m s0 s1 p
  : Lemma
    (ensures foldm_back m s0  == foldm_back m s1)
    (decreases (S.length s0))
  = seqperm_len s0 s1 p;
    if S.length s0 = 0 then (
      assert (S.equal s0 s1)
    )
    else (
      let n0 = S.length s0 - 1 in
      let prefix, last = un_build s0 in
      let prefix', suffix' = split s1 (p n0) in
      let last', suffix' = suffix' $@ 0, drop suffix' 1 in
      let s1' = snd (remove_i s1 (p n0)) in
      let p' : seqperm prefix s1' = shift_perm s0 s1 () p in
      assert (last == last');
      calc
      (==)
      {
        foldm_back m s1;
        (==) { assert (s1 `S.equal` S.append prefix' (cons last' suffix')) }
        foldm_back m (S.append prefix' (cons last' suffix'));
        (==) { foldm_back3 m prefix' last' suffix' }
        m.mult last' (foldm_back m (append prefix' suffix'));
        (==) { assert (S.equal (append prefix' suffix') s1') }
        m.mult last' (foldm_back m s1');
        (==) { foldm_back_perm m prefix s1' p' }
        m.mult last' (foldm_back m prefix);
        (==) { }
        foldm_back m s0;
      }
    )
