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
module FStar.Seq.Permutation
open FStar.Seq
open FStar.Calc

[@@"opaque_to_smt"]
let is_permutation (#a:Type) (s0:seq a) (s1:seq a) (f:index_fun s0) =
  Seq.length s0 == Seq.length s1 /\
  (forall x y. // {:pattern f x; f y}
  x <> y ==> f x <> f y) /\
  (forall (i:nat{i < Seq.length s0}). // {:pattern (Seq.index s1 (f i))}
      Seq.index s0 i == Seq.index s1 (f i))

let reveal_is_permutation #a (s0 s1:seq a) (f:index_fun s0)
  = reveal_opaque (`%is_permutation) (is_permutation s0 s1 f)

let reveal_is_permutation_nopats (#a:Type) (s0 s1:seq a) (f:index_fun s0)
  : Lemma (is_permutation s0 s1 f <==>

           Seq.length s0 == Seq.length s1 /\

           (forall x y. x <> y ==> f x <> f y) /\

           (forall (i:nat{i < Seq.length s0}).
              Seq.index s0 i == Seq.index s1 (f i)))
   = reveal_is_permutation s0 s1 f

let split3_index (#a:eqtype) (s0:seq a) (x:a) (s1:seq a) (j:nat)
  : Lemma
    (requires j < Seq.length (Seq.append s0 s1))
    (ensures (
      let s = Seq.append s0 (Seq.cons x s1) in
      let s' = Seq.append s0 s1 in
      let n = Seq.length s0 in
      if j < n then Seq.index s' j == Seq.index s j
      else Seq.index s' j == Seq.index s (j + 1)
    ))
  = let n = Seq.length (Seq.append s0 s1) in
    if j < n then ()
    else ()

#push-options "--fuel 2 --ifuel 0 --z3rlimit_factor 2"
let rec find (#a:eqtype) (x:a) (s:seq a{ count x s > 0 })
  : Tot (frags:(seq a & seq a) {
      let s' = Seq.append (fst frags) (snd frags) in
      let n = Seq.length (fst frags) in
      s `Seq.equal` Seq.append (fst frags) (Seq.cons x (snd frags))
    }) (decreases (Seq.length s))
  = if Seq.head s = x
    then Seq.empty, Seq.tail s
    else (
      let pfx, sfx = find x (Seq.tail s) in
      assert (Seq.equal (Seq.tail s)
                        (Seq.append pfx (Seq.cons x sfx)));
      assert (Seq.equal s
                        (Seq.cons (Seq.head s) (Seq.tail s)));
      Seq.cons (Seq.head s) pfx, sfx
    )
#pop-options

#push-options "--fuel 2 --ifuel 0 --z3rlimit_factor 10"
let rec permutation_from_equal_counts (#a:eqtype) (s0:seq a) (s1:seq a{(forall x. count x s0 == count x s1)})
  : Tot (seqperm s0 s1)//index_fun s0 { is_permutation s0 s1 f })
        (decreases (Seq.length s0))
  = if Seq.length s0 = 0
    then (
      let f : index_fun s0 = fun i -> i in
      reveal_is_permutation_nopats s0 s1 f;
      if Seq.length s1 = 0 then f
      else (assert (count (Seq.head s1) s1 > 0); f)
    ) else (
      assert (count (Seq.head s0) s0 > 0);
      let pfx, sfx = find (Seq.head s0) s1 in
      introduce forall x. count x (Seq.tail s0) == count x (Seq.append pfx sfx)
      with (
        lemma_append_count_aux x pfx sfx;
        lemma_append_count_aux x (Seq.create 1 (Seq.head s0)) sfx;
        lemma_append_count_aux x pfx (Seq.cons (Seq.head s0) sfx)
      );
      let s1' = (Seq.append pfx sfx) in
      let f' = permutation_from_equal_counts (Seq.tail s0) s1'  in
      reveal_is_permutation_nopats (Seq.tail s0) s1' f';
      let n = Seq.length pfx in
      let f : index_fun s0 =
          fun i -> if i = 0
                then n
                else if f' (i - 1) < n
                then f' (i - 1)
                else f' (i - 1) + 1
      in
      assert (Seq.length s0 == Seq.length s1);
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


module CE = FStar.Algebra.CommMonoid.Equiv

let elim_monoid_laws #a #eq (m:CE.cm a eq)
  : Lemma (
          (forall x y. {:pattern m.mult x y}  eq.eq (m.mult x y) (m.mult y x)) /\
          (forall x y z.{:pattern (m.mult x (m.mult y z))} eq.eq (m.mult x (m.mult y z)) (m.mult (m.mult x y) z)) /\
          (forall x.{:pattern (m.mult x m.unit)} eq.eq (m.mult x m.unit) x)
    )
  = introduce forall x y. eq.eq (m.mult x y) (m.mult y x)
    with ( m.commutativity x y );

    introduce forall x y z. eq.eq (m.mult x (m.mult y z)) (m.mult (m.mult x y) z)
    with ( m.associativity x y z;
           eq.symmetry (m.mult (m.mult x y) z) (m.mult x (m.mult y z)) );

    introduce forall x. eq.eq (m.mult x m.unit) x
    with ( CE.right_identity eq m x )

let rec foldm_snoc_unit_seq (#a:Type) (#eq:CE.equiv a) (m:CE.cm a eq) (s:Seq.seq a)
  : Lemma (requires Seq.equal s (Seq.create (Seq.length s) m.unit))
          (ensures eq.eq (foldm_snoc m s) m.unit)
          (decreases Seq.length s)
  = CE.elim_eq_laws eq;
    elim_monoid_laws m;
    if Seq.length s = 0
    then ()
    else let s_tl, _ = un_snoc s in
         foldm_snoc_unit_seq m s_tl

#push-options "--fuel 2"
let foldm_snoc_singleton (#a:_) #eq (m:CE.cm a eq) (x:a)
  : Lemma (eq.eq (foldm_snoc m (Seq.create 1 x)) x)
  = elim_monoid_laws m
#pop-options

let x_yz_to_y_xz #a #eq (m:CE.cm a eq) (x y z:a)
  : Lemma ((x `m.mult` (y `m.mult` z))
             `eq.eq`
           (y `m.mult` (x `m.mult` z)))
  = CE.elim_eq_laws eq;
    elim_monoid_laws m;  
    calc (eq.eq) {
      x `m.mult` (y `m.mult` z);
      (eq.eq) { m.commutativity x (y `m.mult` z) }
      (y `m.mult` z) `m.mult` x;
      (eq.eq) { m.associativity y z x }
      y `m.mult` (z `m.mult` x);
      (eq.eq) { m.congruence y (z `m.mult` x) y (x `m.mult` z) }
      y `m.mult` (x `m.mult` z);
    }
  
#push-options "--fuel 1 --ifuel 0 --z3rlimit_factor 2"
let rec foldm_snoc_append #a #eq (m:CE.cm a eq) (s1 s2: seq a)
  : Lemma
    (ensures eq.eq (foldm_snoc m (append s1 s2))
                   (m.mult (foldm_snoc m s1) (foldm_snoc m s2)))
    (decreases (Seq.length s2))
  = CE.elim_eq_laws eq;
    elim_monoid_laws m;
    if Seq.length s2 = 0
    then assert (Seq.append s1 s2 `Seq.equal` s1)
    else (
      let s2', last = Seq.un_snoc s2 in
      calc (eq.eq)
      {
        foldm_snoc m (append s1 s2);
        (eq.eq) { assert (Seq.equal (append s1 s2)
                         (Seq.snoc (append s1 s2') last)) }
        foldm_snoc m (Seq.snoc (append s1 s2') last);
        (eq.eq) { assert (Seq.equal (fst (Seq.un_snoc (append s1 s2))) (append s1 s2')) }
        
        m.mult last (foldm_snoc m (append s1 s2'));
        (eq.eq) { foldm_snoc_append m s1 s2';
                  m.congruence last (foldm_snoc m (append s1 s2'))
                               last (m.mult (foldm_snoc m s1) (foldm_snoc m s2')) }
        m.mult last (m.mult (foldm_snoc m s1) (foldm_snoc m s2'));
        (eq.eq) { x_yz_to_y_xz m last (foldm_snoc m s1) (foldm_snoc m s2') }
        m.mult (foldm_snoc m s1) (m.mult last (foldm_snoc m s2'));
        (eq.eq) { }
        m.mult (foldm_snoc m s1) (foldm_snoc m s2);
      })

let foldm_snoc_sym #a #eq (m:CE.cm a eq) (s1 s2: seq a)
  : Lemma
    (ensures eq.eq (foldm_snoc m (append s1 s2)) (foldm_snoc m (append s2 s1)))
  = CE.elim_eq_laws eq;
    elim_monoid_laws m;
    foldm_snoc_append m s1 s2;
    foldm_snoc_append m s2 s1

#push-options "--fuel 0"
let foldm_snoc3 #a #eq (m:CE.cm a eq) (s1:seq a) (x:a) (s2:seq a)
  : Lemma (eq.eq (foldm_snoc m (Seq.append s1 (Seq.cons x s2)))
                 (m.mult x (foldm_snoc m (Seq.append s1 s2))))
  = CE.elim_eq_laws eq;
    elim_monoid_laws m;
    calc (eq.eq)
    {
      foldm_snoc m (Seq.append s1 (Seq.cons x s2));
      (eq.eq) { foldm_snoc_append m s1 (Seq.cons x s2) }
      m.mult (foldm_snoc m s1) (foldm_snoc m (Seq.cons x s2));
      (eq.eq) { foldm_snoc_append m (Seq.create 1 x) s2;
                m.congruence (foldm_snoc m s1)
                             (foldm_snoc m (Seq.cons x s2))
                             (foldm_snoc m s1)
                             (m.mult (foldm_snoc m (Seq.create 1 x)) (foldm_snoc m s2)) }
      m.mult (foldm_snoc m s1) (m.mult (foldm_snoc m (Seq.create 1 x)) (foldm_snoc m s2));
      (eq.eq) { foldm_snoc_singleton m x;
                m.congruence (foldm_snoc m (Seq.create 1 x))
                             (foldm_snoc m s2)
                             x
                             (foldm_snoc m s2);
                m.congruence (foldm_snoc m s1)
                             (m.mult (foldm_snoc m (Seq.create 1 x)) (foldm_snoc m s2))
                             (foldm_snoc m s1)
                             (m.mult x (foldm_snoc m s2)) }
      m.mult (foldm_snoc m s1) (m.mult x (foldm_snoc m s2));
      (eq.eq) { x_yz_to_y_xz m (foldm_snoc m s1) x (foldm_snoc m s2) }
      m.mult x (m.mult (foldm_snoc m s1) (foldm_snoc m s2));
      (eq.eq) { foldm_snoc_append m s1 s2;
                m.congruence x
                             (m.mult (foldm_snoc m s1) (foldm_snoc m s2))
                             x
                             (foldm_snoc m (Seq.append s1 s2)) }
      m.mult x (foldm_snoc m (Seq.append s1 s2));
    }
#pop-options


let remove_i #a (s:seq a) (i:nat{i < Seq.length s})
  : a & seq a
  = let s0, s1 = Seq.split s i in
    Seq.head s1, Seq.append s0 (Seq.tail s1)

#push-options "--using_facts_from '* -FStar.Seq.Properties.slice_slice'"
let shift_perm' #a
               (s0 s1:seq a)
               (_:squash (Seq.length s0 == Seq.length s1 /\ Seq.length s0 > 0))
               (p:seqperm s0 s1)
  : Tot (seqperm (fst (Seq.un_snoc s0))
                 (snd (remove_i s1 (p (Seq.length s0 - 1)))))
  = reveal_is_permutation s0 s1 p;
    let s0', last = Seq.un_snoc s0 in
    let n = Seq.length s0' in
    let p' (i:nat{ i < n })
        : j:nat{ j < n }
       = if p i < p n then p i else p i - 1
    in
    let _, s1' = remove_i s1 (p n) in
    reveal_is_permutation_nopats s0' s1' p';
    p'
#pop-options

let shift_perm #a
               (s0 s1:seq a)
               (_:squash (Seq.length s0 == Seq.length s1 /\ Seq.length s0 > 0))
               (p:seqperm s0 s1)
  : Pure (seqperm (fst (Seq.un_snoc s0))
                  (snd (remove_i s1 (p (Seq.length s0 - 1)))))
         (requires True)
         (ensures fun _ -> let n = Seq.length s0 - 1 in
                        Seq.index s1 (p n) ==
                        Seq.index s0 n)
  = reveal_is_permutation s0 s1 p;
    shift_perm' s0 s1 () p

let seqperm_len #a (s0 s1:seq a)
                   (p:seqperm s0 s1)
  : Lemma
    (ensures Seq.length s0 == Seq.length s1)
  = reveal_is_permutation s0 s1 p

let eq2_eq #a (eq:CE.equiv a) (x y:a)
  : Lemma (requires x == y)
          (ensures x `eq.eq` y)
  = eq.reflexivity x

(* The sequence indexing lemmas make this quite fiddly *)
#push-options "--z3rlimit_factor 2 --fuel 1 --ifuel 0"
let rec foldm_snoc_perm #a #eq m s0 s1 p
  : Lemma
    (ensures eq.eq (foldm_snoc m s0) (foldm_snoc m s1))
    (decreases (Seq.length s0))
  = //for getting calc chain to compose
    CE.elim_eq_laws eq;
    seqperm_len s0 s1 p;
    if Seq.length s0 = 0 then (
      assert (Seq.equal s0 s1);
      eq2_eq eq (foldm_snoc m s0) (foldm_snoc m s1)
    )
    else (
      let n0 = Seq.length s0 - 1 in
      let prefix, last = Seq.un_snoc s0 in
      let prefix', suffix' = Seq.split s1 (p n0) in
      let last', suffix' = Seq.head suffix', Seq.tail suffix' in
      let s1' = snd (remove_i s1 (p n0)) in
      let p' : seqperm prefix s1' = shift_perm s0 s1 () p in
      assert (last == last');
      calc
      (eq.eq)
      {
        foldm_snoc m s1;
        (eq.eq) { assert (s1 `Seq.equal` Seq.append prefix' (Seq.cons last' suffix'));
                  eq2_eq eq (foldm_snoc m s1)
                            (foldm_snoc m (Seq.append prefix' (Seq.cons last' suffix'))) }
        foldm_snoc m (Seq.append prefix' (Seq.cons last' suffix'));
        (eq.eq) { foldm_snoc3 m prefix' last' suffix' }
        m.mult last' (foldm_snoc m (append prefix' suffix'));
        (eq.eq) { assert (Seq.equal (append prefix' suffix') s1');
                  eq2_eq eq (m.mult last' (foldm_snoc m (append prefix' suffix')))
                            (m.mult last' (foldm_snoc m s1')) }
        m.mult last' (foldm_snoc m s1');
        (eq.eq) { foldm_snoc_perm m prefix s1' p';
                  eq.symmetry (foldm_snoc m prefix) (foldm_snoc m s1');
                  eq.reflexivity last';
                  m.congruence last'
                               (foldm_snoc m s1')
                               last'
                               (foldm_snoc m prefix) }
        m.mult last' (foldm_snoc m prefix);
        (eq.eq) { eq2_eq eq (m.mult last' (foldm_snoc m prefix))
                            (foldm_snoc m s0) }
        foldm_snoc m s0;
      };
      eq.symmetry (foldm_snoc m s1) (foldm_snoc m s0))
#pop-options
