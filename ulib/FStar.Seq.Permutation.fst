(*
   Copyright 2021-2022 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Authors: N. Swamy, A. Rastogi, A. Rozanov
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

let introduce_is_permutation (#a:Type) (s0:seq a) (s1:seq a)
                             (f:index_fun s0)
                             (_:squash (Seq.length s0 == Seq.length s1))
                             (_:squash (forall x y. x <> y ==> f x <> f y))
                             (_:squash (forall (i:nat{i < Seq.length s0}). Seq.index s0 i == Seq.index s1 (f i)))
   : Lemma
     (ensures
       is_permutation s0 s1 f)
   = reveal_is_permutation_nopats s0 s1 f

let reveal_is_permutation_pats (#a:Type) (s0 s1:seq a) (f:index_fun s0)
  : Lemma (is_permutation s0 s1 f <==>

           Seq.length s0 == Seq.length s1 /\

           (forall x y. {:pattern f x; f y } x <> y ==> f x <> f y) /\

           (forall (i:nat{i < Seq.length s0}). {:pattern (Seq.index s0 i)}
              Seq.index s0 i == Seq.index s1 (f i)))
   = reveal_is_permutation s0 s1 f

let adapt_index_fun (s:Seq.seq 'a { Seq.length s > 0 })
                    (f:index_fun (Seq.tail s))
                    (n:nat{n < Seq.length s})
  : index_fun s
  = fun i -> if i = 0
          then n
          else if f (i - 1) < n
          then f (i - 1)
          else f (i - 1) + 1

let count_singleton_one (#a:eqtype) (x:a)
  : Lemma (count x (Seq.create 1 x) == 1)
  = ()
let count_singleton_zero (#a:eqtype) (x y:a)
  : Lemma (x =!= y ==> count x (Seq.create 1 y) == 0)
  = ()
let equal_counts_empty (#a:eqtype) (s0 s1:seq a)
  : Lemma
    (requires Seq.length s0 == 0 /\ (forall x. count x s0 == count x s1))
    (ensures  Seq.length s1 == 0)
  = if Seq.length s1 > 0 then
    assert (count (Seq.head s1) s1 > 0)
let count_head (#a:eqtype) (x:seq a{ Seq.length x > 0 })
  : Lemma (count (Seq.head x) x > 0)
  = ()


#push-options "--fuel 0"
#restart-solver
let rec permutation_from_equal_counts (#a:eqtype) (s0:seq a) (s1:seq a{(forall x. count x s0 == count x s1)})
  : Tot (seqperm s0 s1)
        (decreases (Seq.length s0))
  = if Seq.length s0 = 0
    then (
      let f : index_fun s0 = fun i -> i in
      reveal_is_permutation_pats s0 s1 f;
      equal_counts_empty s0 s1;
      f
    ) else (
      count_head s0;
      assert (count (Seq.head s0) s0 > 0);
      let pfx, sfx = find (Seq.head s0) s1 in
      introduce forall x. count x (Seq.tail s0) == count x (Seq.append pfx sfx)
      with (
        if x = Seq.head s0
        then  (
          calc (eq2 #int) {
            count x (Seq.tail s0) <: int;
          (==) {
                 assert (s0 `Seq.equal` Seq.cons (Seq.head s0) (Seq.tail s0));
                 lemma_append_count_aux (Seq.head s0) (Seq.create 1 (Seq.head s0)) (Seq.tail s0);
                 count_singleton_one x
               }
            count x s0 - 1 <: int;
          (==) {}
            count x s1 - 1 <: int;
          (==) {}
            count x (Seq.append pfx (Seq.cons (Seq.head s0) sfx)) - 1 <: int;
          (==) { lemma_append_count_aux x pfx (Seq.cons (Seq.head s0) sfx) }
            count x pfx + count x (Seq.cons (Seq.head s0) sfx) - 1 <: int;
          (==) { lemma_append_count_aux x (Seq.create 1 (Seq.head s0)) sfx }
            count x pfx + (count x (Seq.create 1 (Seq.head s0)) + count x sfx) - 1 <: int;
          (==) { count_singleton_one x }
            count x pfx + count x sfx <: int;
          (==) { lemma_append_count_aux x pfx sfx }
            count x (Seq.append pfx sfx) <: int;
          }
        )
        else (
          calc (==) {
            count x (Seq.tail s0);
           (==) {
                  assert (s0 `Seq.equal` Seq.cons (Seq.head s0) (Seq.tail s0));
                  lemma_append_count_aux x (Seq.create 1 (Seq.head s0)) (Seq.tail s0);
                  count_singleton_zero x (Seq.head s0)
                }
            count x s0;
           (==) { }
            count x s1;
           (==) { }
            count x (Seq.append pfx (Seq.cons (Seq.head s0) sfx));
           (==) { lemma_append_count_aux x pfx (Seq.cons (Seq.head s0) sfx) }
            count x pfx + count x (Seq.cons (Seq.head s0) sfx);
          (==) { lemma_append_count_aux x (Seq.create 1 (Seq.head s0)) sfx }
            count x pfx + (count x (Seq.create 1 (Seq.head s0)) + count x sfx) ;
          (==) { count_singleton_zero x (Seq.head s0) }
            count x pfx + count x sfx;
          (==) { lemma_append_count_aux x pfx sfx }
            count x (Seq.append pfx sfx);
          }
        )
      );
      let s1' = (Seq.append pfx sfx) in
      let f' = permutation_from_equal_counts (Seq.tail s0) s1'  in
      reveal_is_permutation_pats (Seq.tail s0) s1' f';
      let n = Seq.length pfx in
      let f : index_fun s0 = adapt_index_fun s0 f' n in
      assert (Seq.length s0 == Seq.length s1);
      let len_eq : squash (Seq.length s0 == Seq.length s1) = () in
      assert (forall x y. x <> y ==> f' x <> f' y);
      let neq =
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
        )
      in
      let perm_prop =
        introduce forall (i:nat{i < Seq.length s0}). Seq.index s0 i == Seq.index s1 (f i)
        with (
          if i = 0 then ()
          else if f' (i - 1) < n
          then (
            assert (f i == f' (i - 1));
            assert (Seq.index (Seq.tail s0) (i - 1) ==
                    Seq.index s1' (f' (i - 1)))
          )
          else (
            assert (f i = f' (i - 1) + 1);
            assert (Seq.index (Seq.tail s0) (i - 1) ==
                    Seq.index s1' (f' (i - 1)))
          )
        )
      in
      introduce_is_permutation s0 s1 f len_eq neq perm_prop;
      f)
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
#pop-options

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
      let prefix', suffix0 = Seq.split s1 (p n0) in
      assert (Seq.equal s1 (Seq.append prefix' suffix0));
      let last', suffix' = Seq.head suffix0, Seq.tail suffix0 in
      assert (Seq.cons last' suffix' `Seq.equal` suffix0);
      assert (s1 `Seq.equal` Seq.append prefix' (Seq.cons last' suffix'));
      let s1' = snd (remove_i s1 (p n0)) in
      let p' : seqperm prefix s1' = shift_perm s0 s1 () p in
      assert (last == last');
      calc
      (eq.eq)
      {
        foldm_snoc m s1;
        (eq.eq) { eq2_eq eq (foldm_snoc m s1)
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

////////////////////////////////////////////////////////////////////////////////
// foldm_snoc_split
////////////////////////////////////////////////////////////////////////////////

(* Some utilities to introduce associativity-commutativity reasoning on
   CM using quantified formulas with patterns.

   Use these with care, since with large terms the SMT solver may end up
   with an explosion of instantiations
*)
let cm_associativity #c #eq (cm: CE.cm c eq)
  : Lemma (forall (x y z:c). {:pattern (x `cm.mult` y `cm.mult` z)}
              (x `cm.mult` y `cm.mult` z) `eq.eq` (x `cm.mult` (y `cm.mult` z)))
  = Classical.forall_intro_3 (Classical.move_requires_3 cm.associativity)

let cm_commutativity #c #eq (cm: CE.cm c eq)
  : Lemma (forall (x y:c). {:pattern (x `cm.mult` y)}
              (x `cm.mult` y) `eq.eq` (y `cm.mult` x))
  = Classical.forall_intro_2 (Classical.move_requires_2 cm.commutativity)

(* A utility to introduce the equivalence relation laws into the context.
   FStar.Algebra.CommutativeMonoid provides something similar, but this
   version provides a more goal-directed pattern for transitivity.
   We should consider changing FStar.Algebra.CommutativeMonoid *)
let elim_eq_laws #a (eq:CE.equiv a)
  : Lemma (
          (forall x.{:pattern (x `eq.eq` x)} x `eq.eq` x) /\
          (forall x y.{:pattern (x `eq.eq` y)} x `eq.eq` y ==> y `eq.eq` x) /\
          (forall x y z.{:pattern eq.eq x y; eq.eq x z} (x `eq.eq` y /\ y `eq.eq` z) ==> x `eq.eq` z)
          )
   = CE.elim_eq_laws eq

let fold_decomposition_aux #c #eq (cm: CE.cm c eq)
                           (n0: int)
                           (nk: int{nk=n0})
                           (expr1 expr2: (ifrom_ito n0 nk) -> c)
  : Lemma (foldm_snoc cm (init (closed_interval_size n0 nk)
                               (init_func_from_expr (func_sum cm expr1 expr2) n0 nk)) `eq.eq`
           cm.mult (foldm_snoc cm (init (closed_interval_size n0 nk) (init_func_from_expr expr1 n0 nk)))
                   (foldm_snoc cm (init (closed_interval_size n0 nk) (init_func_from_expr expr2 n0 nk))))
  = elim_eq_laws eq;
    let sum_of_funcs (i: under (closed_interval_size n0 nk))
      = expr1 (n0+i) `cm.mult` expr2 (n0+i) in
    lemma_eq_elim (init (closed_interval_size n0 nk) sum_of_funcs)
                  (create 1 (expr1 n0 `cm.mult` expr2 n0));
    foldm_snoc_singleton cm (expr1 n0 `cm.mult` expr2 n0);
    let ts = (init (closed_interval_size n0 nk) sum_of_funcs) in
    let ts1 = (init (nk+1-n0) (fun i -> expr1 (n0+i))) in
    let ts2 = (init (nk+1-n0) (fun i -> expr2 (n0+i))) in
    assert (foldm_snoc cm ts `eq.eq` sum_of_funcs (nk-n0)); // this assert speeds up the proof.
    foldm_snoc_singleton cm (expr1 nk);
    foldm_snoc_singleton cm (expr2 nk);
    cm.congruence (foldm_snoc cm ts1) (foldm_snoc cm ts2) (expr1 nk) (expr2 nk)

let aux_shuffle_lemma #c #eq (cm: CE.cm c eq)
                                     (s1 s2 l1 l2: c)
  : Lemma (((s1 `cm.mult` s2) `cm.mult` (l1 `cm.mult` l2)) `eq.eq`
           ((s1 `cm.mult` l1) `cm.mult` (s2 `cm.mult` l2)))
  = elim_eq_laws eq;
    cm_commutativity cm;
    cm_associativity cm;
    let (+) = cm.mult in
    cm.congruence (s1+s2) l1 (s2+s1) l1;
    cm.congruence ((s1+s2)+l1) l2 ((s2+s1)+l1) l2;
    cm.congruence ((s2+s1)+l1) l2 (s2+(s1+l1)) l2;
    cm.congruence (s2+(s1+l1)) l2 ((s1+l1)+s2) l2


#push-options "--ifuel 0 --fuel 1 --z3rlimit 40"
(* This proof is quite delicate, for several reasons:
     - It's working with higher order functions that are non-trivially dependently typed,
       notably on the ranges the ranges of indexes they manipulate

     - When using the induction hypothesis (i.e., on a recursive call), what we get
       is a property about the function at a different type, i.e., `range_count n0 (nk - 1)`.

     - If left to the SMT solver alone, these higher order functions
       at slightly different types cannot be proven equal and the
       proof fails, often mysteriously.

     - To have something more robust, I rewrote this function to
       return a squash proof, and then to coerce this proof to the
       type needed, where the F* unififer/normalization machinery can
       help, rather than leaving it purely to SMT, which is what
       happens when the property is states as a postcondition of a
       Lemma
*)
let rec foldm_snoc_split' #c #eq (cm: CE.cm c eq)
                           (n0: int)
                           (nk: not_less_than n0)
                           (expr1 expr2: (ifrom_ito n0 nk) -> c)
  : Tot (squash (foldm_snoc cm (init (closed_interval_size n0 nk) (init_func_from_expr (func_sum cm expr1 expr2) n0 nk)) `eq.eq`
                 cm.mult (foldm_snoc cm (init (closed_interval_size n0 nk) (init_func_from_expr expr1 n0 nk)))
                         (foldm_snoc cm (init (closed_interval_size n0 nk) (init_func_from_expr expr2 n0 nk)))))
        (decreases nk-n0)
  = if (nk=n0)
    then fold_decomposition_aux cm n0 nk expr1 expr2
    else (
      cm_commutativity cm;
      elim_eq_laws eq;
      let lfunc_up_to (nf: ifrom_ito n0 nk) = init_func_from_expr (func_sum cm expr1 expr2) n0 nf in
      let range_count = closed_interval_size in
      let full_count = range_count n0 nk in
      let sub_count = range_count n0 (nk-1) in
      let fullseq = init full_count (lfunc_up_to nk) in
      let rfunc_1_up_to (nf: ifrom_ito n0 nk) = init_func_from_expr expr1 n0 nf in
      let rfunc_2_up_to (nf: ifrom_ito n0 nk) = init_func_from_expr expr2 n0 nf in
      let fullseq_r1 = init full_count (rfunc_1_up_to nk) in
      let fullseq_r2 = init full_count (rfunc_2_up_to nk) in
      let subseq = init sub_count (lfunc_up_to nk) in
      let subfold = foldm_snoc cm subseq in
      let last = lfunc_up_to nk sub_count in
      lemma_eq_elim (fst (un_snoc fullseq)) subseq; // subseq is literally (liat fullseq)
      let fullfold = foldm_snoc cm fullseq in
      let subseq_r1 = init sub_count (rfunc_1_up_to nk) in
      let subseq_r2 = init sub_count (rfunc_2_up_to nk) in
      lemma_eq_elim (fst (un_snoc fullseq_r1)) subseq_r1; // subseq is literally (liat fullseq)
      lemma_eq_elim (fst (un_snoc fullseq_r2)) subseq_r2; // subseq is literally (liat fullseq)
      lemma_eq_elim (init sub_count (lfunc_up_to nk)) subseq;
      lemma_eq_elim (init sub_count (lfunc_up_to (nk-1))) subseq;
      lemma_eq_elim subseq_r1 (init sub_count (rfunc_1_up_to (nk-1)));
      lemma_eq_elim subseq_r2 (init sub_count (rfunc_2_up_to (nk-1)));
      let fullfold_r1 = foldm_snoc cm fullseq_r1 in
      let fullfold_r2 = foldm_snoc cm fullseq_r2 in
      let subfold_r1 = foldm_snoc cm subseq_r1 in
      let subfold_r2 = foldm_snoc cm subseq_r2 in
      cm.congruence  (foldm_snoc cm (init sub_count (rfunc_1_up_to (nk-1))))
                     (foldm_snoc cm (init sub_count (rfunc_2_up_to (nk-1))))
                     subfold_r1 subfold_r2;
      let last_r1 = rfunc_1_up_to nk sub_count in
      let last_r2 = rfunc_2_up_to nk sub_count in
      let nk' = nk - 1 in
      (* here's the nasty bit with where we have to massage the proof from the induction hypothesis *)
      let ih
        : squash ((foldm_snoc cm (init (range_count n0 nk') (init_func_from_expr #_ #n0 #nk' (func_sum #(ifrom_ito n0 nk') cm expr1 expr2) n0 nk')) `eq.eq`
              cm.mult (foldm_snoc cm (init (range_count n0 nk') (init_func_from_expr #_ #n0 #nk' expr1 n0 nk')))
                      (foldm_snoc cm (init (range_count n0 nk') (init_func_from_expr #_ #n0 #nk' expr2 n0 nk')))))
        = foldm_snoc_split' cm n0 nk' expr1 expr2
      in
      calc (==) {
        subfold;
      == { }
        foldm_snoc cm subseq;
      == { assert (Seq.equal subseq
                             (init (range_count n0 nk')
                                   (init_func_from_expr #_ #n0 #nk'
                                      (func_sum #(ifrom_ito n0 nk') cm expr1 expr2) n0 nk'))) }
        foldm_snoc cm (init (range_count n0 nk')
                            (init_func_from_expr #_ #n0 #nk'
                               (func_sum #(ifrom_ito n0 nk') cm expr1 expr2) n0 nk'));
      };
      assert (Seq.equal subseq_r1 (init (range_count n0 nk') (init_func_from_expr #_ #n0 #nk' expr1 n0 nk')));
      assert (Seq.equal subseq_r2 (init (range_count n0 nk') (init_func_from_expr #_ #n0 #nk' expr2 n0 nk')));
      let _ : squash (subfold `eq.eq` (subfold_r1 `cm.mult` subfold_r2)) = ih in
      cm.congruence subfold last (subfold_r1 `cm.mult` subfold_r2) last;
      aux_shuffle_lemma cm subfold_r1 subfold_r2 (rfunc_1_up_to nk sub_count) (rfunc_2_up_to nk sub_count);
      cm.congruence (subfold_r1 `cm.mult` (rfunc_1_up_to nk sub_count)) (subfold_r2 `cm.mult` (rfunc_2_up_to nk sub_count))
                    (foldm_snoc cm fullseq_r1) (foldm_snoc cm fullseq_r2)
  )
#pop-options

/// Finally, package the proof up into a Lemma, as expected by the interface
let foldm_snoc_split #c #eq (cm: CE.cm c eq)
                           (n0: int)
                           (nk: not_less_than n0)
                           (expr1 expr2: (ifrom_ito n0 nk) -> c)
  = foldm_snoc_split' cm n0 nk expr1 expr2

open FStar.Seq.Equiv

let rec foldm_snoc_equality #c #eq (add: CE.cm c eq) (s t: seq c)
  : Lemma (requires length s == length t /\ eq_of_seq eq s t)
          (ensures foldm_snoc add s `eq.eq` foldm_snoc add t)
          (decreases length s) = 
  if length s = 0 then (
    assert_norm (foldm_snoc add s == add.unit);
    assert_norm (foldm_snoc add t == add.unit);
    eq.reflexivity add.unit
  ) 
  else (
    let sliat, slast = un_snoc s in
    let tliat, tlast = un_snoc t in
    eq_of_seq_unsnoc eq (length s) s t;
    foldm_snoc_equality add sliat tliat; 
    add.congruence slast (foldm_snoc add sliat)
                   tlast (foldm_snoc add tliat) 
  )
 
let foldm_snoc_split_seq #c #eq (add: CE.cm c eq) 
                     (s: seq c) (t: seq c{length s == length t})
                     (sum_seq: seq c{length sum_seq == length s})
                     (proof: (i: under (length s)) -> Lemma ((index s i `add.mult` index t i)
                       `eq.eq` (index sum_seq i)))
  : Lemma ((foldm_snoc add s `add.mult` foldm_snoc add t) `eq.eq`
           (foldm_snoc add sum_seq)) =
  if length s = 0 then add.identity add.unit 
  else  
    let n = length s in
    let index_1 (i:under n) = index s i in
    let index_2 (i:under n) = index t i in
    let nk = (n-1) in
    assert (n == closed_interval_size 0 nk);
    let index_sum = func_sum add index_1 index_2 in
    let expr1 = init_func_from_expr #c #0 #(n-1) index_1 0 nk in
    let expr2 = init_func_from_expr #c #0 #(n-1) index_2 0 nk in
    let expr_sum = init_func_from_expr #c #0 #(n-1) index_sum 0 nk in
    Classical.forall_intro eq.reflexivity;
    Classical.forall_intro_2 (Classical.move_requires_2 eq.symmetry);
    Classical.forall_intro_3 (Classical.move_requires_3 eq.transitivity);
    foldm_snoc_split add 0 (n-1) index_1 index_2;
    assert (foldm_snoc add (init n (expr_sum)) `eq.eq`
           add.mult (foldm_snoc add (init n expr1)) (foldm_snoc add (init n expr2)));
    lemma_eq_elim s (init n expr1);
    lemma_eq_elim t (init n expr2);
    Classical.forall_intro proof; 
    eq_of_seq_from_element_equality eq (init n expr_sum) sum_seq;
    foldm_snoc_equality add (init n expr_sum) sum_seq ;
    
    assert (eq.eq (foldm_snoc add (init n expr_sum)) 
                  (foldm_snoc add sum_seq));
    assert (foldm_snoc add s == foldm_snoc add (init n expr1));
    assert (foldm_snoc add t == foldm_snoc add (init n expr2));
    assert (add.mult (foldm_snoc add s) (foldm_snoc add t) `eq.eq`
           foldm_snoc add (init n (expr_sum)));
    eq.transitivity (add.mult (foldm_snoc add s) (foldm_snoc add t))
                    (foldm_snoc add (init n (expr_sum)))
                    (foldm_snoc add sum_seq)

let rec foldm_snoc_of_equal_inits #c #eq #m (cm: CE.cm c eq) 
                                  (f: (under m) -> c) 
                                  (g: (under m) -> c)
  : Lemma (requires  (forall (i: under m). f i `eq.eq` g i))
          (ensures foldm_snoc cm (init m f) `eq.eq` 
                   foldm_snoc cm (init m g)) = 
  if m=0 then begin
    assert_norm (foldm_snoc cm (init m f) == cm.unit);
    assert_norm (foldm_snoc cm (init m g) == cm.unit);
    eq.reflexivity cm.unit 
  end else 
  if m=1 then begin
    foldm_snoc_singleton cm (f 0);
    foldm_snoc_singleton cm (g 0);
    eq.transitivity (foldm_snoc cm (init m f)) (f 0) (g 0);
    eq.symmetry (foldm_snoc cm (init m g)) (g 0);
    eq.transitivity (foldm_snoc cm (init m f)) 
                    (g 0)
                    (foldm_snoc cm (init m g))
  end else
    let fliat, flast = un_snoc (init m f) in
    let gliat, glast = un_snoc (init m g) in  
    foldm_snoc_of_equal_inits cm (fun (i: under (m-1)) -> f i) 
                                 (fun (i: under (m-1)) -> g i);
    lemma_eq_elim (init (m-1) (fun (i: under (m-1)) -> f i)) fliat;
    lemma_eq_elim (init (m-1) (fun (i: under (m-1)) -> g i)) gliat;
    cm.congruence flast (foldm_snoc cm fliat)
                  glast (foldm_snoc cm gliat)
                
