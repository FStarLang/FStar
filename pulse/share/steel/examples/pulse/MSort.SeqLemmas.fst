module MSort.SeqLemmas

open FStar.Ghost
module S = FStar.Seq

assume val sort : Seq.seq int -> Seq.seq int
assume val sorted : Seq.seq int -> bool
assume val sort_is_sorted (s:Seq.seq int) : Lemma (sorted (sort s))
assume val sort_len (s:Seq.seq int)
  : Lemma (S.length (sort s) == S.length s)
          [SMTPat (S.length (sort s))]

assume val singl_is_sorted (s : S.seq int)
  : Lemma (requires S.length s < 2)
          (ensures s == sort s)

type seq_view a =
  | Nil
  | Cons : a -> S.seq a -> seq_view a

let view #a (s : S.seq a) : seq_view a =
  if S.length s = 0 then Nil else Cons (S.head s) (S.tail s)

val merge : Seq.seq int -> Seq.seq int -> Seq.seq int
let rec merge s1 s2 : Tot (S.seq int) (decreases S.length s1 + S.length s2) =
  match view s1, view s2 with
  | Nil, Nil -> S.empty
  | Nil, Cons h t -> S.cons h t
  | Cons h t, Nil -> S.cons h t
  | Cons h1 t1, Cons h2 t2 ->
    if h1 <= h2 then S.cons h1 (merge t1 s2) else S.cons h2 (merge s1 t2)

assume val merge_len (s1 s2 : S.seq int)
  : Lemma (ensures S.length (merge s1 s2) == S.length s1 + S.length s2)
          [SMTPat (merge s1 s2)]

assume val merge_sorted' (s1 s2 : S.seq int)
  : Lemma (ensures merge (sort s1) (sort s2) == sort (s1 `S.append` s2))
          [SMTPat (merge (sort s1) (sort s2))]

assume val merge_sorted (s1 s2 : S.seq int)
  : Lemma (requires sorted s1 /\ sorted s2)
          (ensures sorted (merge s1 s2))
          [SMTPat (sorted (merge s1 s2))]

val append_slice #a (s : S.seq a)
  (l1:nat) (l2 : nat{S.length s == l2 /\ l1 <= l2})
  : Lemma (S.append (S.slice s 0 l1) (S.slice s l1 l2) == s)
          [SMTPat (S.append (S.slice s 0 l1) (S.slice s l1 l2))]
let append_slice s l1 l2 =
  assert (S.equal (S.append (S.slice s 0 l1) (S.slice s l1 l2)) s);
  ()

(* These two must be total or the invariant of the loop fails to typecheck.
I think the problem is that the pure assertions within the invariant are not
used to typecheck the other components of the invariant. *)
let stake #a (i:nat) (s : S.seq a)
: Tot (S.seq a)
= if i <= S.length s
  then S.slice s 0 i
  else s

let sdrop #a (i:nat) (s : S.seq a)
: Tot (S.seq a)
= if i <= S.length s
  then S.slice s i (S.length s)
  else S.empty

let take_0_lem #a (s : S.seq a)
  : Lemma (stake 0 s == S.empty)
          [SMTPat (stake 0 s)]
  = ()

let drop_0_lem #a (s : S.seq a)
  : Lemma (sdrop 0 s == s)
          [SMTPat (sdrop 0 s)]
  = ()

let take_len_lem #a (s : S.seq a)
  : Lemma (stake (S.length s) s == s)
          [SMTPat (stake (S.length s) s)]
  = ()

let drop_len_lem #a (s : S.seq a)
  : Lemma (sdrop (S.length s) s == S.empty)
          [SMTPat (sdrop (S.length s) s)]
  = ()
//
let nil_app_l #a (s : S.seq a)
  : Lemma (S.append S.empty s == s)
          [SMTPat (S.append S.empty s)]
  = S.append_empty_l s
let nil_app_r #a (s : S.seq a)
  : Lemma (S.append s S.empty == s)
          [SMTPat (S.append s S.empty)]
  = S.append_empty_r s

let lem_upd_spliced #a (l:nat) (s1 s2 : S.seq a) (i : nat)
  : Lemma
      (requires S.length s1 == l /\ S.length s2 == l /\ 0 <= i /\ i < l )
      (ensures
        S.upd (stake i s1 `S.append` sdrop i s2) i (S.index s1 i) ==
              (stake (i+1) s1 `S.append` sdrop (i+1) s2))
  = assert (S.equal (S.upd (stake i s1 `S.append` sdrop i s2) i (S.index s1 i))
                    (stake (i+1) s1 `S.append` sdrop (i+1) s2));
    ()

let partial_merge
  (s1 s2 : S.seq int)
  (s3 : S.seq int {S.length s3 == S.length s1 + S.length s2})
  (i:nat{i <= S.length s1}) (j : nat{j <= S.length s2})
: Seq.lseq int (S.length s1 + S.length s2) =
  S.append (merge (stake i s1) (stake j s2)) (sdrop (i+j) s3)

#set-options "--z3rlimit 20"

let lemma_eq_intro_explicit (#a : Type) (s1 : S.seq a) (s2 : S.seq a{S.length s2 == S.length s1})
  (pf : ((i:nat{i < S.length s1}) -> Lemma (S.index s1 i == S.index s2 i)))
  : Lemma (S.equal s1 s2)
  = Classical.forall_intro pf;
    S.lemma_eq_intro s1 s2

let lem_partial_merge_full_l_add (s1 s2 : S.seq int) (s3 : _) (i:nat) (j : nat)
  : Lemma (requires i == S.length s1 /\ j < S.length s2)
          (ensures Seq.upd (partial_merge s1 s2 s3 i j)
                           (i+j) (S.index s2 j)
                    == partial_merge s1 s2 s3 i (j+1))
=
  let ss1 = (S.append (merge s1 (stake j s2))
            (Seq.upd (sdrop (i+j) s3) 0 (S.index s2 j))) in
  let ss2 = (S.append (merge s1 (stake (j+1) s2))
            (sdrop (i+j+1) s3)) in
  lemma_eq_intro_explicit ss1 ss2
    (fun k -> admit ())
  ;
  calc S.equal {
    Seq.upd (partial_merge s1 s2 s3 i j)
            (i+j)
            (S.index s2 j);
    `S.equal` { () }
    Seq.upd (S.append (merge s1 (stake j s2))
                      (sdrop (i+j) s3)) 
            (i+j)
            (S.index s2 j);
    `S.equal` { () }
    S.append (merge s1 (stake j s2))
             (Seq.upd (sdrop (i+j) s3) 0 (S.index s2 j));
    `S.equal` { () }
    S.append (merge s1 (stake (j+1) s2))
             (sdrop (i+j+1) s3);
    `S.equal` { () }
    partial_merge s1 s2 s3 i (j+1);
  }

let lem_partial_merge_full_r_add (s1 s2 : S.seq int) (s3 : _) (i:nat) (j : nat)
  : Lemma (requires i < S.length s1 /\ j == S.length s2)
          (ensures Seq.upd (partial_merge s1 s2 s3 i j)
                           (i+j) (S.index s1 i)
                    == partial_merge s1 s2 s3 (i+1) j)
=
  let ss1 = (S.append (merge (stake i s1) s2)
            (Seq.upd (sdrop (i+j) s3) 0 (S.index s1 i))) in
  let ss2 = (S.append (merge (stake (i+1) s1) s2)
            (sdrop (i+j+1) s3)) in
  lemma_eq_intro_explicit ss1 ss2
    (fun k -> admit ())
  ;
  calc S.equal {
    Seq.upd (partial_merge s1 s2 s3 i j)
            (i+j)
            (S.index s1 i);
    `S.equal` { () }
    Seq.upd (S.append (merge (stake i s1) s2)
                      (sdrop (i+j) s3)) 
            (i+j)
            (S.index s1 i);
    `S.equal` { () }
    S.append (merge (stake i s1) s2)
             (Seq.upd (sdrop (i+j) s3) 0 (S.index s1 i));
    `S.equal` { () }
    S.append (merge (stake (i+1) s1) s2)
             (sdrop (i+j+1) s3);
    `S.equal` { () }
    partial_merge s1 s2 s3 (i+1) j;
  }

let lem_partial_merge_left_add (s1 s2 : S.seq int) (s3 : _) (i : nat{i < S.length s1}) (j : nat{j < S.length s2})
  : Lemma (requires Seq.index s1 i <= Seq.index s2 j)
          (ensures Seq.upd (partial_merge s1 s2 s3 i j)
                           (i+j) (S.index s1 i)
                    == partial_merge s1 s2 s3 (i+1) j)
= admit()

let lem_partial_merge_right_add (s1 s2 : S.seq int) (s3 : _) (i : nat{i < S.length s1}) (j : nat{j < S.length s2})
  : Lemma (requires Seq.index s1 i >= Seq.index s2 j)
          (ensures Seq.upd (partial_merge s1 s2 s3 i j)
                           (i+j) (S.index s2 j)
                    == partial_merge s1 s2 s3 i (j+1))
  = admit ()
