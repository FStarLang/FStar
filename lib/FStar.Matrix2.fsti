(*--build-config
    options:--admit_fsi FStar.Seq;
    other-files:seq.fsi
 --*)
 
(*
   Copyright 2008-2015 Nikhil Swamy and Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module FStar.Matrix2
#set-options "--no_fs_typ_app"
#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 "

type matrix2 : nat -> nat -> Type -> Type
open FStar.Seq

(* Destructors *)
val index:  #a:Type -> #m:nat -> #n:nat -> matrix2 m n a -> i:nat{i < m} -> j:nat{j < n} -> Tot a
val row:    #a:Type -> #m:nat -> #n:nat -> matrix2 m n a -> i:nat{i<m} -> Tot (seq a)
val col:    #a:Type -> #m:nat -> #n:nat -> matrix2 m n a -> j:nat{j<n} -> Tot (seq a)

(* Constructors *)
val create: #a:Type -> m:nat -> n:nat -> a -> Tot (matrix2 m n a)
val emp:    #a:Type -> Tot (matrix2 0 0 a)
val upd:    #a:Type -> #m:nat -> #n:nat -> x:matrix2 m n a -> i:nat{i<m} -> j:nat{j<n} -> a -> Tot (matrix2 m n a)
val upd_row:#a:Type -> #m:nat -> #n:nat -> x:matrix2 m n a -> i:nat{i<m} -> r:seq a{Seq.length r = n} -> Tot (matrix2 m n a)
val upd_col:#a:Type -> #m:nat -> #n:nat -> x:matrix2 m n a -> j:nat{j<n} -> c:seq a{Seq.length c = m} -> Tot (matrix2 m n a)

(* Lemmas about length *)
val lemma_row_len: #a:Type -> m:nat -> n:nat -> x:matrix2 m n a -> i:nat{i<m} -> Lemma
  (requires True)
  (ensures (Seq.length (row x i) = n))
  [SMTPat (Seq.length (row x i))]

val lemma_col_len: #a:Type -> m:nat -> n:nat -> x:matrix2 m n a -> j:nat{j<n} -> Lemma
  (requires True)
  (ensures (Seq.length (col x j) = m))
  [SMTPat (Seq.length (col x j))]

(* Lemmas about index *)
val lemma_index_create: #a:Type -> m:nat -> n:nat -> v:a -> i:nat{i < m} -> j:nat{j < n} -> Lemma
  (requires True)
  (ensures (index (create m n v) i j = v))
  [SMTPat (index (create m n v) i j)]

val lemma_index_upd1: #a:Type -> m:nat -> n:nat -> x:matrix2 m n a -> i:nat{i<m} -> j:nat{j<n} -> v:a -> Lemma
  (requires True)
  (ensures (index (upd x i j v) i j = v))
  [SMTPat (index (upd x i j v) i j)]

val lemma_index_upd2: #a:Type -> m:nat -> n:nat -> x:matrix2 m n a -> i:nat{i<m} -> j:nat{j<n} -> i':nat{i'<m} -> j':nat{j'<n} -> v:a -> Lemma
  (requires (i<>i' \/ j<>j'))
  (ensures (index (upd x i j v) i' j' = index x i' j'))
  [SMTPat (index (upd x i j v) i' j')]
  
val lemma_index_row: #a:Type -> m:nat -> n:nat -> x:matrix2 m n a -> i:nat{i<m} -> j:nat{j<n} -> Lemma 
  (requires (True))
  (ensures (Seq.index (row x i) j = index x i j))
  [SMTPat (Seq.index (row x i) j)]

val lemma_index_col: #a:Type -> m:nat -> n:nat -> x:matrix2 m n a -> i:nat{i<m} -> j:nat{j<n} -> Lemma 
  (requires (True))
  (ensures (Seq.index (col x j) i = index x i j))
  [SMTPat (Seq.index (col x j) i)]

val lemma_index_upd_row1: #a:Type -> m:nat -> n:nat -> x:matrix2 m n a -> s:seq a{Seq.length s = n} -> i:nat{i<m} -> j:nat{j<n} -> Lemma 
  (requires (True))
  (ensures (index (upd_row x i s) i j = Seq.index s j))
  [SMTPat (index (upd_row x i s) i j)]

val lemma_index_upd_row2: #a:Type -> m:nat -> n:nat -> x:matrix2 m n a -> s:seq a{Seq.length s = n} -> i:nat{i<m} 
                          -> i':nat{i'<m /\ i<>i'} -> j:nat{j<n} -> Lemma 
  (requires (True))
  (ensures (index (upd_row x i s) i' j = index x i' j))
  [SMTPat (index (upd_row x i s) i' j)]

val lemma_index_upd_col1: #a:Type -> m:nat -> n:nat -> x:matrix2 m n a -> s:seq a{Seq.length s = m} -> j:nat{j<n} -> i:nat{i<m} -> Lemma 
  (requires (True))
  (ensures (index (upd_col x j s) i j = Seq.index s i))
  [SMTPat (index (upd_col x j s) i j)]

val lemma_index_upd_col2: #a:Type -> m:nat -> n:nat -> x:matrix2 m n a -> s:seq a{Seq.length s = m} -> j:nat{j<n} 
                          -> i:nat{i<m} -> j':nat{j'<n /\ j'<>j} -> Lemma 
  (requires (True))
  (ensures (index (upd_col x j s) i j' = index x i j'))
  [SMTPat (index (upd_col x j s) i j')]

(* Extensionality *)
type Eq: #a:Type -> #m:nat -> #n:nat -> matrix2 m n a -> matrix2 m n a -> Type
val lemma_eq_intro: #a:Type -> #m:nat -> #n:nat -> x1:matrix2 m n a -> x2:matrix2 m n a -> Lemma
     (requires ((forall (i:nat{i < m}) (j:nat{j<n}). {:pattern (index x1 i j); (index x2 i j)} (index x1 i j == index x2 i j))))
     (ensures (Eq x1 x2))
     [SMTPatT (Eq x1 x2)]

val lemma_eq_elim: #a:Type -> #m:nat -> #n:nat -> x1:matrix2 m n a -> x2:matrix2 m n a -> Lemma
     (requires (Eq x1 x2))
     (ensures (x1=x2))
     [SMTPatT (Eq x1 x2)]


