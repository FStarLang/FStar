(*
   Copyright 2008-2017 Microsoft Research

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

module FStar.Vector.Properties

open FStar.Vector.Base
module S = FStar.Seq
module U32 = FStar.UInt32
module L = FStar.List.Tot

open FStar.UInt32

#set-options "--use_two_phase_tc true"

let int_to_u32 (x:int): Tot U32.t = U32.uint_to_t (UInt.to_uint_t 32 x)
let u32_to_int (x:U32.t): Tot (y:int{y = U32.v x}) = U32.v x
let is_u32 (x:int): bool = UInt.fits x U32.n

let subv
    (#a:Type)
    (#l:len_t)
    (v:raw a l)
    (i:len_t)
    (j:len_t{i <=^ j /\ j <=^ l})
  : Tot (raw a (j -^ i))
  = FStar.Vector.Base.sub v i j

/// This coercion seems to be necessary in some places
///
/// For example,  when trying to treat a    `raw a (l1 +^ l2)`
///                                    as a `raw a (m1 +^ m2)`
/// F* type inference tries matches on the head symbol of the index
/// and tries to prove `l1 = m1 /\ l2 = m2`
/// which is often too strong.
/// This coercion is a workaround for in such cases
unfold
let coerce
    (#a:Type)
    (#l:len_t)
    (v:raw a l)
    (m:len_t{l == m})
  : Tot (raw a m)
  = v

/// An abbreviation that states that some binary arithmetic
/// operation on len_t's respects bounds
unfold
let ok
    (op:int -> int -> int)
    (l1:len_t)
    (l2:len_t)
  : Type
  = UInt.size U32.(op (v l1) (v l2)) U32.n

/// Most lemmas from FStar.Seq.Properties can just be lifted
/// to vectors, although the lengths have to be bounds checked
let append_inj
    (#a:Type)
    (#l1:len_t)
    (#l2:len_t)
    (#m1:len_t)
    (#m2:len_t)
    (u1:raw a l1)
    (u2:raw a l2{ok (+) l1 l2})
    (v1:raw a m1)
    (v2:raw a m2{ok (+) m1 m2})
  : Lemma
    (requires (m1 +^ m2 = l1 +^ l2 /\
               equal (u1@|u2) (coerce (v1@|v2) (l1 +^ l2)) /\
               (l1 == m1 \/ l2 == m2)))
    (ensures (l1 = m1 /\
              l2 = m2 /\
              equal u1 v1 /\
              equal u2 v2))
  = FStar.Seq.lemma_append_inj (reveal u1) (reveal u2) (reveal v1) (reveal v2)

let head 
    (#a:Type) 
    (#l:len_t{l >^ 0ul}) 
    (v:raw a l)
  : Tot a
  = v.[0ul]

let tail 
    (#a:Type) 
    (#l:len_t{l >^ 0ul}) 
    (v:raw a l)
  : Tot (raw a U32.(l -^ 1ul))
  = subv v 1ul l

let head_append
    (#a:Type)
    (#l1:len_t)
    (#l2:len_t)
    (v1:raw a l1{l1 >^ 0ul})
    (v2:raw a l2{ok (+) l1 l2})
  : Lemma
    (ensures (head (v1@|v2) == head v1))
  = ()

let tail_append
    (#a:Type)
    (#l1:len_t)
    (#l2:len_t)
    (v1:raw a l1{l1 >^ 0ul})
    (v2:raw a l2{ok (+) l1 l2})
  : Lemma
    (ensures (tail (v1@|v2) == tail v1@|v2))
  = Seq.lemma_tail_append (reveal v1) (reveal v2)

let reinx 
    (#a:Type) 
    (#l:len_t) 
    (i:len_t) 
    (v:raw a l{i <^ l}) 
  : Tot (index_t v) 
  = let (r:len_t{r <^ l}) = i in
    r
      
let lemma_append_inj_l
    (#a:Type) 
    (#l1:len_t)
    (#l2:len_t)
    (v1:raw a l1)
    (v2:raw a l2)
    (w1:raw a l1) 
    (w2:raw a l2)
    (i:index_t v1{ok (+) l1 l2})
  : Lemma
    (requires (equal (v1 @| v2) (w1 @| w2)))
    (ensures (v1.[i] == w1.[reinx i w1]))
  = let rs = v1 @| v2 in
    let rt = w1 @| w2 in
    let rl = l1 +^ l2 in
    assert (v1.[i] == index rs (reinx i rs));
    assert (w1.[reinx i w1] == index rt (reinx i rt))

let lemma_append_inj_r
    (#a:Type)
    (#l1:len_t)
    (#l2:len_t)
    (v1:raw a l1)
    (v2:raw a l2)
    (w1:raw a l1)
    (w2:raw a l2)
    (i:index_t v2{ok (+) l1 l2})
  : Lemma 
    (requires (equal (v1 @| v2) (w1 @| w2)))
    (ensures (v2.[i] == w2.[reinx i w2]))
  = let rs = v1 @| v2 in
    let rt = w1 @| w2 in
    let rl = l1 +^ l2 in
    let ipl1 = i +^ l1 in
    assert (v2.[i] == index rs ipl1);
    assert (w2.[reinx i w2] == index rt ipl1)

let lemma_append_len_disj
    (#a:Type)
    (#lv1:len_t)
    (#lv2:len_t)
    (#lw1:len_t)
    (#lw2:len_t)
    (v1:raw a lv1)
    (v2:raw a lv2)
    (w1:raw a lw1)
    (w2:raw a lw2{ok (+) lv1 lv2 /\ ok (+) lw1 lw2})
  : Lemma 
    (requires ((lv1 =^ lw1 \/ lv2 =^ lw2) /\ 
              (equal2 (append v1 v2) (append w1 w2))))
    (ensures (lv1 =^ lw1 /\ lv2 =^ lw2))
  = let v1v2 = append v1 v2 in
    let w1w2 = append w1 w2 in
    assert (raw_length v1v2 == u32_to_int (lv1 +^ lv2));
    assert (raw_length w1w2 == u32_to_int (lw1 +^ lw2))

let lemma_append_inj
    (#a:Type)
    (#lv1:len_t)
    (#lv2:len_t)
    (#lw1:len_t)
    (#lw2:len_t)
    (v1:raw a lv1)
    (v2:raw a lv2{ok (+) lv1 lv2})
    (w1:raw a lw1)
    (w2:raw a lw2{ok (+) lw1 lw2})
  : Lemma
    (requires ((lv1 = lw1 \/ lv2 = lw2)) /\
              // cwinter: via equal2 we can do this without annoying coercions.
              equal2 (append v1 v2) (append w1 w2))
    (ensures (lv1 = lw1 /\ lv2 = lw2 /\ 
              equal v1 w1 /\ equal v2 w2))
  = Seq.lemma_append_inj (reveal v1) (reveal v2) (reveal w1) (reveal w2)

let last
    (#a:Type) 
    (#l:len_t)
    (v:raw a l {l >^ 0ul})
  : Tot a
  = v.[l -^ 1ul]

let empty
    (#a:Type)
  : Tot (raw a 0ul)
  = init #a 0ul (fun _ -> ())  //AR: use of init seems to require the implicit

let create1
    (#a:Type)
    (x:a)
  : Tot (raw a 1ul)
  = init 1ul (fun _ -> x)

let cons
    (#a:Type)
    (#l:len_t)
    (x:a)
    (v:raw a l{ok (+) l 1ul})
  : Tot (raw a (1ul +^ l))
  = append (create1 x) v

let lemma_cons_inj
    (#a:Type)
    (#lv1:len_t)
    (#lv2:len_t) 
    (x1:a) 
    (x2:a) 
    (v1:raw a lv1) 
    (v2:raw a lv2 {ok (+) lv1 1ul /\ ok (+) lv2 1ul})
  : Lemma 
    (requires (equal2 (cons x1 v1) (cons x2 v2)))
    (ensures (v1 == v2 /\ equal v1 v2))
  = let w1 = create1 x1 in 
    let w2 = create1 x2 in 
    lemma_append_inj w1 v1 w2 v2;
    assert(w1.[0ul] == w2.[0ul])

let split
    (#a:Type)
    (#l:len_t)
    (v:raw a l)
    (i:index_t v)
  : Tot (raw a i * raw a (l -^ i))
  = init i (fun j -> v.[int_to_u32 j]), init (l -^ i) (fun j -> v.[i +^ int_to_u32 j])

let lemma_split
    (#a:Type)
    (#l:len_t)
    (v:raw a l) 
    (i:index_t v)
  : Lemma 
    (ensures (append (fst (split v i)) (snd (split v i)) == v))
  = assert (equal (append (fst (split v i)) (snd (split v i))) v)

let split_eq
    (#a:Type)
    (#l:len_t)
    (v:raw a l)
    (i:index_t v) 
  : Pure (raw a i * raw a (l -^ i))
    (requires True)
    (ensures (fun x -> (append (fst x) (snd x) == v)))
  = let x = split v i in
    lemma_split v i;
    x

let rec count 
    (#a:eqtype)
    (#l:len_t)
    (x:a) 
    (v:raw a l) 
  : Tot nat 
    (decreases (u32_to_int l))
  = if l =^ 0ul then 0 
    else
      let t = tail v in
      let n = if head v = x then 1 else 0 in
      n + (count x t)

let mem
    (#a:eqtype)
    (#l:len_t)
    (x:a) 
    (v:raw a l) 
  : Tot bool
  = count x v > 0

#set-options "--max_fuel 1 --initial_fuel 1"
let rec mem_index 
    (#a:eqtype) 
    (#l:len_t) 
    (x:a) 
    (v:raw a l)
  : Lemma 
    (requires (mem x v))
    (ensures (exists (i:index_t v). (index v i) == x))
    (decreases (u32_to_int l))
  = if l =^ 0ul then ()
    else let m : (m:len_t{m >^ 0ul}) = l in
         let u = coerce v m in //NS: I use this patterns sometimes to workaround providing too many painful implicit arguments
         if head u = x then ()
         else let t = tail u in
              let _ = mem_index x t in
              assert (forall (j:index_t t). t.[j] == u.[j +^ 1ul]) //NS: this bit of index juggling is needed to find the witness of the existential in the goal
#reset-options

#set-options "--use_two_phase_tc true"

let swap
    (#a:Type) 
    (#l:len_t) 
    (v:raw a l) 
    (i:index_t v)
    (j:index_t v) 
  : Tot (raw a l)
  = let nv = update v j (index v i) in
    update nv (reinx i nv) (index v j)

let lemma_sub_append
    (#a:Type)
    (#lv1:len_t)
    (#lv2:len_t)
    (v1:raw a lv1 {lv1 >=^ 1ul})
    (v2:raw a lv2 {ok (+) lv1 lv2})
  : Lemma
    (ensures (let s1 = subv v1 0ul 1ul in
              let s2 = subv v1 1ul lv1 in
              let v1v2 = append v1 v2 in
              let s2v2 = append s2 v2 in
              let s1s2v2= append s1 s2v2 in
              equal2 v1v2 s1s2v2))
  = ()

let rec lemma_sub_first_in_append
    (#a:Type)
    (#lv1:len_t)
    (#lv2:len_t)
    (v1:raw a lv1)
    (v2:raw a lv2{ok (+) lv1 lv2}) 
    (i:index_t v1{ok (+) (lv1 -^ i) lv2})
  : Lemma
    (ensures (let v1v2 = append v1 v2 in
              let lv1v2 = int_to_u32 (raw_length v1v2) in
              let v1_from_i = subv v1 i lv1 in
              let v1_from_i_v2 = append v1_from_i v2 in
              let v1v2_from_i = subv v1v2 i lv1v2 in
              equal2 v1v2_from_i v1_from_i_v2))
    (decreases (u32_to_int lv1))
  = if i =^ 0ul then ()
    else lemma_sub_first_in_append (tail v1) v2 (i -^ 1ul)

let sub_update
    (#a:Type)
    (#l:len_t)
    (v:raw a l)
    (i:index_t v)
    (j:index_t v{i <=^ j})
    (k:index_t v{k <^ i \/ j <=^ k})
    (x:a)
  : Lemma
    (ensures (subv (update v k x) i j == subv v i j))
    [SMTPat (subv (update v k x) i j)]
  = lemma_eq_intro (subv (update v k x) i j) (subv v i j)

let update_sub
    (#a:Type)
    (#l:len_t)
    (v:raw a l)
    (i:index_t v)
    (j:index_t v{i <=^ j})
    (k:index_t v{ok (+) i k /\ i +^ k <^ j})
    (x:a)
  : Lemma
    (ensures (let t = subv v i j in
              update t (reinx k t) x == subv (update v (i +^ k) x) i j))
    [SMTPat (update (subv v i j) k x)]
  = let t = subv v i j in
    lemma_eq_intro (update t (reinx k t) x) (subv (update v (i +^ k) x) i j)

let lemma_cons_head_append
    (#a:Type) 
    (#lv1:len_t) 
    (#lv2:len_t)
    (v1:raw a lv1{lv1 >^ 0ul})
    (v2:raw a lv2{ok (+) lv1 lv2})
  : Lemma
    (ensures (let (v1v2:raw a (lv1 +^ lv2)) = append v1 v2 in
              let (hv1:a) = head v1 in
              let (tv1:raw a (lv1 -^ 1ul)) = tail v1 in
              let (tv1v2:raw a (lv1 +^ lv2 -^ 1ul)) = append tv1 v2 in
              let magic_len = 1ul +^ ((lv1 -^ 1ul) +^ lv2) in
              let (hv1tv1v2:raw a magic_len) = cons hv1 tv1v2 in              
              magic_len = lv1 +^ lv2 /\
              equal v1v2 hv1tv1v2))
  = ()

let lemma_tl
    (#a:Type)
    (#l:len_t)
    (hd:a)
    (tl:raw a l{ok (+) l 1ul})
  : Lemma
    (ensures (equal (tail (cons hd tl)) tl))
  = ()

let rec sorted
    (#a:Type) 
    (#l:len_t)
    (f:a -> a -> Tot bool)
    (v:raw a l)
  : Tot bool 
    (decreases (u32_to_int l))
  = if l <=^ 1ul
    then true
    else let hd = head v in
         f hd v.[1ul] && sorted f (tail v)

#set-options "--max_fuel 1 --initial_fuel 1"
let rec lemma_append_count
    (#a:eqtype)
    (#llo:len_t)
    (#lhi:len_t)
    (lo:raw a llo)
    (hi:raw a lhi{ok (+) llo lhi})
  : Lemma
    (ensures (forall x. count x (append lo hi) = (count x lo + count x hi)))
    (decreases (u32_to_int llo))
  = if llo =^ 0ul
    then assert (equal (append lo hi) hi)
    else 
      let (lohi:raw a (llo +^ lhi)) = append lo hi in
      let (hdlo:a) = head lo in
      let ltllohi = llo -^ 1ul +^ lhi in
      let (tllohi:raw a ltllohi) = append (tail lo) hi in
      let lhdlotllohi = 1ul +^ (llo -^ 1ul +^ lhi) in
      let (hdlotllohi:raw a lhdlotllohi) = cons hdlo tllohi in
      (assert (equal hdlotllohi lohi);
           let (ln:len_t) = llo -^ 1ul in
           lemma_append_count (tail lo) hi;
           let ltl_l_h = (llo -^ 1ul) +^ lhi in
           let (tl_l_h:raw a ltl_l_h) = append (tail lo) hi in
           let llh = 1ul +^ ltl_l_h in
           let (lh:raw a llh) = cons (head lo) tl_l_h in
           assert (equal2 (tail lh) tl_l_h))
#reset-options

#set-options "--use_two_phase_tc true"

let lemma_append_count_aux
    (#a:eqtype)
    (#llo:len_t)
    (#lhi:len_t)
    (x:a)
    (lo:raw a llo)
    (hi:raw a lhi{ok (+) llo lhi})
  : Lemma
    (requires True)
    (ensures (count x (append lo hi) = (count x lo + count x hi)))
  = lemma_append_count lo hi

let lemma_mem_inversion
    (#a:eqtype)
    (#l:len_t)
    (v:raw a l{l >^ 0ul})
    : Lemma
  (ensures (forall x. mem x v = (x=head v || mem x (tail v))))
= ()

let rec lemma_mem_count
    (#a:eqtype)
    (#l:len_t)
    (v:raw a l)
    (f:a -> Tot bool)
  : Lemma
    (requires (forall (i:index_t v). f v.[i]))
    (ensures (forall (x:a). mem x v ==> f x))
    (decreases (u32_to_int l))
  = if l =^ 0ul then ()
    else let ltl = l -^ 1ul in
         let tl = tail v in
         assert (forall (i:len_t{i <^ ltl}). 
                     (index tl i) = v.[i +^ 1ul]);
         lemma_mem_count tl f

let lemma_count_sub
    (#a:eqtype) 
    (#l:len_t)
    (v:raw a l)
    (i:index_t v)
  : Lemma
    (requires True)
    (ensures (forall x. count x v = count x (subv v 0ul i) + count x (subv v i l)))
  = assert (equal v (append (subv v 0ul i) (subv v i l)));
    lemma_append_count (subv v 0ul i) (subv v i l)

type total_order (a:eqtype) (f: (a -> a -> Tot bool)) =
    (forall a. f a a)                                           (* reflexivity   *)
    /\ (forall a1 a2. (f a1 a2 /\ a1<>a2)  <==> not (f a2 a1))  (* anti-symmetry *)
    /\ (forall a1 a2 a3. f a1 a2 /\ f a2 a3 ==> f a1 a3)        (* transitivity  *)
type tot_ord (a:eqtype) = f:(a -> a -> Tot bool){total_order a f}

#set-options "--max_fuel 1 --initial_fuel 1 --z3rlimit 100"
let rec sorted_concat_lemma
    (#a:eqtype)
    (#llo:len_t)
    (#lhi:len_t)
    (f:a -> a -> Tot bool{total_order a f})
    (lo:raw a llo{sorted f lo})
    (pivot:a)
    (hi:raw a lhi{sorted f hi /\ ok (+) llo lhi /\ ok (+) (llo +^ lhi) 1ul})
  : Lemma 
    (requires (forall y. (mem y lo ==> f y pivot) /\
                         (mem y hi ==> f pivot y)))
    (ensures (sorted f (append lo (cons pivot hi))))
    (decreases (u32_to_int llo))
  = let phi = cons pivot hi in
    let lphi = lhi +^ 1ul in
    if llo =^ 0ul 
    then let llophi = llo +^ lhi +^ 1ul in
         let lophi = append lo phi in
         (assert (equal2 lophi phi);
          assert (equal (tail phi) hi))
    else let tlo = tail lo in
         let ltlo = llo -^ 1ul in
         let tllophi = append tlo phi in
         let h = head lo in
         sorted_concat_lemma f tlo pivot hi;
         lemma_cons_head_append lo phi;
         lemma_tl h tllophi

#set-options "--max_fuel 1 --initial_fuel 1 --z3rlimit 30"
let split_5 
    (#a:Type)
    (#l:len_t)
    (v:raw a l) 
    (i:index_t v{ok (+) i 1ul /\ ok (Prims.op_Subtraction) l i})
    (j:index_t v{i <^ j /\ ok (+) j 1ul /\ ok (+) i j /\ 1ul <^ l -^ j})
  : Pure (raw a i * 
          raw a 1ul * 
          raw a (j -^ (i +^ 1ul)) * 
          raw a 1ul * 
          raw a (l -^ (j +^ 1ul)))
    (requires (True))
    (ensures (fun (b, c, d, e, f) ->
               (v == b @| c @| d @| e @| f)
               /\ equal2 b (subv v 0ul i)
               /\ equal2 c (subv v i (i +^ 1ul))
               /\ equal2 d (subv v (i +^ 1ul) j)
               /\ equal2 e (subv v j (j +^ 1ul))
               /\ equal2 f (subv v (j +^ 1ul) l)
               ))
  = let frag_lo,  (rest:raw a (l -^ i)) = split_eq v i in  
    let frag_i,   (rest:raw a (l -^ i -^ 1ul))  = split_eq rest (reinx 1ul rest) in
    let frag_mid, (rest:raw a (l -^ i -^ 1ul -^ (j -^ (i +^ 1ul)))) = split_eq rest (j -^ (i +^ 1ul)) in
    let frag_j,   (rest:raw a (l -^ i -^ 1ul -^ (j -^ (i +^ 1ul)) -^ 1ul)) = split_eq rest (reinx 1ul rest) in
    let frag_hi   = coerce rest (l -^ (j +^ 1ul)) in
    (frag_lo, frag_i, frag_mid, frag_j, frag_hi)
#reset-options

#set-options "--use_two_phase_tc true"

let lemma_swap_permutes_aux_frag_eq
    (#a:Type)
    (#l:len_t)
    (v:raw a l)
    (i:index_t v)
    (j:index_t v{i <=^ j /\ ok (+) i 1ul /\ ok (+) j 1ul})
    (i':index_t v)
    (j':index_t v{i' <=^ j' /\ ok (+) i' 1ul /\ ok (+) j' 1ul /\
              (j <^ i'  //high sub
              \/ j' <=^ i //low sub
              \/ (i <^ i' /\ j' <=^ j)) //mid sub 
              })
  : Lemma (ensures (subv v i' j' == subv (swap v i j) i' j'
                 /\ subv v i (i +^ 1ul) == coerce (subv (swap v i j) j (j +^ 1ul)) (i +^ 1ul -^ i)
                 /\ subv v j (j +^ 1ul) == coerce (subv (swap v i j) i (i +^ 1ul)) (j +^ 1ul -^ j)))
  = assert (equal (subv v i' j') (subv (swap v i j) i' j'));
    assert (equal (subv v i (i +^ 1ul)) (coerce (subv (swap v i j) j (j +^ 1ul)) (i +^ 1ul -^ i)));
    assert (equal (subv v j (j +^ 1ul)) (coerce (subv (swap v i j) i (i +^ 1ul)) (j +^ 1ul -^ j)))

#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3rlimit 20"
let lemma_swap_permutes_aux
    (#a:eqtype)
    (#l:len_t)
    (v:raw a l)
    (i:index_t v) 
    (j:index_t v{i <=^ j})
    (x:a)
  : Lemma
    (requires (ok (+) i 1ul /\ ok (+) j 1ul /\ ok (+) i j /\ 1ul <^ l -^ j /\ ok (Prims.op_Subtraction) l i))
    (ensures (count x v = count x (swap v i j)))
  = if i =^ j
    then assert (equal (swap v i j) v)
    else begin
      let frag_lo, frag_i, frag_mid, frag_j, frag_hi = split_5 v i j in
      let l5 = (l -^ (j +^ 1ul)) in
      let l4 = 1ul in
      let l3 = (j -^ (i +^ 1ul)) in
      let l2 = 1ul in
      let l1 = i in
      let l45 = l4 +^ l5 in
      let (f45:raw a l45) = (append frag_j frag_hi) in
      let l345 = l3 +^ l45 in
      let (f345:raw a l345) = (append frag_mid f45) in
      let l2345 = l2 +^ l345 in
      let (f2345:raw a l2345) = (append frag_i f345) in
      lemma_append_count_aux x frag_lo f2345;
      lemma_append_count_aux x frag_i f345;
      lemma_append_count_aux x frag_mid f45;
      lemma_append_count_aux x frag_j frag_hi;

      let v' = swap v i j in
      let i' = reinx i v' in
      let j' = reinx j v' in
      let frag_lo', frag_j', frag_mid', frag_i', frag_hi' = split_5 v' i' j' in // cwinter: necessary?
      
      lemma_swap_permutes_aux_frag_eq v i j 0ul i;
      lemma_swap_permutes_aux_frag_eq v i j (i +^ 1ul) j;
      lemma_swap_permutes_aux_frag_eq v i j (j +^ 1ul) (l -^ 1ul);

      let lihi = l2 +^ l5 in
      let (ihi:raw a lihi) = (append frag_i frag_hi) in
      let lmidihi = l3 +^ lihi in
      let (midihi:raw a lmidihi) = (append frag_mid ihi) in
      let ljmidihi = l4 +^ lmidihi in
      let (jmidihi:raw a ljmidihi) = (append frag_j midihi) in
      lemma_append_count_aux x frag_lo jmidihi;
      lemma_append_count_aux x frag_j midihi;
      lemma_append_count_aux x frag_mid ihi;
      lemma_append_count_aux x frag_i frag_hi      
  end
#reset-options

#set-options "--use_two_phase_tc true"

type permutation 
     (#a:eqtype)
     (#l:len_t)
     (v1:raw a l)
     (v2:raw a l) 
  = (forall i. count i v1 = count i v2)

let lemma_swap_permutes
    (#a:eqtype)
    (#l:len_t)
    (v:raw a l)
    (i:index_t v)
    (j:index_t v{i <=^ j})
  : Lemma
      (requires (ok (+) i 1ul /\ ok (+) j 1ul /\ ok (+) i j /\ 1ul <^ l -^ j /\ 1ul <^ l -^ i))
      (ensures (permutation v (swap v i j)))
  = FStar.Classical.forall_intro' #a #(fun x -> count x v = count x (swap v i j)) (lemma_swap_permutes_aux v i j)

#set-options "--max_fuel 1 --initial_fuel 1"
let cons_perm
    (#a:eqtype)
    (#l:len_t {l >^ 0ul})
    (tl:raw a (l -^ 1ul))
    (v:raw a l)
  : Lemma 
    (requires (permutation tl (tail v)))
    (ensures (permutation (cons (head v) tl) v))
  = lemma_tl (head v) tl

#set-options "--max_fuel 2 --initial_fuel 2"
let lemma_mem_append
    (#a:eqtype)
    (#l1:len_t)
    (#l2:len_t)
    (v1:raw a l1)
    (v2:raw a l2{ok (+) l1 l2})
  : Lemma 
    (ensures (forall (x:a). mem x (v1 @| v2) <==> (mem x v1 || mem x v2)))
  = lemma_append_count v1 v2

let lemma_sub_cons
    (#a:eqtype)
    (#l:len_t)
    (v:raw a l)
    (i:index_t v)
    (j:index_t v{i <^ j})
  : Lemma (ensures (forall x. mem x (subv v i j) <==> (x = v.[i] || mem x (subv v (i +^ 1ul) j))))
  = let vi1 = create1 v.[i] in
    assert (equal2 (subv v i j) (append vi1 (subv v (i +^ 1ul) j)));
    lemma_mem_append vi1 (subv v (i +^ 1ul) j)

let lemma_sub_snoc
    (#a:eqtype)
    (#l:len_t)
    (v:raw a l)
    (i:index_t v)
    (j:index_t v{i <^ j})
  : Lemma 
    (ensures (forall x. mem x (subv v i j) <==> (x = v.[j -^ 1ul] || mem x (subv v i (j -^ 1ul)))))
  = let vj1 = create1 v.[j -^ 1ul] in
    assert (equal2 (subv v i j) (append (subv v i (j -^ 1ul)) vj1));
    lemma_mem_append (subv v i (j -^ 1ul)) vj1

#reset-options "--z3rlimit 10 --use_two_phase_tc true"
let lemma_ordering_lo_snoc
    (#a:eqtype)
    (#l:len_t)
    (f:tot_ord a)
    (v:raw a l)
    (i:index_t v)
    (j:index_t v{i <=^ j})
    (pv:a)
   : Lemma 
     (requires ((forall y. mem y (subv v i j) ==> f y pv) /\ f v.[j] pv))
     (ensures ((forall y. mem y (subv v i (j +^ 1ul)) ==> f y pv)))
  = let vj1 = create1 v.[j] in
    assert (equal2 (subv v i (j +^ 1ul)) (append (subv v i j) vj1));
    lemma_mem_append (subv v i j) vj1

#reset-options "--z3rlimit 20 --use_two_phase_tc true"
let lemma_ordering_hi_cons
    (#a:eqtype)
    (#l:len_t)
    (f:tot_ord a)
    (v:raw a l)
    (back:index_t v)
    (len:index_t v{back <^ len})
    (pv:a)
  : Lemma 
    (requires ((forall y. mem y (subv v (back +^ 1ul) len) ==> f pv y) /\ f pv v.[back]))
    (ensures ((forall y. mem y (subv v back len) ==> f pv y)))
  = let vb1 = create1 v.[back] in
    assert (equal2 (subv v back len) (append vb1 (subv v (back +^ 1ul) len)));
    lemma_mem_append vb1 (subv v (back +^ 1ul) len)
#reset-options "--use_two_phase_tc true"

let swap_frame_lo
    (#a:Type)
    (#l:len_t)
    (v:raw a l)
    (lo:index_t v)
    (i:index_t v{lo <=^ i})
    (j:index_t v{i <=^ j})
  : Lemma 
    (ensures (subv v lo i == subv (swap v i j) lo i))
  = assert (equal (subv v lo i) (subv (swap v i j) lo i))

let swap_frame_lo' 
    (#a:Type)
    (#l:len_t)
    (v:raw a l)
    (lo:index_t v)
    (i':index_t v{lo <=^ i'})
    (i:index_t v{i' <=^ i})
    (j:index_t v{i <=^ j})
  : Lemma 
    (ensures (subv v lo i' == subv (swap v i j) lo i'))
  = assert (equal (subv v lo i') (subv (swap v i j) lo i'))

let swap_frame_hi
    (#a:Type)
    (#l:len_t)
    (v:raw a l)
    (i:index_t v)
    (j:index_t v{i <=^ j})
    (k:index_t v{j <^ k})
    (hi:index_t v{k <=^ hi})
  : Lemma 
    (ensures (subv v k hi == subv (swap v i j) k hi))
  = assert (equal (subv v k hi) (subv (swap v i j) k hi))

let lemma_swap_sub_commute
    (#a:Type)
    (#l:len_t)
    (v:raw a l)
    (start:index_t v)
    (i:index_t v{start <=^ i})
    (j:index_t v{i <=^ j})
    (len:len_t{j <^ len /\ len <=^ l})
  : Lemma 
    (ensures (subv (swap v i j) start len == (swap (subv v start len) (i -^ start) (j -^ start))))
  = assert (equal (subv (swap v i j) start len) (swap (subv v start len) (i -^ start) (j -^ start)))

let lemma_swap_permutes_sub 
    (#a:eqtype)
    (#l:len_t)
    (v:raw a l)
    (start:index_t v)
    (i:index_t v{start <=^ i})
    (j:index_t v{i <=^ j})
    (len:len_t{j <^ len /\ len <=^ l})
  : Lemma 
    (requires (ok (+) i 1ul /\ ok (+) j 1ul /\ ok (+) i j /\ ok (Prims.op_Subtraction) start j /\ 0ul <^ start -^ i))
    (ensures (permutation (subv v start len) (subv (swap v i j) start len)))
  = lemma_swap_sub_commute v start i j len;
    lemma_swap_permutes (subv v start len) (i -^ start) (j -^ start)

(* replaces the [i,j) sub-vector of v1 with the corresponding sub-vector of v2 *)
let splice
    (#a:Type)
    (#l:len_t)
    (v1:raw a l)
    (i:index_t v1)
    (v2:raw a l)
    (j:len_t{i <=^ j /\ j <=^ l})
  : Tot (raw a l)
  = append (subv v1 0ul i) (append (subv v2 i j) (subv v1 j l))

let splice_refl 
    (#a:Type)
    (#l:len_t)
    (v:raw a l)
    (i:index_t v)
    (j:len_t{i <=^ j /\ j <=^ l})
  : Lemma
    (ensures (v == splice v i v j))
  = assert (equal v (splice v i v j))

let lemma_swap_splice
    (#a:Type)
    (#l:len_t)
    (v:raw a l)
    (start:index_t v)
    (i:index_t v{start <=^ i})
    (j:index_t v{i <=^ j})
    (len:len_t{j <^ len /\ len <=^ l})
   : Lemma
     (ensures (swap v i j == splice v start (swap v i j) len))
= assert (equal (swap v i j) (splice v start (swap v i j) len))

let lemma_vector_frame_hi
    (#a:Type)
    (#l:len_t)
    (v1:raw a l)
    (v2:raw a l)
    (i:index_t v2)
    (j:index_t v1{i <=^ j})
    (m:index_t v1{j <=^ m})
    (n:len_t{m <^ n /\ n <=^ l})
  : Lemma
    (requires (v1 == (splice v2 i v1 j)))
    (ensures  ((subv v1 m n == subv v2 m n) /\ (index v1 m == index v2 (reinx m v2))))
  = assert (equal (subv v1 m n) (subv v2 m n))

let lemma_vector_frame_lo
    (#a:Type)
    (#l:len_t)
    (v1:raw a l)
    (v2:raw a l)
    (i:index_t v1)
    (j:index_t v1{i <=^ j})
    (m:index_t v2{j <^ m})
    (n:len_t{m <=^ n /\ n <=^ l})
  : Lemma
    (requires (v1 == (splice v2 m v1 n)))
    (ensures  ((subv v1 i j == subv v2 i j) /\ (index v1 j == index v2 (reinx j v2))))
  = assert (equal (subv v1 i j) (subv v2 i j))

let lemma_tail_sub
    (#a:Type)
    (#l:len_t)
    (v:raw a  l)
    (i:index_t v)
    (j:len_t{i <^ j /\ j <=^ l /\ ok (+) i 1ul})
  : Lemma
    (requires True)
    (ensures (let tl = tail (subv v i j) in
              let sv = subv v (i +^ 1ul) j in
              tl == coerce sv (j -^ i -^ 1ul)))
    [SMTPat (tail (subv v i j))]
  = assert (equal (tail (subv v i j)) (coerce (subv v (i +^ 1ul) j) (j -^ i -^ 1ul)))

let lemma_weaken_frame_right 
    (#a:Type)
    (#l:len_t)
    (v1:raw a l)
    (v2:raw a l) 
    (i:index_t v2)
    (j:index_t v1)
    (k:len_t{i <=^ j /\ j <=^ k /\ k <=^ l})
  : Lemma
    (requires (v1 == splice v2 i v1 j))
    (ensures (v1 == splice v2 i v1 k))
  = assert (equal v1 (splice v2 i v1 k))

let lemma_weaken_frame_left
    (#a:Type)
    (#l:len_t)
    (v1:raw a l)
    (v2:raw a l)
    (i:index_t v2)
    (j:index_t v2) 
    (k:len_t{i <=^ j /\ j <=^ k /\ k <=^ l})
  : Lemma
    (requires (v1 == splice v2 j v1 k))
    (ensures (v1 == splice v2 i v1 k))
  = assert (equal v1 (splice v2 i v1 k))

let lemma_trans_frame
    (#a:Type)
    (#l:len_t)
    (v1:raw a l)
    (v2:raw a l)
    (v3:raw a l)
    (i:index_t v3)
    (j:len_t{i <=^ j && j <=^ l})
  : Lemma
    (requires ((v1 == splice v2 (reinx i v2) v1 j) /\ v2 == splice v3 i v2 j))
    (ensures (v1 == splice v3 i v1 j))
  = assert (equal v1 (splice v3 i v1 j))

#reset-options "--z3rlimit 40 --use_two_phase_tc true"
let lemma_weaken_perm_left
    (#a:eqtype)
    (#l:len_t)
    (v1:raw a l)
    (v2:raw a l)
    (i:index_t v1)
    (j:index_t v2)
    (k:len_t{i <=^ j /\ j <=^ k /\ k <=^ l})
  : Lemma
    (requires (v1 == splice v2 j v1 k /\ permutation (subv v2 j k) (subv v1 j k)))
    (ensures (permutation (subv v2 i k) (subv v1 i k)))
  = assert (equal2 (subv v2 i k) (append (subv v2 i j)
                                      (subv v2 j k)));
    assert (equal2 (subv v1 i k) (append (subv v2 i j)
                                      (subv v1 j k)));
    lemma_append_count (subv v2 i j) (subv v2 j k);
    lemma_append_count (subv v2 i j) (subv v1 j k)

let lemma_weaken_perm_right
    (#a:eqtype)
    (#l:len_t)
    (v1:raw a l)
    (v2:raw a l)
    (i:index_t v1)
    (j:index_t v2)
    (k:len_t{i <=^ j /\ j <=^ k /\ k <=^ l})
  : Lemma
    (requires (let iq:len_t = i in
               v1 == splice v2 iq v1 j /\ 
               permutation (subv v2 iq j) (subv v1 iq j)))
    (ensures (permutation (subv v2 i k) (subv v1 i k)))
  = assert (equal2 (subv v2 i k) (append (subv v2 i j)
                                     (subv v2 j k)));
    assert (equal2 (subv v1 i k) (append (subv v1 i j)
                                     (subv v2 j k)));
    lemma_append_count (subv v2 i j) (subv v2 j k);
    lemma_append_count (subv v1 i j) (subv v2 j k)
#reset-options "--use_two_phase_tc true"

let lemma_trans_perm
    (#a:eqtype)
    (#l:len_t)
    (v1:raw a l)
    (v2:raw a l)
    (v3:raw a l)
    (i:index_t v1)
    (j:len_t{i <=^ j && j <=^ l})
  : Lemma
    (requires (permutation (subv v1 i j) (subv v2 i j)
              /\ permutation (subv v2 i j) (subv v3 i j)))
    (ensures (permutation (subv v1 i j) (subv v3 i j)))
  = ()

let snoc
    (#a:Type)
    (#l:len_t)
    (v:raw a l{ok (+) l 1ul}) 
    (x:a)
  : Tot (raw a (l +^ 1ul))
  = append v (create1 x)

let lemma_cons_snoc 
    (#a:Type) 
    (#l:len_t) 
    (hd:a) 
    (v:raw a l{ok (+) l 1ul /\ ok (+) l 2ul}) 
    (tl:a)
  : Lemma 
    (requires True)
    (ensures (let q = coerce (snoc v tl) (1ul +^ l) in
              let r = coerce (cons hd q) (1ul +^ (1ul +^ l)) in
              let s = coerce (cons hd v) (1ul +^ l) in
              let t = coerce (snoc s tl) (1ul +^ (1ul +^ l)) in
             (equal r t)))
  = ()    

let lemma_tail_snoc
    (#a:Type)
    (#l:len_t)
    (v:raw a l{l >^ 1ul /\ ok (+) l 1ul})
    (x:a)
  : Lemma 
    (ensures (let r = coerce (tail (snoc v x)) l in
              let s = coerce (snoc (tail v) x) l in
              r == s))
  = let x1 = create1 x in
    lemma_sub_first_in_append v x1 1ul

let lemma_snoc_inj
    (#a:Type)
    (#l:len_t)
    (v1:raw a l)
    (v2:raw a l{ok (+) l 1ul})
    (x1:a)
    (x2:a)
  : Lemma 
    (requires (equal (snoc v1 x1) (snoc v2 x2)))
    (ensures (x1 == x2 /\ equal v1 v2))
  = let t1 = create1 x1 in 
    let t2 = create1 x2 in 
    lemma_append_inj v1 t1 v2 t2;
    assert(head t1 == head t2)

#set-options "--initial_fuel 2 --max_fuel 2"
let lemma_mem_snoc
    (#a:eqtype)
    (#l:len_t)
    (v:raw a l{ok (+) l 1ul}) 
    (x:a)
  : Lemma (ensures (forall y. mem y (snoc v x) <==> mem y v \/ x=y))
  = lemma_append_count v (create1 x)

let rec find_l
    (#a:Type)
    (#l:len_t)
    (f:a -> Tot bool)
    (v:raw a l)
  : Tot (o:option a{Some? o ==> f (Some?.v o)})
    (decreases (u32_to_int l))
  = if l =^ 0ul then None
    else let hv = head v in
         if f hv then Some hv
         else find_l f (tail v)
    
let rec find_append_some
    (#a:Type)
    (#l1:len_t)
    (#l2:len_t)
    (v1:raw a l1)
    (v2:raw a l2{ok (+) l1 l2})
    (f:a -> Tot bool)
  : Lemma
    (requires (Some? (find_l f v1)))
    (ensures (find_l f (append v1 v2) == find_l f v1))
    (decreases (u32_to_int l1))
  = if l1 =^ 0ul then ()
    else if f (head v1) then ()
    else
      let l1s1 = l1 -^ 1ul in
      let q = append (tail v1) v2 in
      let r = tail (append v1 v2) in
      let _ = assert (equal2 q r) in
      let tl = tail v1 in
      find_append_some tl v2 f

#reset-options "--z3rlimit 10 --use_two_phase_tc true"
let rec find_append_none
    (#a:Type)
    (#l1:len_t)
    (#l2:len_t)
    (v1:raw a l1)
    (v2:raw a l2{ok (+) l1 l2})
    (f:a -> Tot bool)
  : Lemma
    (requires (None? (find_l f v1)))
    (ensures (find_l f (append v1 v2) == find_l f v2))
    (decreases (u32_to_int l1))
  = if l1 =^ 0ul then assert (equal2 (append v1 v2) v2)
    else
      let q = tail (append v1 v2) in
      let r = append (tail  v1) v2 in
      let _ = assert (equal2 q r) in
      find_append_none (tail v1) v2 f

#reset-options "--z3rlimit 30 --use_two_phase_tc true"
let rec find_append_none_v2
    (#a:Type)
    (#l1:len_t)
    (#l2:len_t)
    (v1:raw a l1)
    (v2:raw a l2{ok (+) l1 l2})
    (f:a -> Tot bool)
  : Lemma
    (requires (None? (find_l f v2)))
    (ensures  (find_l f (append v1 v2) == find_l f v1))
    (decreases (u32_to_int l1))
  = if l1 =^ 0ul then assert (equal2 (append v1 v2) v2)
    else if f (head v1) then ()
    else begin
      find_append_none_v2 (tail v1) v2 f;
      let q = tail (append v1 v2) in
      let r = append (tail v1) v2 in
      assert (equal2 q r)
    end
#reset-options "--use_two_phase_tc true"

let find_snoc
    (#a:Type)
    (#l:len_t)
    (v:raw a l{ok (+) l 1ul})
    (x:a)
    (f:a -> Tot bool)
  : Lemma 
    (ensures (let res = find_l f (snoc v x) in
              match res with 
              | None -> find_l f v == None /\ not (f x)
              | Some y -> res == find_l f v \/ (f x /\ x==y)))
    (decreases (u32_to_int l))
  = if Some? (find_l f v) then find_append_some v (create1 x) f
    else find_append_none v (create1 x) f

let un_snoc 
    (#a:Type) 
    (#l:len_t)
    (v:raw a l{l >^ 0ul}) 
  : Tot (r:(raw a (l -^ 1ul) * a){v == snoc (fst r) (snd r)}) 
  = let s', a = split v (l -^ 1ul) in
    assert (equal (snoc s' (index a 0ul)) v);
    s', index a 0ul

let un_snoc_snoc 
    (#a:Type)
    (#l:len_t)
    (v:raw a l{ok (+) l 1ul})
    (x:a)
  : Lemma 
    (requires True)
    (ensures (un_snoc (snoc v x) == (v, x)))
  = let v', x = un_snoc (snoc v x) in
    assert (equal v v')

let rec find_r
    (#a:Type)
    (#l:len_t)
    (f:a -> Tot bool)
    (v:raw a l{ok (+) l 1ul})
  : Tot (o:option a{Some? o ==> f (Some?.v o)})
    (decreases (u32_to_int l))
  = if l =^ 0ul then None
    else let prefix, last = un_snoc v in 
         if f last then Some last
         else find_r f prefix

type found (i:len_t) = True
let rec raw_find_aux
    (#a:Type)
    (#l:len_t)
    (f:a -> Tot bool)
    (v:raw a l)
    (ctr:len_t{ctr <=^ l})
  : Pure (option a)
    (requires (forall (i:index_t v{i >=^ ctr}). not (f v.[i])))
    (ensures (function 
              | None -> forall (i:index_t v). not (f v.[i])
              | Some x -> f x /\  
                (exists (i:index_t v). {:pattern (found i)} found i /\ x == v.[i])))
  = match ctr with
    | 0ul -> None
    | _ -> let i = ctr -^ 1ul in
    if f v.[i]
    then (assert (found i); Some v.[i])
    else raw_find_aux f v i

let raw_find
    (#a:Type)
    (#l:len_t)
    (f:a -> Tot bool)
    (v:raw a l)
  : Pure (option a)
    (requires True)
    (ensures (function
              | None -> forall (i:index_t v). not (f v.[i])
              | Some x -> f x /\ 
                (exists (i:index_t v).{:pattern (found i)} found i /\ x == v.[i])))
  = raw_find_aux f v l

let find_mem 
    (#a:eqtype)
    (#l:len_t)
    (v:raw a l) 
    (f:a -> Tot bool) 
    (x:a{f x})
  : Lemma 
    (requires (mem x v))
    (ensures (Some? (raw_find f v) /\ f (Some?.v (raw_find f v))))
  = match raw_find f v with
    | None -> mem_index x v
    | Some _ -> ()

let for_all
    (#a: Type)
    (#l:len_t)
    (f:a -> Tot bool)
    (v:raw a l)
  : Pure bool
    (requires True)
    (ensures (fun b -> (b == true <==> (forall (i:index_t v) . f v.[i] == true))))
  = None? (raw_find (fun i -> not (f i)) v)

let rec raw_mem_k
    (#a:eqtype)
    (#l:len_t)
    (v:raw a l)
    (n:index_t v)
  : Lemma 
    (requires True)
    (ensures (mem v.[n] v))
    (decreases (u32_to_int n))
    [SMTPat (mem v.[n] v)]
  = if n =^ 0ul then ()
    else let tl = tail v in
         raw_mem_k tl (n -^ 1ul)

let rec raw_to_list
    (#a:Type)
    (#l:len_t)
    (v:raw a l)
  : Tot (r:list a{L.length r = u32_to_int l}) 
    (decreases (u32_to_int l))
  = if l =^ 0ul then []
    else index v 0ul::(raw_to_list (subv v 1ul l))

let rec raw_of_list
    (#a:Type)
    (l:list a{is_u32 (L.length l)})
  : Tot (r:raw a (int_to_u32 (L.length l)))
  = match l with
    | [] -> init #a 0ul (fun _ -> ())
    | hd::tl -> create1 hd @| raw_of_list tl

#set-options "--z3rlimit 30"
let rec lemma_raw_list_bij
    (#a:Type)
    (#l:len_t)
    (v:raw a l)
  : Lemma
    (requires (True))
    (ensures  (raw_of_list (raw_to_list v) == v))
    (decreases (u32_to_int l))
  = if l =^ 0ul then (
       lemma_eq_intro v (raw_of_list (raw_to_list v))
    )
    else (
      lemma_raw_list_bij (subv v 1ul l);
      lemma_eq_intro v (raw_of_list (raw_to_list v))
    )

#set-options "--z3rlimit 50"
let rec lemma_list_raw_bij
    (#a:Type)
    (l:list a{is_u32 (L.length l)})
  : Lemma
    (requires (True))
    (ensures  (raw_to_list (raw_of_list l) == l))
    (decreases (L.length l))
  = if L.length l = 0 then ()
    else (
      lemma_list_raw_bij (L.tl l);
      let hd = L.hd l in let tl = L.tl l in
      assert (raw_to_list (raw_of_list tl) == tl);
      assert (raw_of_list l == create1 hd @| raw_of_list tl);
      let lraw = raw_of_list l in
      let ll32 = int_to_u32 (L.length l) in
      let tlraw = coerce (raw_of_list tl) (ll32 -^ 1ul) in
      lemma_eq_intro tlraw (subv lraw 1ul ll32)
    )
#reset-options "--use_two_phase_tc true"

unfold 
let createL_post 
    (#a:Type0)
    (#len:len_t)
    (l:list a{is_u32 (L.length l)}) 
    (v:raw a len) 
  : GTot Type0 
  = normalize (L.length l = (u32_to_int len)) /\ raw_to_list v == l /\ raw_of_list l == v

let createL
    (#a:Type0)
    (l:list a{is_u32 (L.length l)})
  : Pure (raw a (int_to_u32 (L.length l)))
    (requires True)
    (ensures (fun s -> createL_post l s))
  = let s = raw_of_list l in
    lemma_list_raw_bij l;
    s

let rec lemma_index_is_nth
    (#a:Type)
    (#l:len_t)
    (v:raw a l)
    (i:index_t v)
  : Lemma
    (requires True)
    (ensures (L.index (raw_to_list v) (u32_to_int i) == v.[i]))
    (decreases (u32_to_int i))
  = if i =^ 0ul then ()
    else lemma_index_is_nth (subv v 1ul l) (i -^ 1ul)

////////////////////////////////////////////////////////////////////////////////
//s `contains` x : Type0
//    An undecidable version of `mem`, 
//    for when the vector payload is not an eqtype
  ////////////////////////////////////////////////////////////////////////////////
abstract 
let contains
    (#a:Type)
    (#l:len_t)
    (v:raw a l) 
    (x:a) 
  : Tot Type0 
  = if l =^ 0ul then false
    else (exists (k:index_t v). v.[k] == x)
    
let contains_intro 
    (#a:Type)
    (#l:len_t)
    (v:raw a l) 
    (k:index_t v) 
    (x:a)
  : Lemma 
    (v.[k] == x ==> v `contains` x)
  = ()

let contains_elim 
    (#a:Type)
    (#l:len_t)
    (v:raw a l) 
    (x:a)
  : Lemma (v `contains` x ==> (exists (k:index_t v). v.[k] == x))
  = ()

let lemma_contains_empty 
    (#a:Type)
  : Lemma (forall (x:a). ~ (contains (init 0ul (fun _ -> x)) x)) 
  = ()

let lemma_contains_create1 
    (#a:Type) 
    (x:a) 
  : Lemma (forall (y:a). contains (create1 x) y ==> y == x) 
  = ()

#reset-options "--z3rlimit 20 --use_two_phase_tc true"
private
let intro_append_contains_from_disjunction 
    (#a:Type)
    (#l1:len_t)
    (#l2:len_t)
    (v1:raw a l1)
    (v2:raw a l2{ok (+) l1 l2})
    (x:a) 
  : Lemma 
    (requires (v1 `contains` x \/ v2 `contains` x))
    (ensures (v1 @| v2) `contains` x)
  = contains_elim v1 x;
    contains_elim v2 x;
    let v1v2 = v1 @| v2 in
    assert ((exists i. (v1.[i] == x /\ v1v2.[reinx i v1v2] == x)) \/
            (exists j. (v2.[j] == x /\ v1v2.[reinx (j +^ l1) v1v2] == x)))

#reset-options "--z3rlimit 40 --use_two_phase_tc true"
let append_contains_equiv 
    (#a:Type)
    (#l1:len_t)
    (#l2:len_t)
    (v1:raw a l1) 
    (v2:raw a l2{ok (+) l1 l2}) 
    (x:a)
  : Lemma ((v1 @| v2) `contains` x
           <==>
           (v1 `contains` x \/ v2 `contains` x))
  = contains_elim (v1 @| v2) x;
    let v1v2 = v1 @| v2 in
    assume (v1v2 `contains` x ==>
            ((exists i. (v1.[i] == x /\ v1v2.[reinx i v1v2] == x)) \/
             (exists j. (v2.[j] == x /\ v1v2.[reinx (j +^ l1) v1v2] == x))))
#reset-options "--use_two_phase_tc true"

let snoc_v_x_contains_x
    (#a:Type)
    (#l:len_t)
    (v:raw a l{ok (+) l 1ul})
    (x:a)
  : Lemma ((snoc v x) `contains` x)
  = assert((snoc v x) == (append v (create1 x))); 
    append_contains_equiv v (create1 x) x;
    assert (last (snoc v x) == x)

let snoc_v_x_contains_y
    (#a:Type)
    (#l:len_t)
    (v:raw a l{ok (+) l 1ul})
    (x:a)
    (y:a)
  : Lemma 
    (requires (x == y))
    (ensures ((snoc v x) `contains` y))
  = snoc_v_x_contains_x v x
  
let v_contains_x_snoc_y_contains_x
    (#a:Type)
    (#l:len_t)
    (v:raw a l{ok (+) l 1ul})
    (x:a)
    (y:a)
  : Lemma 
    (requires (v `contains` x))
    (ensures ((snoc v y) `contains` x))
  = append_contains_equiv v (create1 y) x
  
let contains_snoc_r_l_aux
    (#a:Type)
    (#l:len_t)
    (v:raw a l{ok (+) l 1ul})
    (x:a)
    (y:a)
  : Lemma 
    (requires (v `contains` y \/ x==y))
    (ensures ((snoc v x) `contains` y))
  = let c = StrongExcludedMiddle.strong_excluded_middle (x == y) in
    if c then snoc_v_x_contains_y v x y
    else v_contains_x_snoc_y_contains_x v y x

let contains_snoc_r_l_aux2
    (#a:Type)
    (#l:len_t)
    (v:raw a l{ok (+) l 1ul})
    (x:a)
    (y:a)
  : Lemma 
    (requires True)
    (ensures ((v `contains` y \/ x==y) ==> (snoc v x) `contains` y)) 
    // cwinter: not sure how to move the premise to the of the implication
    // into the precondition without breaking contains_snoc_r_l. 
  = let if_p_then_q (#p:Type0) (#q:Type0) 
                    (l:(unit -> Lemma (requires p) (ensures q))) (s:squash p) 
                  : Lemma q 
                  = l s in
    let p1 = x == y in
    let p2 = v `contains` y in
    let c = (snoc v x) `contains` y in
    Classical.or_elim  #p1 #p2 #(fun _ -> (snoc v x) `contains` y)
    (if_p_then_q #_ #c (fun _ -> (snoc_v_x_contains_y v x y)))
    (if_p_then_q #_ #c (fun _ -> (v_contains_x_snoc_y_contains_x v y x)))

let contains_snoc_r_l
    (#a:Type)
    (#l:len_t)
    (v:raw a l{ok (+) l 1ul})
    (x:a)
  : Lemma 
    (requires True)
    (ensures (forall y. v `contains` y \/ x==y ==> (snoc v x) `contains` y))
  = Classical.forall_intro (contains_snoc_r_l_aux2 v x)
  
#reset-options "--z3rlimit 20 --use_two_phase_tc true"
let contains_snoc_l_r
    (#a:Type)
    (#l:len_t)
    (v:raw a l{ok (+) l 1ul})
    (x:a)
  : Lemma 
    (ensures (forall y. (snoc v x) `contains` y ==> v `contains` y \/ x==y))
  = FStar.Classical.forall_intro (append_contains_equiv v (create1 x))
#reset-options "--use_two_phase_tc true"

let contains_snoc 
    (#a:Type)
    (#l:len_t)
    (v:raw a l{ok (+) l 1ul})
    (x:a)
  : Lemma 
    (ensures (forall y. (snoc v x) `contains` y <==> v `contains` y \/ x==y))
  = contains_snoc_r_l v x;
    contains_snoc_l_r v x

let rec lemma_find_l_exists_index
    (#a:Type) 
    (#l:len_t)
    (f:a -> Tot bool)
    (v:raw a l)
  : Lemma 
    (requires (Some? (find_l f v)))
    (ensures (exists i. f v.[i]))
    (decreases (u32_to_int l))
  = assert (l >^ 0ul);
    let m : (m:len_t{m >^ 0ul}) = l in
    let u = coerce v m in
    if f (head u) then ()
    else let tl = tail u in
         let _ = lemma_find_l_exists_index f tl in
         assert (forall (j:index_t tl). tl.[j] == u.[j +^ 1ul])


#reset-options "--initial_fuel 1 --max_fuel 4 --z3rlimit 20 --use_two_phase_tc true"
let rec lemma_find_l_contains 
    (#a:Type) 
    (#l:len_t)
    (f:a -> Tot bool)
    (v:raw a l)
  : Lemma 
    (requires (Some? (find_l f v)))
    (ensures (v `contains` (Some?.v (find_l f v))))
    (decreases (u32_to_int l))
  = assert (l >^ 0ul);
    let x = Some?.v (find_l f v) in
    assert (f x);
    lemma_find_l_exists_index f v;
    assert (exists i. f v.[i]);
    // cwinter: there must be a better way than this...
    let rec raw_find_x_aux (#a:Type) (#l:len_t) (f:a -> Tot bool) (x:a) (v:raw a l) (ctr:len_t{ctr <=^ l})
      : Pure (option a)
        (requires (forall (i:index_t v{i >=^ ctr}). not (f v.[i]) /\ 
                                                    (v.[i] == x \/  ~ (v.[i] == x))))
        (ensures (function 
                 | None -> forall (i:index_t v). not (f v.[i])
                 | Some y -> f y /\  
                             (exists (i:index_t v). {:pattern (found i)} found i /\ 
                                                   y == v.[i] /\ x == y)))
      = match ctr with
        | 0ul -> None
        | _ -> let i = ctr -^ 1ul in
        if (f v.[i])
        then (assert (found i); Some v.[i])
        else raw_find_x_aux x f v i in
    let raw_find_x (#a:Type) (#l:len_t) (f:a -> Tot bool) (x:a) (v:raw a l)
      : Pure (option a)
        (requires True)
        (ensures (function
                 | None -> forall (i:index_t v). not (f v.[i])
                 | Some y -> f y /\ 
                             (exists (i:index_t v). {:pattern (found i)} found i /\ 
                                                    x == v.[i] /\ x == y)))
      = raw_find_x_aux f x v l in
    match raw_find_x f x v with
    | None -> ()
    | Some y -> assert (x == y)

let contains_cons 
    (#a:Type)
    (#l:len_t)
    (hd:a) 
    (tl:raw a l{ok (+) l 1ul}) 
    (x:a)
  : Lemma ((cons hd tl) `contains` x
          ==>
          (x==hd \/ tl `contains` x))
  = append_contains_equiv (create1 hd) tl x

let append_cons_snoc
    (#a:Type) 
    (#l1:len_t{ok (+) l1 1ul})
    (#l2:len_t{ok (+) l2 1ul /\ ok (+) 1ul l2 /\ ok (+) (l2 +^ 1ul) l1})
    (v1:raw a l1)
    (x:a)
    (v2:raw a l2{ok (+) l1 l2})
      : Lemma (let q = append v1 (cons x v2) in
               let r = coerce (append (snoc v1 x) v2) (l1 +^ (1ul +^ l2)) in
               equal q r)
   = ()           
    
let append_subs 
    (#a:Type)
    (#l1:len_t)
    (#l2:len_t)
    (v1:raw a l1)
    (v2:raw a l2{ok (+) l1 l2})
   : Lemma (equal v1 (subv (append v1 v2) 0ul l1) /\
            equal v2 (subv (append v1 v2) l1 (l1 +^ l2)) /\
            (forall (i:len_t) (j:len_t). (
              i <=^ j /\ j <=^ l2 
              ==> (let (q:raw a (j -^ i)) = subv v2 i j in
                   let (r:raw a ((l1 +^ j) -^ (l1 +^ i))) = (subv (append v1 v2) (l1 +^ i) (l1 +^ j)) in
                   equal2 q r))))
   = ()       


// // cwinter: TODO
// #reset-options "--max_fuel 3 --initial_fuel 1 --z3rlimit 20"
// let rec find_l_none_no_index 
//     (#a:Type)
//     (#l:len_t)
//     (v:raw a l{ok (+) l 1ul})
//     (f:a -> Tot bool)
//   : Lemma 
//     (requires (None? (find_l f v)))
//     (ensures (forall (i:index_t v). not (f v.[i])))
//     (decreases (u32_to_int l))
//   = if l =^ 0ul then ()
//     else let ls1 = l -^ 1ul in
//          let m : (m:len_t{m >^ 0ul}) = l in
//          let u = coerce #a #l v m in
//          let (hd:a{not (f hd)}) = head #a #m u in
//          let tl = tail #a #m u in
//          let hd1 = create1 #a hd in
//          assert (not (f hd) /\ hd1.[0ul] == hd /\ not (f hd1.[0ul]));
//          assert (None? (find_l #a #ls1 f tl));
//          assert (None? (find_l #a #1ul f hd1)); // <-- find_append_none wants this.
//          find_l_none_no_index #a #ls1 tl f;
//          assert (equal #a #l u (append #a #1ul #ls1 hd1 tl));
//        	find_append_none #a #1ul #ls1 hd1 tl f
// #reset-options

let suffix_of
    (#a:Type)
    (#l1:len_t)
    (#l2:len_t)    
    (suffix:raw a l2)
    (v:raw a l1)
  : Tot Type0
  = if l2 >^ l1 then False
    else 
      let prelen = l1 -^ l2 in
      (exists (prefix:raw a prelen). (v == prefix @| suffix))

// MOVE TO BASE FROM HERE?
let rec lemma_index_create
    (#a:Type) 
    (n:len_t)
    (x:a)
    (i:len_t{i <^ n})
  : Lemma
    (requires True)
    (ensures ((init n (fun _ -> x)).[i] == x))
    (decreases (u32_to_int n))
    [SMTPat ((init n (fun _ -> x)).[i])]
  = if n =^ 0ul then ()
    else
      if i =^ 0ul then () 
      else lemma_index_create (n -^ 1ul) x (i -^ 1ul)

let rec lemma_index_upd1
    (#a:Type)
    (#l:len_t) 
    (v:raw a l)
    (n:len_t{n <^ l})
    (x:a)
  : Lemma
    (requires True)
    (ensures ((update v n x).[n] == x)) 
    (decreases (u32_to_int l))
    [SMTPat ((update v n x).[n])]
  = if n =^ 0ul then () 
    else lemma_index_upd1 (tail v) (n -^ 1ul) x

let rec lemma_index_upd2
    (#a:Type)
    (#l:len_t)
    (v:raw a l)
    (n:len_t{n <^ l})
    (x:a)
    (i:len_t{i <^ l /\ i <> n})
  : Lemma
    (requires True)
    (ensures ((update v n x).[i] == v.[i])) 
    (decreases (u32_to_int l))
    [SMTPat ((update v n x).[i])]
  = if l =^ 0ul then ()
    else if i =^ 0ul then ()
    else if n =^ 0ul then ()
    else let hd = head v in
         let tl = tail v in
         lemma_index_upd2 tl (n -^ 1ul) x (i -^ 1ul)

abstract 
let rec lemma_index_app1
    (#a:Type) 
    (#l1:len_t)
    (#l2:len_t)
    (v1:raw a l1)
    (v2:raw a l2)
    (i:len_t{i <^ l1 /\ ok (+) l1 l2})
  : Lemma
    (requires True)
    (ensures ((v1 @| v2).[i] == v1.[i])) 
    (decreases (u32_to_int l1))
    [SMTPat ((v1 @| v2).[i])]
  = if l1 =^ 0ul then ()
    else if i =^ 0ul then ()
    else let hd = head v1 in
         let tl = tail v1 in
         lemma_index_app1 tl v2 (i -^ 1ul)

abstract 
let rec lemma_index_app2
    (#a:Type)
    (#l1:len_t)
    (#l2:len_t)
    (v1:raw a l1)
    (v2:raw a l2)
    (i:index_t v1{ok (+) l1 l2 /\ i <^ (l1 +^ l2) /\ l1 <=^ i})
  : Lemma
    (requires True)
    (ensures (index (v1 @| v2) i == index v2 (i -^ l1))) 
    (decreases (u32_to_int l1))
    [SMTPat (index (v1 @| v2) i)]
  = if l1 =^ 0ul then ()
    else if i =^ 0ul then ()
    else let hd = head v1 in
         let tl = tail v1 in
         lemma_index_app2 tl v2 (i -^ 1ul)

abstract
let rec lemma_index_sub
    (#a:Type)
    (#l:len_t)
    (v:raw a l)
    (i:index_t v)
    (j:index_t v{i <=^ j})
    (k:len_t{k <^ j -^ i})
  : Lemma
    (requires True)
    (ensures (index (subv v i j) k == index v (k +^ i))) 
    (decreases (u32_to_int l))
    [SMTPat (index (subv v i j) k)]
  = if i >^ 0ul then lemma_index_sub (tail v) (i -^ 1ul) (j -^ 1ul) k
    else
      if j =^ 0ul then ()
      else if k =^ 0ul then () 
      else let tl = (tail v) in
           lemma_index_sub tl (reinx i tl) (j -^ 1ul) (k -^ 1ul)

abstract 
let lemma_eq_elim
    (#a:Type)
    (#l1:len_t)
    (#l2:len_t)    
    (v1:raw a l1)
    (v2:raw a l2)
  : Lemma
     (requires (l1 =^ l2 /\ equal v1 v2) \/ (equal2 v1 v2))
     (ensures (v1 == v2))
     [SMTPat (equal v1 v2); SMTPat (equal2 v1 v2)]
  = Seq.lemma_eq_elim (reveal v1) (reveal v2)

// MOVE TO BASE UP TO HERE?


let cons_head_tail
    (#a:Type)
    (#l:len_t)
    (v:raw a l{l >^ 0ul})
  : Lemma
    (requires True)
    (ensures (v == cons (head v) (tail v)))
    [SMTPat (cons (head v) (tail v))]
  = lemma_eq_intro v (cons (head v) (tail v))

let head_cons
    (#a:Type)
    (#l:len_t)
    (x:a)
    (v:raw a l{ok (+) l 1ul})
  : Lemma
    (ensures (head (cons x v) == x))
  = ()

let suffix_of_tail
    (#a:Type)
    (#l:len_t)
    (v:raw a l{l >^ 0ul})
  : Lemma
    (requires True)
    (ensures ((tail v) `suffix_of` v))
    [SMTPat ((tail v) `suffix_of` v)]
  = cons_head_tail v

let index_cons_l
    (#a:Type)
    (#l:len_t)
    (c:a)
    (v:raw a l{l >^ 0ul /\ ok (+) l 1ul})
  : Lemma
    (ensures ((cons c v).[0ul] == c))
  = ()

let index_cons_r
    (#a:Type)
    (#l:len_t)
    (c:a)
    (v:raw a l)
    (i:len_t{1ul <=^ i /\ i <=^ l /\ ok (+) l 1ul})
  : Lemma
    (ensures (index (cons c v) i == index v (i -^ 1ul)))
  = ()

let append_cons
    (#a:Type)
    (#l1:len_t)
    (#l2:len_t)
    (c:a)
    (v1:raw a l1)
    (v2:raw a l2{ok (+) l1 l2 /\ ok (+) (l1 +^ l2) 1ul})
  : Lemma
    (ensures (let v1v2 = append v1 v2 in
              let lv1v2 = l1 +^ l2 +^ 1ul in
              let appcons = coerce (append (cons c v1) v2) lv1v2 in
              let consapp = coerce (cons c v1v2) lv1v2 in
              appcons == consapp))
  = lemma_eq_elim (append (cons c v1) v2) (cons c (append v1 v2))

let index_tail
    (#a:Type)
    (#l:len_t)
    (v:raw a l{l >^ 0ul})
    (i:len_t{i <^ l -^ 1ul})
  : Lemma
    (ensures (index (tail v) i == index v (i +^ 1ul)))
  = ()

let mem_cons
    (#a:eqtype)
    (#l:len_t)
    (x:a)
    (v:raw a l{ok (+) l 1ul})
  : Lemma
    (ensures (forall y. mem y (cons x v) <==> mem y v \/ x=y))
  = lemma_append_count (create1 x) v

let snoc_sub_index
    (#a:Type)
    (#l:len_t)
    (v:raw a l)
    (i:index_t v)
    (j:index_t v{i <=^ j})
  : Lemma
    (requires True)
    (ensures (snoc (subv v i j) (index v j) == coerce (subv v i (j +^ 1ul)) (j -^ i +^ 1ul)))
    [SMTPat (snoc (subv v i j) (index v j))]
  = lemma_eq_elim (snoc (subv v i j) (index v j)) (subv v i (j +^ 1ul))

let cons_index_sub
    (#a:Type)
    (#l:len_t)
    (v:raw a l)
    (i:len_t)
    (j:len_t{i <^ j /\ j <=^ l} )
  : Lemma
    (requires True)
    (ensures (cons (index v i) (subv v (i +^ 1ul) j) == coerce (subv v i j) (1ul +^ (j -^ (i +^ 1ul))) ))
    [SMTPat (cons (index v i) (subv v (i +^ 1ul) j))]
  = lemma_eq_elim (cons (index v i) (subv v (i +^ 1ul) j)) (subv v i j)

let sub_is_empty
    (#a:Type)
    (#l:len_t)
    (v:raw a l)
    (i:len_t{i <=^ l})
  : Lemma
    (requires (True))
    (ensures (coerce (subv v i i) 0ul == empty))
    [SMTPat (subv v i i)]
  = lemma_eq_elim (subv v i i) empty

let sub_length
    (#a:Type)
    (#l:len_t)
    (v:raw a l)
  : Lemma
    (requires True)
    (ensures (subv v 0ul l == v))
    [SMTPat (subv v 0ul l)]
  = lemma_eq_elim (subv v 0ul l) v

let sub_sub
    (#a:Type)
    (#l:len_t)
    (v:raw a l)
    (i1:len_t)
    (j1:len_t{i1 <=^ j1 /\ j1 <=^ l} )
    (i2:len_t)
    (j2:len_t{i2 <=^ j2 /\ j2 <=^ j1 -^ i1})
  : Lemma
    (requires (ok (+) i1 i2 /\ ok (+) i1 j2)) 
    (ensures (subv (subv v i1 j1) i2 j2 == coerce (subv v (i1 +^ i2) (i1 +^ j2)) (j2 -^ i2)))
    [SMTPat (subv (subv v i1 j1) i2 j2)]
  = lemma_eq_elim (subv (subv v i1 j1) i2 j2) (subv v (i1 +^ i2) (i1 +^ j2))

#reset-options "--z3rlimit 30 --use_two_phase_tc true"
let raw_of_list_tl
    (#a: Type)
    (l:list a{is_u32 (L.length l) /\ L.length l > 0} )
: Lemma
  (requires True)
  (ensures (let l32s1 = (int_to_u32 (L.length l)) -^ 1ul in
            let rawtl = coerce (raw_of_list (L.tl l)) l32s1 in
            let tlraw = coerce (tail (raw_of_list l)) l32s1 in
            rawtl == tlraw
            ))
  [SMTPat (raw_of_list (L.tl l))]
= lemma_tl (L.hd l) (raw_of_list (L.tl l)); // cwinter: just this goes through, ...
  let l32s1 = (int_to_u32 (L.length l)) -^ 1ul in
  let rawtl = coerce (raw_of_list (L.tl l)) l32s1 in
  let tlraw = coerce (tail (raw_of_list l)) l32s1 in
  lemma_eq_intro rawtl tlraw; // ... this makes it go through faster.
  lemma_eq_elim rawtl tlraw

#reset-options "--z3rlimit 30 --use_two_phase_tc true"
let rec mem_raw_of_list
    (#a:eqtype)
    (x:a)
    (l:list a{is_u32 (L.length l)})
  : Lemma
    (requires True)
    (ensures (mem x (raw_of_list l) == L.mem x l))
    (decreases (L.length l))
    [SMTPat (mem x (raw_of_list l))]
  = match l with
    | [] -> ()
    | hd :: tl ->
      let l32 = int_to_u32 (L.length l) in
      let _ : squash (head (raw_of_list l) == hd) = () in
      let _ : squash (let l32s1 = l32 -^ 1ul in
                      let rawtl = coerce (raw_of_list tl) l32s1 in
                      let tlraw = coerce (tail (raw_of_list l)) l32s1 in
                      tlraw == rawtl) = raw_of_list_tl l in
      let _ : squash (mem x (raw_of_list l) == (x = hd || mem x (raw_of_list tl))) = 
                     lemma_mem_inversion (raw_of_list l) 
      in
        mem_raw_of_list x tl
