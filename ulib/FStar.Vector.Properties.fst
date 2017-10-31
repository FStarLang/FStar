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

unfold 
let all_ok
    (op:len_t -> len_t -> len_t)
    (lst:list len_t)
  : Type
  = let f a x = assert(UInt.size (U32.v (op a x)) U32.n); (op a x) in
    let sum = List.Tot.fold_left f 0ul lst in
    UInt.size (U32.v sum) U32.n

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
    (requires (let open U32 in
               m1 +^ m2 = l1 +^ l2 /\
               equal (u1@|u2) (coerce (v1@|v2) (l1 +^ l2)) /\
               (l1 == m1 \/ l2 == m2)))
    (ensures (l1 = m1 /\
              l2 = m2 /\
              equal u1 v1 /\
              equal u2 v2))
  = FStar.Seq.lemma_append_inj (reveal u1) (reveal u2) (reveal v1) (reveal v2)

let head (#a:Type) (#l:len_t{l <> 0ul}) (v:raw a l)
  : Tot a
  = v.[0ul]

let tail (#a:Type) (#l:len_t{l <> 0ul}) (v:raw a l)
  : Tot (raw a U32.(l -^ 1ul))
  = sub v 1ul l

let head_append
    (#a:Type)
    (#l1:len_t)
    (#l2:len_t)
    (v1:raw a l1{l1 <> 0ul})
    (v2:raw a l2{ok (+) l1 l2})
  : Lemma
    (ensures (head (v1@|v2) == head v1))
  = ()

let tail_append
    (#a:Type)
    (#l1:len_t)
    (#l2:len_t)
    (v1:raw a l1{l1 <> 0ul})
    (v2:raw a l2{ok (+) l1 l2})
  : Lemma
    (ensures (tail (v1@|v2) == tail v1@|v2))
  = Seq.lemma_tail_append (reveal v1) (reveal v2)


open U32

val int_to_u32: x:int -> Tot U32.t
let int_to_u32 x = U32.uint_to_t (UInt.to_uint_t 32 x)

val u32_to_int: (x:U32.t) -> Tot (y:int{y = U32.v x}) 
let u32_to_int x = U32.v x

let subv
    (#a:Type)
    (#l:len_t)
    (v:raw a l)
    (i:len_t)
    (j:len_t{U32.(v i <= v j /\ v j <= v l)})
  : Tot (raw a (j -^ i))
  = Base.sub #a #l v i j

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
    (requires (equal (append v1 v2) (append w1 w2)))
    (ensures (v1.[i] == w1.[reinx i w1]))
  = let rs = append v1 v2 in
    let rt = append w1 w2 in
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
    (requires (equal (append v1 v2) (append w1 w2)))
    (ensures (v2.[i] == w2.[reinx i w2]))
  = let rs = append v1 v2 in
    let rt = append w1 w2 in
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
    cut (raw_length v1v2 == u32_to_int (lv1 +^ lv2));
    cut (raw_length w1w2 == u32_to_int (lw1 +^ lw2))

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

let create1
    (#a:Type)
    (x:a)
  : raw a 1ul
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
  = cut (equal (append (fst (split v i)) (snd (split v i))) v)

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
      let t = tail #a #l v in
      let n = if head #a #l v = x then 1 else 0 in
      n + (count #a #(l -^ 1ul) x t)

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
    (ensures (exists (i:index_t v). (index #a #l v i) == x)) // cwinter: why doesn't it like this?
    (decreases (u32_to_int l))
  = if l =^ 0ul then ()
    else if (head #a #l v) = x then ()
    else
      let t = tail #a #l v in
      mem_index #a #(l -^ 1ul) x t
#reset-options

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
              equal2 #a #(lv1v2 -^ i) v1v2_from_i v1_from_i_v2))
    (decreases (u32_to_int lv1))
  = if i =^ 0ul then ()
    else lemma_sub_first_in_append (tail v1) v2 (i -^ 1ul)

// cwinter: should this go into FStar.Vector.Base.fst?
let lemma_eq_intro
    (#a:Type) 
    (#l:len_t)
    (v1:raw a l)
    (v2:raw a l)
  : Lemma
     (requires (forall (i:len_t{i <^ l}).{:pattern (index v1 (reinx i v1)); (index v2 (reinx i v2))} 
                       index v1 (reinx i v1) == index v2 (reinx i v2)))
     (ensures (equal v1 v2))
  = ()

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
              equal #a #(lv1 +^ lv2) v1v2 hv1tv1v2))
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
  : Tot bool (decreases (u32_to_int l))
  = if l <=^ 1ul
    then true
    else let hd = head #a #l v in
         f hd v.[1ul] && sorted #a #(l -^ 1ul) f (tail #a #l v)

#set-options "--max_fuel 1 --initial_fuel 1"
let rec lemma_append_count
    (#a:eqtype)
    (#llo:len_t)
    (#lhi:len_t)
    (lo:raw a llo)
    (hi:raw a lhi{ok (+) llo lhi})
  : Lemma
    (ensures (forall x. count x (append #a #llo #lhi lo hi) = (count x lo + count x hi)))
    (decreases (u32_to_int llo))
  = if llo =^ 0ul
    then cut (equal #a #(llo +^ lhi) (append #a #llo #lhi lo hi) hi)
    else 
      let (lohi:raw a (llo +^ lhi)) = append lo hi in
      let (hdlo:a) = head #a #llo lo in
      let ltllohi = llo -^ 1ul +^ lhi in
      let (tllohi:raw a ltllohi) = append #a #(llo -^ 1ul) #lhi (tail #a #llo lo) hi in
      let lhdlotllohi = 1ul +^ (llo -^ 1ul +^ lhi) in
      let (hdlotllohi:raw a lhdlotllohi) = cons #a #(llo -^ 1ul +^ lhi) hdlo tllohi in
      (cut (equal hdlotllohi lohi);
           let (ln:len_t) = llo -^ 1ul in
           lemma_append_count #a #ln (tail #a #llo lo) hi;
           let ltl_l_h = (llo -^ 1ul) +^ lhi in
           let (tl_l_h:raw a ltl_l_h) = append #a #(llo -^ 1ul) #lhi (tail #a #llo lo) hi in
           let llh = 1ul +^ ltl_l_h in
           let (lh:raw a llh) = cons #a #ltl_l_h (head #a #llo lo) tl_l_h in
           cut (equal2 #a #(llh -^ 1ul) #ltl_l_h (tail #a #llh lh) tl_l_h))
#reset-options

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
         let tl = tail #a #l v in
         cut (forall (i:len_t{i <^ ltl}). 
                     (index #a #ltl tl i) = v.[i +^ 1ul]);
         lemma_mem_count #a #ltl tl f

let lemma_count_sub
    (#a:eqtype) 
    (#l:len_t)
    (v:raw a l)
    (i:index_t v)
  : Lemma
    (requires True)
    (ensures (forall x. count x v = count x (subv v 0ul i) + count x (subv v i l)))
    (decreases (u32_to_int l))
  = cut (equal v (append (subv v 0ul i) (subv v i l)));
    lemma_append_count (subv v 0ul i) (subv v i l)

type total_order (a:eqtype) (f: (a -> a -> Tot bool)) =
    (forall a. f a a)                                           (* reflexivity   *)
    /\ (forall a1 a2. (f a1 a2 /\ a1<>a2)  <==> not (f a2 a1))  (* anti-symmetry *)
    /\ (forall a1 a2 a3. f a1 a2 /\ f a2 a3 ==> f a1 a3)        (* transitivity  *)
type tot_ord (a:eqtype) = f:(a -> a -> Tot bool){total_order a f}

#set-options "--max_fuel 1 --initial_fuel 1 --z3rlimit  100"
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
         let lophi = append #a #llo #lphi lo phi in
         (cut (equal2 #a #llophi #lphi lophi phi);
          cut (equal #a #lhi (tail #a #lphi phi) hi))
    else let tlo = tail #a #llo lo in
         let ltlo = llo -^ 1ul in
         let tllophi = append #a #ltlo #lphi tlo phi in
         let h = head #a #llo lo in
         sorted_concat_lemma #a #ltlo #lhi f tlo pivot hi;
         lemma_cons_head_append lo phi;
         lemma_tl #a #(llo -^ 1ul +^ lphi) h tllophi

#set-options "--max_fuel 1 --initial_fuel 1 --z3rlimit 30"
let split_5 
    (#a:Type)
    (#l:len_t)
    (v:raw a l) 
    (i:index_t v)
    (j:index_t v{i <^ j})
  : Pure (raw a i * 
          raw a 1ul * 
          raw a (j -^ (i +^ 1ul)) * 
          raw a 1ul * 
          raw a (l -^ (j +^ 1ul)))
    (requires (1ul <^ l -^ i /\ 1ul <^ l -^ j))
    (ensures (fun (b, c, d, e, f) ->
               (v == b @| c @| d @| e @| f)
               /\ equal2 b (subv v 0ul i)
               /\ equal2 c (subv v i (i +^ 1ul))
               /\ equal2 d (subv v (i +^ 1ul) j)
               /\ equal2 e (subv v j (j +^ 1ul))
               /\ equal2 f (subv v (j +^ 1ul) l)
               ))
  = let frag_lo,  rest = split_eq v i in
    let frag_i,   rest = split_eq rest (reinx 1ul rest) in
    let frag_mid, rest = split_eq rest (j -^ (i +^ 1ul)) in
    let frag_j,   (rest:raw a (l -^ i -^ 1ul -^ (j -^ (i +^ 1ul)) -^ 1ul)) = split_eq rest (reinx 1ul rest) in
    let frag_hi        = coerce rest (l -^ (j +^ 1ul)) in
    (frag_lo, frag_i, frag_mid, frag_j, frag_hi)
#reset-options

let lemma_swap_permutes_aux_frag_eq
    (#a:Type)
    (#l:len_t)
    (v:raw a  l)
    (i:index_t v)
    (j:index_t v{i <=^ j})
    (i':index_t v)
    (j':index_t v{i' <=^ j' /\
                  (j <^ i'  //high sub
                  \/ j' <=^ i //low sub
                  \/ (i <^ i' /\ j' <=^ j)) //mid sub
                  /\ ok (+) i 1ul
                  /\ ok (+) j 1ul
                  })
  : Lemma (ensures (subv v i' j' == subv (swap v i j) i' j'
                 /\ subv v i (i +^ 1ul) == coerce (subv (swap v i j) j (j +^ 1ul)) (i +^ 1ul -^ i)
                 /\ subv v j (j +^ 1ul) == coerce (subv (swap v i j) i (i +^ 1ul)) (j +^ 1ul -^ j)))
  = cut (equal (subv v i' j') (subv (swap v i j) i' j'));
    cut (equal (subv v i (i +^ 1ul)) (coerce (subv (swap v i j) j (j +^ 1ul)) (i +^ 1ul -^ i)));
    cut (equal (subv v j (j +^ 1ul)) (coerce (subv (swap v i j) i (i +^ 1ul)) (j +^ 1ul -^ j)))

#set-options "--z3rlimit 20"
let lemma_swap_permutes_aux
    (#a:eqtype)
    (#l:len_t)
    (v:raw a l)
    (i:index_t v) 
    (j:index_t v{i <=^ j /\ ok (+) i 1ul /\ ok (+) j 1ul})
    (x:a)
  : Lemma
    (requires True)
    (ensures (count x v = count x (swap v i j)))
  = if j =^ i
    then cut (equal (swap v i j) v)
    else begin
      let frag_lo, frag_i, frag_mid, frag_j, frag_hi = split_5 v i j in
      lemma_append_count_aux x frag_lo (append frag_i (append frag_mid (append frag_j frag_hi)));
      lemma_append_count_aux x frag_i (append frag_mid (append frag_j frag_hi));
      lemma_append_count_aux x frag_mid (append frag_j frag_hi);
      lemma_append_count_aux x frag_j frag_hi;

      let v' = swap v i j in
      let frag_lo', frag_j', frag_mid', frag_i', frag_hi' = split_5 v' i j in

      lemma_swap_permutes_aux_frag_eq v i j 0ul i;
      lemma_swap_permutes_aux_frag_eq v i j (i +^ 1ul) j;
      lemma_swap_permutes_aux_frag_eq v i j (j +^ 1ul) l;

      lemma_append_count_aux x frag_lo (append frag_j (append frag_mid (append frag_i frag_hi)));
      lemma_append_count_aux x frag_j (append frag_mid (append frag_i frag_hi));
      lemma_append_count_aux x frag_mid (append frag_i frag_hi);
      lemma_append_count_aux x frag_i frag_hi
  end
#reset-options

type permutation (#a:eqtype) (#l:len_t) (v1:raw a l) (v2:raw a l) = (forall i. count i v1 = count i v2)

let lemma_swap_permutes
    (#a:eqtype)
    (#l:len_t)
    (v:raw a l)
    (i:index_t v)
    (j:index_t v{i <=^ j})
  : Lemma
    (permutation v (swap v i j))
  = FStar.Classical.forall_intro #a #(fun x -> count x v = count x (swap v i j)) (lemma_swap_permutes_aux v i j)

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
    cut (equal2 (subv v i j) (append vi1 (subv v (i +^ 1ul) j)));
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
    cut (equal2 (subv v i j) (append (subv v i (j -^ 1ul)) vj1));
    lemma_mem_append (subv v i (j -^ 1ul)) vj1

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
    cut (equal2 (subv v i (j +^ 1ul)) (append (subv v i j) vj1));
    lemma_mem_append (subv v i j) vj1

#set-options "--z3rlimit 10"
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
    cut (equal2 (subv v back len) (append vb1 (subv v (back +^ 1ul) len)));
    lemma_mem_append vb1 (subv v (back +^ 1ul) len)
#reset-options

let swap_frame_lo
    (#a:Type)
    (#l:len_t)
    (v:raw a l)
    (lo:index_t v)
    (i:index_t v{lo <=^ i})
    (j:index_t v{i <=^ j})
  : Lemma 
    (ensures (subv v lo i == subv (swap v i j) lo i))
  = cut (equal (subv v lo i) (subv (swap v i j) lo i))

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
  = cut (equal (subv v lo i') (subv (swap v i j) lo i'))

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
  = cut (equal (subv v k hi) (subv (swap v i j) k hi))

let lemma_swap_sub_commute
    (#a:Type)
    (#l:len_t)
    (v:raw a l)
    (start:index_t v)
    (i:index_t v{start <=^ i})
    (j:index_t v{i <=^ j})
    (len:index_t v{j <^ len})
  : Lemma 
    (ensures (subv (swap v i j) start len == (swap (subv v start len) (i -^ start) (j -^ start))))
  = cut (equal (subv (swap v i j) start len) (swap (subv v start len) (i -^ start) (j -^ start)))

let lemma_swap_permutes_sub 
    (#a:eqtype)
    (#l:len_t)
    (v:raw a l)
    (start:index_t v)
    (i:index_t v{start <=^ i})
    (j:index_t v{i <=^ j})
    (len:index_t v{j <^ len})
  : Lemma 
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
  = cut (equal v (splice v i v j))

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
= cut (equal (swap v i j) (splice v start (swap v i j) len))

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
  = cut (equal (subv v1 m n) (subv v2 m n))

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
  = cut (equal (subv v1 i j) (subv v2 i j))

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
  = cut (equal (tail (subv v i j)) (coerce (subv v (i +^ 1ul) j) (j -^ i -^ 1ul)))

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
  = cut (equal v1 (splice v2 i v1 k))

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
  = cut (equal v1 (splice v2 i v1 k))

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
  = cut (equal v1 (splice v3 i v1 j))

#reset-options "--z3rlimit  20"
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
  = cut (equal2 (subv v2 i k) (append (subv v2 i j)
                                      (subv v2 j k)));
    cut (equal2 (subv v1 i k) (append (subv v2 i j)
                                      (subv v1 j k)));
    lemma_append_count (subv v2 i j) (subv v2 j k);
    lemma_append_count (subv v2 i j) (subv v1 j k)

#reset-options "--z3rlimit  30"
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
               permutation #a #(j -^ i) (subv v2 iq j) (subv v1 iq j)))
    (ensures (permutation (subv v2 i k) (subv v1 i k)))
  = cut (equal2 (subv v2 i k) (append (subv v2 i j)
                                     (subv v2 j k)));
    cut (equal2 (subv v1 i k) (append (subv v1 i j)
                                     (subv v2 j k)));
    lemma_append_count (subv v2 i j) (subv v2 j k);
    lemma_append_count (subv v1 i j) (subv v2 j k)
#reset-options

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
    lemma_append_inj #a #l #1ul #l #1ul v1 t1 v2 t2;
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
    else let hv = head #a #l v in
         if f hv then Some hv
         else find_l #a #(l -^ 1ul) f (tail #a #l v)
    
let rec find_append_some
    (#a:Type)
    (#l1:len_t)
    (#l2:len_t)
    (v1:raw a l1{l1 >^ 0ul}) // cwinter: should work with l1 =^ 0ul too?
    (v2:raw a l2{ok (+) l1 l2})
    (f:a -> Tot bool)
  : Lemma
    (requires (Some? (find_l f v1)))
    (ensures (find_l f (append v1 v2) == find_l f v1))
    (decreases (u32_to_int l1))
  = if f (head v1) then ()
    else
      let q = append #a #(l1 -^ 1ul) #l2 (tail #a #l1 v1) v2 in
      let r = tail #a #(l1 +^ l2) (append #a #l1 #l2 v1 v2) in
      let _ = cut (equal2 #a #(l1 -^ 1ul +^ l2) #(l1 +^ l2 -^ 1ul) q r) in
      find_append_some #a #(l1 -^ 1ul) #l2 (tail #a #l1 v1) v2 f // cwinter: l1 -^ 1ul could be 0ul here, no?

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
  = if l1 =^ 0ul then cut (equal2 (append v1 v2) v2)
    else
      let q = tail #a #(l1 +^ l2) (append v1 v2) in
      let r = append #a #(l1 -^ 1ul) #l2 (tail #a #l1 v1) v2 in
      let _ = cut (equal2 #a #(l1 +^ l2 -^ 1ul) #(l1 -^ 1ul +^ l2 ) q r) in
      find_append_none #a #(l1 -^ 1ul) #l2 (tail #a #l1 v1) v2 f

#set-options "--z3rlimit 30"
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
  = if l1 =^ 0ul then cut (equal2 #a #(l1 +^ l2) #l2 (append #a #l1 #l2 v1 v2) v2)
    else if f (head #a #l1 v1) then ()
    else begin
      find_append_none_v2 #a #(l1 -^ 1ul) #l2 (tail #a #l1 v1) v2 f;
      let q = (tail #a #(l1 +^ l2) (append #a #l1 #l2 v1 v2)) in
      let r = (append #a #(l1 -^ 1ul) #l2 (tail #a #l1 v1) v2) in
      cut (equal2 #a #(l1 +^ l2 -^ 1ul) #(l1 -^ 1ul +^ l2) q r)
    end

// val find_snoc: #a:Type -> s:Seq.seq a -> x:a -> f:(a -> Tot bool)
//                -> Lemma (ensures (let res = find_l f (snoc s x) in
//                            match res with 
//                            | None -> find_l f s == None /\ not (f x)
//                            | Some y -> res == find_l f s \/ (f x /\ x==y)))
//                  (decreases (Seq.length s))
// let find_snoc #a s x f =
//   if Some? (find_l f s) then find_append_some s (Seq.create 1 x) f
//   else find_append_none s (Seq.create 1 x) f

// let un_snoc (#a:Type) (s:seq a{length s <> 0}) : Tot (r:(seq a * a){s == snoc (fst r) (snd r)}) =
//   let s', a = split s (length s - 1) in
//   assert (Seq.equal (snoc s' (Seq.index a 0)) s);
//   s', Seq.index a 0

// let un_snoc_snoc (#a:Type) (s:seq a) (x:a) : Lemma (un_snoc (snoc s x) == (s, x)) =
//   let s', x = un_snoc (snoc s x) in
//   assert (Seq.equal s s')

// val find_r: #a:Type -> f:(a -> Tot bool) -> l:seq a -> Tot (o:option a{Some? o ==> f (Some?.v o)})
//   (decreases (Seq.length l))
// let rec find_r #a f l = 
//   if Seq.length l = 0 then None
//   else let prefix, last = un_snoc l in 
//        if f last then Some last
//        else find_r f prefix

// #set-options "--initial_ifuel 1 --max_ifuel 1 --initial_fuel 0 --max_fuel 0"
// type found (i:nat) = True
// val seq_find_aux : #a:Type -> f:(a -> Tot bool) -> l:seq a
//                    -> ctr:nat{ctr <= Seq.length l}
//                    -> Pure (option a)
//                       (requires (forall (i:nat{ i < Seq.length l /\ i >= ctr}).
//                                         not (f (Seq.index l i) )))
//                       (ensures (function 
//                                   | None -> forall (i:nat{i < Seq.length l}).  not (f (Seq.index l i))
//                                   | Some x -> f x /\  (exists (i:nat{i < Seq.length l}). {:pattern (found i)}
//                   found i /\
//                                                             x == Seq.index l i)))

// let rec seq_find_aux #a f l ctr =
//   match ctr with
//   | 0 -> None
//   | _ -> let i = ctr - 1 in
//   if f (Seq.index l i)
//   then (
//      cut (found i);
//      Some (Seq.index l i))
//   else seq_find_aux f l i

// val seq_find: #a:Type -> f:(a -> Tot bool) -> l:seq a ->
//                      Pure (option a)
//                           (requires True)
//                           (ensures (function
//                                       | None -> forall (i:nat{i < Seq.length l}). not (f (Seq.index l i))
//                                       | Some x -> f x /\ (exists (i:nat{i < Seq.length l}).{:pattern (found i)}
//                                                           found i /\ x == Seq.index l i)))

// let seq_find #a f l =
//   seq_find_aux f l (Seq.length l)

// let find_mem (#a:eqtype) (s:seq a) (f:a -> Tot bool) (x:a{f x})
//    : Lemma (requires (mem x s))
//            (ensures (Some? (seq_find f s) /\ f (Some?.v (seq_find f s))))
//    = match seq_find f s with
//      | None -> mem_index x s
//      | Some _ -> ()

// let for_all
//   (#a: Type)
//   (f: (a -> Tot bool))
//   (l: seq a)
// : Pure bool
//   (requires True)
//   (ensures (fun b -> (b == true <==> (forall (i: nat {i < Seq.length l} ) . f (index l i) == true))))
// = None? (seq_find (fun i -> not (f i)) l)

// #set-options "--initial_ifuel 1 --max_ifuel 1 --initial_fuel 1 --max_fuel 1"
// val seq_mem_k: #a:eqtype -> s:seq a -> n:nat{n < Seq.length s} -> 
//     Lemma (requires True)
//     (ensures (mem (Seq.index s n) s))
//     (decreases n)
//     [SMTPat (mem (Seq.index s n) s)]
// let rec seq_mem_k #a s n = 
//   if n = 0 then ()
//   else let tl = tail s in
//        seq_mem_k tl (n - 1)

// module L = FStar.List.Tot

// val seq_to_list: #a:Type -> s:seq a -> Tot (l:list a{L.length l = length s}) (decreases (length s))
// let rec seq_to_list #a s =
//   if length s = 0 then []
//   else index s 0::seq_to_list (subv s 1 (length s))

// val seq_of_list: #a:Type -> l:list a -> Tot (s:seq a{L.length l = length s})
// let rec seq_of_list #a l =
//   match l with
//   | [] -> createEmpty #a
//   | hd::tl -> create 1 hd @| seq_of_list tl

// val lemma_seq_list_bij: #a:Type -> s:seq a -> Lemma
//   (requires (True))
//   (ensures  (seq_of_list (seq_to_list s) == s))
//   (decreases (length s))
// let rec lemma_seq_list_bij #a s =
//   if length s = 0 then (
//     Seq.lemma_eq_intro s (seq_of_list (seq_to_list s))
//   )
//   else (
//     lemma_seq_list_bij (subv s 1 (length s));
//     lemma_eq_intro s (seq_of_list (seq_to_list s))
//   )

// val lemma_list_seq_bij: #a:Type -> l:list a -> Lemma
//   (requires (True))
//   (ensures  (seq_to_list (seq_of_list l) == l))
//   (decreases (L.length l))
// let rec lemma_list_seq_bij #a l =
//   if L.length l = 0 then ()
//   else (
//     lemma_list_seq_bij #a (L.tl l);
//     let hd = L.hd l in let tl = L.tl l in
//     cut (seq_to_list (seq_of_list tl) == tl);
//     cut (seq_of_list l == create 1 hd @| seq_of_list tl);
//     lemma_eq_intro (seq_of_list tl) (subv (seq_of_list l) 1 (length (seq_of_list l)))
//   )

// unfold let createL_post (#a:Type0) (l:list a) (s:seq a) : GTot Type0 =
//   normalize (L.length l = length s) /\ seq_to_list s == l /\ seq_of_list l == s

// val createL: #a:Type0 -> l:list a -> Pure (seq a)
//   (requires True)
//   (ensures (fun s -> createL_post #a l s))
// let createL #a l =
//   let s = seq_of_list l in
//   lemma_list_seq_bij l;
//   s

// val lemma_index_is_nth: #a:Type -> s:seq a -> i:nat{i < length s} -> Lemma
//   (requires True)
//   (ensures  (L.index (seq_to_list s) i == index s i))
//   (decreases i)
// let rec lemma_index_is_nth #a s i =
//   if i = 0 then ()
//   else (
//     lemma_index_is_nth (subv s 1 (length s)) (i-1)
//   )

// ////////////////////////////////////////////////////////////////////////////////
// //s `contains` x : Type0
// //    An undecidable version of `mem`, 
// //    for when the sequence payload is not an eqtype
// ////////////////////////////////////////////////////////////////////////////////
// abstract let contains (#a:Type) (s:seq a) (x:a) : Tot Type0 = 
//   exists (k:nat). k < Seq.length s /\ Seq.index s k == x
    
// let contains_intro (#a:Type) (s:seq a) (k:nat) (x:a)
//   : Lemma (k < Seq.length s /\ Seq.index s k == x
//       ==>
//      s `contains` x)
//   = ()

// let contains_elim (#a:Type) (s:seq a) (x:a)
//   : Lemma (s `contains` x
//       ==>
//     (exists (k:nat). k < Seq.length s /\ Seq.index s k == x))
//   = ()

// let lemma_contains_empty (#a:Type) : Lemma (forall (x:a). ~ (contains Seq.createEmpty x)) = ()

// let lemma_contains_singleton (#a:Type) (x:a) : Lemma (forall (y:a). contains (create 1 x) y ==> y == x) = ()

// private let intro_append_contains_from_disjunction (#a:Type) (s1:seq a) (v2:seq a) (x:a)
//     : Lemma (requires s1 `contains` x \/ v2 `contains` x)
//          (ensures (append s1 v2) `contains` x)
//     = let open FStar.Classical in 
//       let open FStar.StrongExcludedMiddle in
//       let open FStar.Squash in
//       if strong_excluded_middle (s1 `contains` x)
//       then ()
//       else let s = append s1 v2 in
//      exists_elim (s `contains` x) (get_proof (v2 `contains` x)) (fun k -> 
//            assert (Seq.index s (Seq.length s1 + k) == x))

// let append_contains_equiv (#a:Type) (s1:seq a) (v2:seq a) (x:a)
//   : Lemma ((append s1 v2) `contains` x
//       <==>
//        (s1 `contains` x \/ v2 `contains` x))
//   = FStar.Classical.move_requires (intro_append_contains_from_disjunction s1 v2) x

// val contains_snoc : #a:Type -> s:Seq.seq a -> x:a ->
//    Lemma (ensures (forall y. (snoc s x) `contains` y  <==> s `contains` y \/ x==y))
// let contains_snoc #a s x =
//   FStar.Classical.forall_intro (append_contains_equiv s (Seq.create 1 x))

// let rec lemma_find_l_contains (#a:Type) (f:a -> Tot bool) (l:seq a)
//   : Lemma (requires True) (ensures Some? (find_l f l) ==> l `contains` (Some?.v (find_l f l)))
//           (decreases (Seq.length l))
//   = if length l = 0 then ()
//     else if f (head l) then ()
//     else lemma_find_l_contains f (tail l)

// let contains_cons (#a:Type) (hd:a) (tl:Seq.seq a) (x:a)
//   : Lemma ((cons hd tl) `contains` x
//      <==>
//      (x==hd \/ tl `contains` x))
//   = append_contains_equiv (Seq.create 1 hd) tl x

// let append_cons_snoc (#a:Type) (u: Seq.seq a) (x:a) (v:Seq.seq a)
//     : Lemma (Seq.equal (Seq.append u (cons x v))
//            (Seq.append (snoc u x) v))
//     = ()           
    
// let append_subs (#a:Type) (s1:Seq.seq a) (v2:Seq.seq a)
//    : Lemma ( Seq.equal s1 (Seq.sub (Seq.append s1 v2) 0 (Seq.length s1)) /\
//        Seq.equal v2 (Seq.sub (Seq.append s1 v2) (Seq.length s1) (Seq.length s1 + Seq.length v2)) /\
//        (forall (i:nat) (j:nat).
//     i <= j /\ j <= Seq.length v2 ==>
//     Seq.equal (Seq.sub v2 i j) 
//         (Seq.sub (Seq.append s1 v2) (Seq.length s1 + i) (Seq.length s1 + j))))
//    = ()       


// val find_l_none_no_index (#a:Type) (s:Seq.seq a) (f:(a -> Tot bool)) :
//   Lemma (requires (None? (find_l f s)))
//         (ensures (forall (i:nat{i < Seq.length s}). not (f (Seq.index s i))))
//   (decreases (Seq.length s))
// #reset-options
// let rec find_l_none_no_index #a s f =
//   if Seq.length s = 0
//   then ()
//   else (assert (not (f (head s)));
//         assert (None? (find_l f (tail s)));
//         find_l_none_no_index (tail s) f;
//   assert (Seq.equal s (cons (head s) (tail s)));
//   find_append_none (create 1 (head s)) (tail s) f)

// (** More properties, with new naming conventions *)

// let suffix_of
//   (#a: Type)
//   (s_suff s: seq a)
// = exists s_pref . (s == append s_pref s_suff)

// let cons_head_tail
//   (#a: Type)
//   (s: seq a {length s > 0})
// : Lemma
//   (requires True)
//   (ensures (s == cons (head s) (tail s)))
//   [SMTPat (cons (head s) (tail s))]
// = let _ : squash (subv s 0 1 == create 1 (index s 0)) =
//       lemma_index_sub s 0 1 0;
//       lemma_index_create 1 (index s 0) 0;
//       lemma_eq_elim (subv s 0 1) (create 1 (index s 0))
//   in
//   lemma_split s 1

// let head_cons
//   (#a: Type)
//   (x: a)
//   (s: seq a)
// : Lemma
//   (ensures (head (cons x s) == x))
// = ()

// let suffix_of_tail
//   (#a: Type)
//   (s: seq a {length s > 0})
// : Lemma
//   (requires True)
//   (ensures ((tail s) `suffix_of` s))
//   [SMTPat ((tail s) `suffix_of` s)]
// = cons_head_tail s    

// let index_cons_l
//   (#a: Type)
//   (c: a)
//   (s: seq a)
// : Lemma
//   (ensures (index (cons c s) 0 == c))
// = ()

// let index_cons_r
//   (#a: Type)
//   (c: a)
//   (s: seq a)
//   (i: nat {1 <= i /\ i <= length s})
// : Lemma
//   (ensures (index (cons c s) i == index s (i - 1)))
// = ()

// let append_cons
//   (#a: Type)
//   (c: a)
//   (s1 v2: seq a)
// : Lemma
//   (ensures (append (cons c s1) v2 == cons c (append s1 v2)))
// = lemma_eq_elim (append (cons c s1) v2) (cons c (append s1 v2))

// let index_tail
//   (#a: Type)
//   (s: seq a {length s > 0})
//   (i: nat {i < length s - 1} )
// : Lemma
//   (ensures (index (tail s) i == index s (i + 1)))
// = ()

// let mem_cons
//   (#a:eqtype)
//   (x:a)
//   (s:seq a)
// : Lemma
//   (ensures (forall y. mem y (cons x s) <==> mem y s \/ x=y))
// = lemma_append_count (create 1 x) s

// let snoc_sub_index
//   (#a: Type)
//   (s: seq a)
//   (i: nat)
//   (j: nat {i <= j /\ j < length s} )
// : Lemma
//   (requires True)
//   (ensures (snoc (subv s i j) (index s j) == sub s i (j + 1)))
//   [SMTPat (snoc (subv s i j) (index s j))]
// = lemma_eq_elim (snoc (subv s i j) (index s j)) (subv s i (j + 1))

// let cons_index_sub
//   (#a: Type)
//   (s: seq a)
//   (i: nat)
//   (j: nat {i < j /\ j <= length s} )
// : Lemma
//   (requires True)
//   (ensures (cons (index s i) (subv s (i + 1) j) == sub s i j))
//   [SMTPat (cons (index s i) (subv s (i + 1) j))]
// = lemma_eq_elim (cons (index s i) (subv s (i + 1) j)) (subv s i j)

// let sub_is_empty
//   (#a: Type)
//   (s: seq a)
//   (i: nat {i <= length s})
// : Lemma
//   (requires True)
//   (ensures (subv s i i == createEmpty))
//   [SMTPat (subv s i i)]
// = lemma_eq_elim (subv s i i) createEmpty

// let sub_length
//   (#a: Type)
//   (s: seq a)
// : Lemma
//   (requires True)
//   (ensures (subv s 0 (length s) == s))
//   [SMTPat (subv s 0 (length s))]
// = lemma_eq_elim (subv s 0 (length s)) s

// let sub_sub
//   (#a: Type)
//   (s: seq a)
//   (i1: nat)
//   (j1: nat {i1 <= j1 /\ j1 <= length s} )
//   (i2: nat)
//   (j2: nat {i2 <= j2 /\ j2 <= j1 - i1} )
// : Lemma
//   (requires True)
//   (ensures (subv (subv s i1 j1) i2 j2 == sub s (i1 + i2) (i1 + j2)))
//   [SMTPat (subv (subv s i1 j1) i2 j2)]
// = lemma_eq_elim (subv (subv s i1 j1) i2 j2) (subv s (i1 + i2) (i1 + j2))

// let seq_of_list_tl
//   (#a: Type)
//   (l: list a { List.Tot.length l > 0 } )
// : Lemma
//   (requires True)
//   (ensures (seq_of_list (List.Tot.tl l) == tail (seq_of_list l)))
//   [SMTPat (seq_of_list (List.Tot.tl l))]
// = lemma_tl (List.Tot.hd l) (seq_of_list (List.Tot.tl l))

// let rec mem_seq_of_list
//   (#a: eqtype)
//   (x: a)
//   (l: list a)
// : Lemma
//   (requires True)
//   (ensures (mem x (seq_of_list l) == List.Tot.mem x l))
//   [SMTPat (mem x (seq_of_list l))]
// = match l with
//   | [] -> ()
//   | y :: q ->
//     let _ : squash (head (seq_of_list l) == y) = () in
//     let _ : squash (tail (seq_of_list l) == seq_of_list q) = seq_of_list_tl l in
//     let _ : squash (mem x (seq_of_list l) == (x = y || mem x (seq_of_list q))) =
//      lemma_mem_inversion (seq_of_list l)
//     in
//     mem_seq_of_list x q
