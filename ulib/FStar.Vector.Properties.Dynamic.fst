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

module FStar.Vector.Properties.Dynamic

open FStar.Vector.Base
open FStar.Vector.Properties
module S = FStar.Seq
module U32 = FStar.UInt32
module L = FStar.List.Tot

open FStar.UInt32

let int_to_u32 (x:int): Tot U32.t = U32.uint_to_t (UInt.to_uint_t 32 x)
let u32_to_int (x:U32.t): Tot (y:int{y = U32.v x}) = U32.v x
let is_u32 (x:int): bool = UInt.fits x U32.n


type vector a = Vector.Base.t a
type vector_index v = Vector.Base.index_t (as_raw v)

let equal (#a:Type) (x:vector a) (y:vector a): Tot Type0 = x == y

let subv
    (#a:Type)
    (v:vector a)
    (i:len_t)
    (j:len_t{i <=^ j /\ j <=^ (len v)})
  : Tot (r:vector a{len r =^ j -^ i})
  = FStar.Vector.Base.slice #a v i j


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
    (v:vector a)
    (m:len_t{len v =^ m})
  : Tot (r:vector a{len r =^ m})
  = v

let append_inj
    (#a:Type)
    (u1:vector a)
    (u2:vector a{ok (+) (len u1) (len u2)})
    (v1:vector a)
    (v2:vector a{ok (+) (len v1) (len v2)})
  : Lemma
    (requires ((len v1) +^ (len v2) =^ (len u1) +^ (len u2) /\
               (u1 @@ u2) == (coerce (v1@@v2) ((len v1) +^ (len v2))) /\
               (len v1 =^ len u1 \/ len v2 =^ len u2)))
    (ensures (len v1 =^ len u1 /\ len v2 =^ len u2 /\ u1 == v1 /\ u2 == v2))
  = Vector.Properties.append_inj (as_raw v1) (as_raw v2) (as_raw u1) (as_raw u2)

let head 
    (#a:Type) 
    (v:vector a{len v >^ 0ul})
  : Tot a
  = v.(0ul)

let tail 
    (#a:Type) 
    (v:vector a{len v >^ 0ul})
  : Tot (r:vector a{len r =^ len v -^ 1ul})
  = subv v 1ul (len v)

let head_append
    (#a:Type)
    (v1:vector a{len v1 >^ 0ul})
    (v2:vector a{ok (+) (len  v1) (len v2)})
  : Lemma
    (ensures (head (v1@@v2) == head v1))
  = ()

let tail_append
    (#a:Type)
    (v1:vector a{(len v1) >^ 0ul})
    (v2:vector a{ok (+) (len v1) (len v2)})
  : Lemma
    (ensures (tail (v1@@v2) == tail v1@@v2))
  = Vector.Properties.tail_append (as_raw v1) (as_raw v2)

let reinx 
    (#a:Type) 
    (i:len_t) 
    (v:vector a{i <^ len v}) 
  : Tot (vector_index v) 
  = let (r:len_t{r <^ len v}) = i in
    r
      
let lemma_append_inj_l
    (#a:Type) 
    (v1:vector a)
    (v2:vector a{len v1 =^ len v2 /\ ok (+) (len v1) (len v2)})
    (w1:vector a) 
    (w2:vector a)
    (i:vector_index v1{len w1 =^ len w2 /\ ok (+) (len w1) (len w2)})
  : Lemma
    (requires ((v1 @@ v2) == (w1 @@ w2)))
    (ensures (v1.(i) == w1.(reinx i w1)))
  = let rs = v1 @@ v2 in
    let rt = w1 @@ w2 in
    let rl = len v1 +^ len v2 in
    assert (v1.(i) == rs.(reinx i rs));
    assert (w1.(reinx i w1) == rt.(reinx i rt))

let lemma_append_inj_r
    (#a:Type)
    (v1:vector a)
    (v2:vector a)
    (w1:vector a)
    (w2:vector a)
    (i:vector_index v2{len v1 =^ len v2 /\ len w1 =^ len w2 /\ 
                       ok (+) (len v1) (len v2) /\ ok (+) (len w1) (len w2)})
  : Lemma 
    (requires ((v1 @@ v2) == (w1 @@ w2)))
    (ensures (v2.(i) == w2.(reinx i w2)))
  = let rs = v1 @@ v2 in
    let rt = w1 @@ w2 in
    let rl = (len v1) +^ (len v2) in
    let ipl1 = i +^ len v1 in
    assert (v2.(i) == rs.(ipl1));
    assert (w2.(reinx i w2) == rt.(ipl1))

let lemma_append_len_disj
    (#a:Type)
    (v1:vector a)
    (v2:vector a{ok (+) (len v1) (len v2)})
    (w1:vector a)
    (w2:vector a{ok (+) (len w1) (len w2)})
  : Lemma 
    (requires ((len v1 =^ len w1 \/ (len v2) =^ (len w2)) /\ v1 @@ v2 == w1 @@ w2))
    (ensures (len v1 =^ (len w1) /\ len v2 =^ len w2))
  = let v1v2 = v1 @@ v2 in
    let w1w2 = w1 @@ w2 in
    assert (length v1v2 == u32_to_int (len v1 +^ len v2));
    assert (length w1w2 == u32_to_int (len w1 +^ len w2))

let lemma_append_inj
    (#a:Type)
    (v1:vector a)
    (v2:vector a{ok (+) (len v1) (len v2)})
    (w1:vector a)
    (w2:vector a{ok (+) (len w1) (len w2)})
  : Lemma
    (requires ((len v1 = len w1 \/ len v2 = len w2) /\ v1 @@ v2 == w1 @@ w2))
    (ensures ((len v1 =^ len w1 /\ len v2 =^ len w2 /\ v1 == w1 /\ v2 == w2)))
  = Vector.Properties.lemma_append_inj (as_raw v1) (as_raw v2) (as_raw w1) (as_raw w2)

let last
    (#a:Type) 
    (v:vector a {len v >^ 0ul})
  : Tot a
  = v.(len v -^ 1ul)

let empty
    (#a:Type)
  : Tot (r:vector a{len r =^ 0ul})
  = from_raw (init #a 0ul (fun _ -> ()))

let create1
    (#a:Type)
    (x:a)
  : Tot (r:vector a{len r =^ 1ul})
  = from_raw (init 1ul (fun _ -> x))

let createN
    (#a:Type)
    (l:len_t)
    (contents: (i:nat { i < U32.v l } -> Tot a))
  : Tot (r:vector a{len r =^ l})
  = from_raw (init #a l contents) 

let cons
    (#a:Type)
    (x:a)
    (v:vector a{ok (+) (len v) 1ul})
  : Tot (r:vector a{len r =^ 1ul +^ (len v)})
  = (create1 x) @@ v

let lemma_cons_inj
    (#a:Type)
    (x1:a) 
    (x2:a) 
    (v1:vector a) 
    (v2:vector a{ok (+) (len v1) 1ul /\ ok (+) (len v2) 1ul})
  : Lemma 
    (requires (cons x1 v1 == cons x2 v2))
    (ensures (v1 == v2))
  = let w1 = create1 x1 in 
    let w2 = create1 x2 in 
    lemma_append_inj w1 v1 w2 v2;
    assert(w1.(0ul) == w2.(0ul))

let split
    (#a:Type)
    (v:vector a)
    (i:vector_index v)
  : Tot (r1:vector a{len r1 =^ i} * 
         r2:vector a{len r2 =^ (len v -^ i)})
  = from_raw (init i (fun j -> v.(int_to_u32 j))),
    from_raw (init (len v -^ i) (fun j -> v.(i +^ int_to_u32 j)))

let lemma_split
    (#a:Type)
    (v:vector a) 
    (i:vector_index v)
  : Lemma 
    (ensures (let f, s = split v i in (f @@ s) == v))
  = let f, s = split v i in
    let rv = as_raw v in    
    let rf, rs = Vector.Properties.split rv i in
    Vector.Properties.lemma_split rv i;
    assert (Vector.Base.equal rf (as_raw f));
    assert (Vector.Base.equal rs (Vector.Properties.coerce (as_raw s) (len v -^ i)))
  
let split_eq
    (#a:Type)
    (v:vector a)
    (i:vector_index v) 
  : Pure (r1:vector a{len r1 =^ i} * (r2:vector a{len r2 =^ len v -^ i}))
    (requires True)
    (ensures (fun x -> ((fst x) @@ (snd x) == v)))
  = let x = split v i in
    lemma_split v i;
    x

let count 
    (#a:eqtype)
    (x:a) 
    (v:vector a)
  : Tot nat 
  = Vector.Properties.count x (as_raw v)

let mem
    (#a:eqtype)
    (x:a) 
    (v:vector a) 
  : Tot bool
  = Vector.Properties.mem x (as_raw v)

let mem_index 
    (#a:eqtype) 
    (x:a) 
    (v:vector a)
  : Lemma 
    (requires (mem x v))
    (ensures (exists (i:vector_index v). v.(i) == x))
  = Vector.Properties.mem_index x (as_raw v)

let swap
    (#a:Type) 
    (v:vector a) 
    (i:vector_index v)
    (j:vector_index v) 
  : Tot (r:vector a{len r =^ len v})
  = from_raw (Vector.Properties.swap (as_raw v) i j)

let lemma_slice_append
    (#a:Type)
    (v1:vector a{len v1 >=^ 1ul})
    (v2:vector a{ok (+) (len v1) (len v2)})
  : Lemma
    (ensures (let s1 = subv v1 0ul 1ul in
              let s2 = subv v1 1ul (len v1) in
              let v1v2 = v1 @@ v2 in
              let s2v2 = s2 @@ v2 in
              let s1s2v2 = s1 @@ s2v2 in
              v1v2 == s1s2v2))
  = Vector.Properties.lemma_sub_append (as_raw v1) (as_raw v2)

let lemma_slice_first_in_append
    (#a:Type)
    (v1:vector a)
    (v2:vector a{ok (+) (len v1) (len v2)}) 
    (i:vector_index v1{ok (+) ((len v1) -^ i) (len v2)})
  : Lemma
    (ensures (let v1v2 = v1 @@ v2 in
              let lv1v2 = len v1v2 in
              let v1_from_i = subv v1 i (len v1) in
              let v1_from_i_v2 = v1_from_i @@ v2 in
              let v1v2_from_i = subv v1v2 i lv1v2 in
              v1v2_from_i == v1_from_i_v2))
  = Vector.Properties.lemma_sub_first_in_append (as_raw v1) (as_raw v2) i

let slice_update
    (#a:Type)
    (v:vector a)
    (i:vector_index v)
    (j:vector_index v{i <=^ j})
    (k:vector_index v{k <^ i \/ j <=^ k})
    (x:a)
  : Lemma
    (ensures (subv (v.(k) <- x) i j == subv v i j))
    [SMTPat (subv (v.(k) <- x) i j)]
  = Vector.Properties.sub_update (as_raw v) i j k x

let update_slice
    (#a:Type)
    (v:vector a)
    (i:vector_index v)
    (j:vector_index v{i <=^ j})
    (k:vector_index v{ok (+) i k /\ i +^ k <^ j})
    (x:a)
  : Lemma
    (ensures (let t = subv v i j in
              (t.(reinx k t) <- x) == subv (v.(i +^ k) <- x) i j))
    [SMTPat ((subv v i j).(k) <- x)]
  = Vector.Properties.update_sub (as_raw v) i j k x

let lemma_cons_head_append
    (#a:Type) 
    (v1:vector a{len v1 >^ 0ul})
    (v2:vector a{ok (+) (len v1) (len v2)})
  : Lemma
    (ensures (let (v1v2:vector a{len v1v2 =^ (len v1 +^ len v2)}) = v1 @@ v2 in
              let (hv1:a) = head v1 in
              let (tv1:vector a{len tv1 =^ len v1 -^ 1ul}) = tail v1 in
              let (tv1v2:vector a{len tv1v2 =^ len v1 +^ len v2 -^ 1ul}) = tv1 @@ v2 in
              let magic_len = 1ul +^ ((len v1 -^ 1ul) +^ len v2) in
              let (hv1tv1v2:vector a{len hv1tv1v2 =^ magic_len}) = cons hv1 tv1v2 in              
              magic_len = len v1 +^ len v2 /\
              v1v2 == hv1tv1v2))
  = Vector.Properties.lemma_cons_head_append (as_raw v1) (as_raw v2)

let lemma_tl
    (#a:Type)
    (hd:a)
    (tl:vector a{ok (+) (len tl) 1ul})
  : Lemma
    (ensures (tail (cons hd tl)) == tl)
  = Vector.Properties.lemma_tl hd (as_raw tl)

let sorted
    (#a:Type) 
    (f:a -> a -> Tot bool)
    (v:vector a)
  : Tot bool
  = Vector.Properties.sorted f (as_raw v)
  
let lemma_append_count
    (#a:eqtype)
    (lo:vector a)
    (hi:vector a{ok (+) (len lo) (len hi)})
  : Lemma
    (ensures (forall x. (count x (lo @@ hi)) = ((count x lo) + (count x hi))))
  = Vector.Properties.lemma_append_count (as_raw lo) (as_raw hi)

let lemma_append_count_aux
    (#a:eqtype)
    (x:a)
    (lo:vector a)
    (hi:vector a{ok (+) (len lo) (len hi)})
  : Lemma
    (requires True)
    (ensures (count x (lo @@ hi) = (count x lo + count x hi)))
  = lemma_append_count lo hi

let lemma_mem_inversion
    (#a:eqtype)
    (v:vector a{len v >^ 0ul})
    : Lemma
  (ensures (forall x. mem x v = (x=head v || mem x (tail v))))
= ()

let lemma_mem_count
    (#a:eqtype)
    (v:vector a)
    (f:a -> Tot bool)
  : Lemma
    (requires (forall (i:vector_index v). f v.(i)))
    (ensures (forall (x:a). mem x v ==> f x))
  = Vector.Properties.lemma_mem_count (as_raw v) f

let lemma_count_slice
    (#a:eqtype) 
    (v:vector a)
    (i:vector_index v)
  : Lemma
    (requires True)
    (ensures (forall x. count x v = count x (subv v 0ul i) + count x (subv v i (len v))))
  = Vector.Properties.lemma_count_sub (as_raw v) i

let sorted_concat_lemma
    (#a:eqtype)
    (f:a -> a -> Tot bool{total_order a f})
    (lo:vector a{sorted f lo})
    (pivot:a)
    (hi:vector a{sorted f hi /\ ok (+) (len lo) (len hi) /\ ok (+) (len lo +^ len hi) 1ul})
  : Lemma 
    (requires (forall y. (mem y lo ==> f y pivot) /\
                         (mem y hi ==> f pivot y)))
    (ensures (sorted f (lo @@ (cons pivot hi))))
  = Vector.Properties.sorted_concat_lemma f (as_raw lo) pivot (as_raw hi)

let split_5 
    (#a:Type)
    (v:vector a) 
    (i:vector_index v{ok (+) i 1ul /\ ok (Prims.op_Subtraction) (len v) i})
    (j:vector_index v{i <^ j /\ ok (+) j 1ul /\ ok (+) i j /\ 1ul <^ (len v) -^ j})
  : Pure (v1:vector a{len v1 =^ i} * 
          v2:vector a{len v2 =^ 1ul} * 
          v3:vector a{len v3 =^ j -^ (i +^ 1ul)}* 
          v4:vector a{len v4 =^ 1ul} * 
          v5:vector a{len v5 =^ len v -^ (j +^ 1ul)})
    (requires (True))
    (ensures (fun (b, c, d, e, f) ->
               (v == b @@ c @@ d @@ e @@ f)
               /\ b == (subv v 0ul i)
               /\ c == (subv v i (i +^ 1ul))
               /\ d == (subv v (i +^ 1ul) j)
               /\ e == (subv v j (j +^ 1ul))
               /\ f == (subv v (j +^ 1ul) (len v))
               ))
  = let a, b, c, d, e = Vector.Properties.split_5 (as_raw v) i j in
    (from_raw a, from_raw b, from_raw c, from_raw d, from_raw e)

let lemma_swap_permutes_aux_frag_eq
    (#a:Type)
    (v:vector a)
    (i:vector_index v)
    (j:vector_index v{i <=^ j /\ ok (+) i 1ul /\ ok (+) j 1ul})
    (i':vector_index v)
    (j':vector_index v{i' <=^ j' /\ ok (+) i' 1ul /\ ok (+) j' 1ul /\
              (j <^ i'  //high sub
              \/ j' <=^ i //low sub
              \/ (i <^ i' /\ j' <=^ j)) //mid sub 
              })
  : Lemma (ensures (subv v i' j' == subv (swap v i j) i' j'
                 /\ subv v i (i +^ 1ul) == coerce (subv (swap v i j) j (j +^ 1ul)) (i +^ 1ul -^ i)
                 /\ subv v j (j +^ 1ul) == coerce (subv (swap v i j) i (i +^ 1ul)) (j +^ 1ul -^ j)))
  = Vector.Properties.lemma_swap_permutes_aux_frag_eq (as_raw v) i j i' j'

let lemma_swap_permutes_aux
    (#a:eqtype)
    (v:vector a)
    (i:vector_index v) 
    (j:vector_index v{i <=^ j})
    (x:a)
  : Lemma
    (requires (ok (+) i 1ul /\ ok (+) j 1ul /\ ok (+) i j /\ 1ul <^ (len v) -^ j /\ ok (Prims.op_Subtraction) (len v) i))
    (ensures (count x v = count x (swap v i j)))
  = Vector.Properties.lemma_swap_permutes_aux (as_raw v) i j x
  
type permutation 
     (#a:eqtype)
     (v1:vector a)
     (v2:vector a) 
  = (forall i. count i v1 = count i v2)

let lemma_swap_permutes
    (#a:eqtype)
    (v:vector a)
    (i:vector_index v)
    (j:vector_index v{i <=^ j})
  : Lemma
      (requires (ok (+) i 1ul /\ ok (+) j 1ul /\ ok (+) i j /\ 1ul <^ (len v) -^ j /\ 1ul <^ (len v) -^ i))
      (ensures (permutation v (swap v i j)))
  = FStar.Classical.forall_intro' #a #(fun x -> count x v = count x (swap v i j)) (lemma_swap_permutes_aux v i j)

let cons_perm
    (#a:eqtype)
    (tl:vector a)
    (v:vector a{len v >^ 0ul /\ len tl =^ len v -^ 1ul})
  : Lemma 
    (requires (permutation tl (tail v)))
    (ensures (permutation (cons (head v) tl) v))
  = let rtl:raw a (len v -^ 1ul) = as_raw tl in
    let rv:raw a (len v) =  as_raw v in
    Vector.Properties.cons_perm rtl rv

let lemma_mem_append
    (#a:eqtype)
    (v1:vector a)
    (v2:vector a{ok (+) (len v1) (len v2)})
  : Lemma 
    (ensures (forall (x:a). mem x (v1 @@ v2) <==> (mem x v1 || mem x v2)))
  = lemma_append_count v1 v2

let lemma_slice_cons
    (#a:eqtype)
    (v:vector a)
    (i:vector_index v)
    (j:vector_index v{i <^ j})
  : Lemma (ensures (forall x. mem x (subv v i j) <==> (x = v.(i) || mem x (subv v (i +^ 1ul) j))))
  = Vector.Properties.lemma_sub_cons (as_raw v) i j

let lemma_slice_snoc
    (#a:eqtype)
    (v:vector a)
    (i:vector_index v)
    (j:vector_index v{i <^ j})
  : Lemma 
    (ensures (forall x. mem x (subv v i j) <==> (x = v.(j -^ 1ul) || mem x (subv v i (j -^ 1ul)))))
  = Vector.Properties.lemma_sub_snoc (as_raw v) i j
  
let lemma_ordering_lo_snoc
    (#a:eqtype)
    (f:tot_ord a)
    (v:vector a)
    (i:vector_index v)
    (j:vector_index v{i <=^ j})
    (pv:a)
   : Lemma 
     (requires ((forall y. mem y (subv v i j) ==> f y pv) /\ f v.(j) pv))
     (ensures ((forall y. mem y (subv v i (j +^ 1ul)) ==> f y pv)))
  = Vector.Properties.lemma_ordering_lo_snoc f (as_raw v) i j pv

let lemma_ordering_hi_cons
    (#a:eqtype)
    (f:tot_ord a)
    (v:vector a)
    (back:vector_index v)
    (l:vector_index v{back <^ l})
    (pv:a)
  : Lemma 
    (requires ((forall y. mem y (subv v (back +^ 1ul) l) ==> f pv y) /\ f pv v.(back)))
    (ensures ((forall y. mem y (subv v back l) ==> f pv y)))
  = Vector.Properties.lemma_ordering_hi_cons f (as_raw v) back l pv

let swap_frame_lo
    (#a:Type)
    (v:vector a)
    (lo:vector_index v)
    (i:vector_index v{lo <=^ i})
    (j:vector_index v{i <=^ j})
  : Lemma 
    (ensures (subv v lo i == subv (swap v i j) lo i))
  = assert (equal (subv v lo i) (subv (swap v i j) lo i))

let swap_frame_lo' 
    (#a:Type)
    (v:vector a)
    (lo:vector_index v)
    (i':vector_index v{lo <=^ i'})
    (i:vector_index v{i' <=^ i})
    (j:vector_index v{i <=^ j})
  : Lemma 
    (ensures (subv v lo i' == subv (swap v i j) lo i'))
  = assert (equal (subv v lo i') (subv (swap v i j) lo i'))

let swap_frame_hi
    (#a:Type)
    (v:vector a)
    (i:vector_index v)
    (j:vector_index v{i <=^ j})
    (k:vector_index v{j <^ k})
    (hi:vector_index v{k <=^ hi})
  : Lemma 
    (ensures (subv v k hi == subv (swap v i j) k hi))
  = assert (equal (subv v k hi) (subv (swap v i j) k hi))

let lemma_swap_slice_commute
    (#a:Type)
    (v:vector a)
    (start:vector_index v)
    (i:vector_index v{start <=^ i})
    (j:vector_index v{i <=^ j})
    (l:len_t{j <^ l /\ l <=^ (len v)})
  : Lemma 
    (ensures (subv (swap v i j) start l == (swap (subv v start l) (i -^ start) (j -^ start))))
  = assert (equal (subv (swap v i j) start l) (swap (subv v start l) (i -^ start) (j -^ start)))

let lemma_swap_permutes_slice 
    (#a:eqtype)
    (v:vector a)
    (start:vector_index v)
    (i:vector_index v{start <=^ i})
    (j:vector_index v{i <=^ j})
    (l:len_t{j <^ l /\ l <=^ (len v)})
  : Lemma 
    (requires (ok (+) i 1ul /\ ok (+) j 1ul /\ ok (+) i j /\ ok (Prims.op_Subtraction) start j /\ 0ul <^ start -^ i))
    (ensures (permutation (subv v start l) (subv (swap v i j) start l)))
  = lemma_swap_slice_commute v start i j l;
    lemma_swap_permutes (subv v start l) (i -^ start) (j -^ start)

(* replaces the [i,j) sub-vector of v1 with the corresponding sub-vector of v2 *)
let splice
    (#a:Type)
    (v1:vector a)
    (i:vector_index v1)
    (v2:vector a)
    (j:len_t{i <=^ j /\ j <=^ len v1 /\ len v1 =^ len v2})
  : Tot (vector a)
  = (subv v1 0ul i) @@ ((subv v2 i j) @@ (subv v1 j (len v1)))

let splice_refl 
    (#a:Type)
    (v:vector a)
    (i:vector_index v)
    (j:len_t{i <=^ j /\ j <=^ len v})
  : Lemma
    (ensures (v == splice v i v j))
  = Vector.Properties.splice_refl (as_raw v) i j

let lemma_swap_splice
    (#a:Type)
    (v:vector a)
    (start:vector_index v)
    (i:vector_index v{start <=^ i})
    (j:vector_index v{i <=^ j})
    (l:len_t{j <^ l /\ l <=^ len v})
   : Lemma
     (ensures (swap v i j == splice v start (swap v i j) l))
   = Vector.Properties.lemma_swap_splice (as_raw v) start i j l

let lemma_vector_frame_hi
    (#a:Type)
    (v1:vector a)
    (v2:vector a{len v1 =^ len v2})
    (i:vector_index v2)
    (j:vector_index v1{i <=^ j})
    (m:vector_index v1{j <=^ m})
    (n:len_t{m <^ n /\ n <=^ len v1})
  : Lemma
    (requires (v1 == (splice v2 i v1 j)))
    (ensures  ((subv v1 m n == subv v2 m n) /\ (v1.(m) == v2.(reinx m v2))))
  = let l = len v1 in
    let (rv1:raw a l) = as_raw v1 in
    let (rv2:raw a l) = as_raw v2 in
    Vector.Properties.lemma_vector_frame_hi rv1 rv2 i j m n

let lemma_vector_frame_lo
    (#a:Type)
    (v1:vector a)
    (v2:vector a{len v1 =^ len v2})
    (i:vector_index v1)
    (j:vector_index v1{i <=^ j})
    (m:vector_index v2{j <^ m})
    (n:len_t{m <=^ n /\ n <=^ len v1})
  : Lemma
    (requires (v1 == (splice v2 m v1 n)))
    (ensures  ((subv v1 i j == subv v2 i j) /\ (v1.(j) == v2.(reinx j v2))))
  = let l = len v1 in
    let (rv1:raw a l) = as_raw v1 in
    let (rv2:raw a l) = as_raw v2 in
    Vector.Properties.lemma_vector_frame_lo rv1 rv2 i j m n

let lemma_tail_slice
    (#a:Type)
    (v:vector a)
    (i:vector_index v)
    (j:len_t{i <^ j /\ j <=^ (len v) /\ ok (+) i 1ul})
  : Lemma
    (requires True)
    (ensures (let tl = tail (subv v i j) in
              let sv = subv v (i +^ 1ul) j in
              tl == coerce sv (j -^ i -^ 1ul)))
    [SMTPat (tail (subv v i j))]
  = assert ((tail (subv v i j)) == (coerce (subv v (i +^ 1ul) j) (j -^ i -^ 1ul)))

let lemma_weaken_frame_right 
    (#a:Type)
    (v1:vector a)
    (v2:vector a{len v1 =^ len v2}) 
    (i:vector_index v2)
    (j:vector_index v1)
    (k:len_t{i <=^ j /\ j <=^ k /\ k <=^ len v1})
  : Lemma
    (requires (v1 == splice v2 i v1 j))
    (ensures (v1 == splice v2 i v1 k))
  = let l = len v1 in
    let (rv1:raw a l) = as_raw v1 in
    let (rv2:raw a l) = as_raw v2 in 
    Vector.Properties.lemma_weaken_frame_right rv1 rv2 i j k

let lemma_weaken_frame_left
    (#a:Type)
    (v1:vector a)
    (v2:vector a{len v1 =^ len v2})
    (i:vector_index v2)
    (j:vector_index v2) 
    (k:len_t{i <=^ j /\ j <=^ k /\ k <=^ len v1})
  : Lemma
    (requires (v1 == splice v2 j v1 k))
    (ensures (v1 == splice v2 i v1 k))
  = let l = len v1 in
    let (rv1:raw a l) = as_raw v1 in
    let (rv2:raw a l) = as_raw v2 in 
    Vector.Properties.lemma_weaken_frame_left rv1 rv2 i j k


let lemma_trans_frame
    (#a:Type)
    (v1:vector a)
    (v2:vector a)
    (v3:vector a{len v1 =^ len v2 /\ len v2 =^ len v3})
    (i:vector_index v3)
    (j:len_t{i <=^ j && j <=^ len v1})
  : Lemma
    (requires ((v1 == splice v2 (reinx i v2) v1 j) /\ v2 == splice v3 i v2 j))
    (ensures (v1 == splice v3 i v1 j))
  = let l = len v1 in
    let (rv1:raw a l) = as_raw v1 in
    let (rv2:raw a l) = as_raw v2 in 
    let (rv3:raw a l) = as_raw v3 in 
    Vector.Properties.lemma_trans_frame rv1 rv2 rv3 i j

#reset-options "--z3rlimit 20"
let lemma_weaken_perm_left
    (#a:eqtype)
    (v1:vector a)
    (v2:vector a{len v1 =^ len v2})
    (i:vector_index v1)
    (j:vector_index v2)
    (k:len_t{i <=^ j /\ j <=^ k /\ k <=^ len v1})
  : Lemma
    (requires (v1 == splice v2 j v1 k /\ permutation (subv v2 j k) (subv v1 j k)))
    (ensures (permutation (subv v2 i k) (subv v1 i k)))
  = let l = len v1 in
    let (rv1:raw a l) = as_raw v1 in
    let (rv2:raw a l) = as_raw v2 in 
    Vector.Properties.lemma_weaken_perm_left rv1 rv2 i j k

let lemma_weaken_perm_right
    (#a:eqtype)
    (v1:vector a)
    (v2:vector a{len v1 =^ len v2})
    (i:vector_index v1)
    (j:vector_index v2)
    (k:len_t{i <=^ j /\ j <=^ k /\ k <=^ len v1})
  : Lemma
    (requires (let iq:len_t = i in
               v1 == splice v2 iq v1 j /\ 
               permutation (subv v2 iq j) (subv v1 iq j)))
    (ensures (permutation (subv v2 i k) (subv v1 i k)))
  = let l = len v1 in
    let (rv1:raw a l) = as_raw v1 in
    let (rv2:raw a l) = as_raw v2 in 
    Vector.Properties.lemma_weaken_perm_right rv1 rv2 i j k
#reset-options

let lemma_trans_perm
    (#a:eqtype)
    (v1:vector a)
    (v2:vector a)
    (v3:vector a{len v1 =^ len v2 /\ len v2 =^ len v3})
    (i:vector_index v1)
    (j:len_t{i <=^ j && j <=^ len v1})
  : Lemma
    (requires (permutation (subv v1 i j) (subv v2 i j)
              /\ permutation (subv v2 i j) (subv v3 i j)))
    (ensures (permutation (subv v1 i j) (subv v3 i j)))
  = ()

let snoc
    (#a:Type)
    (v:vector a{ok (+) (len v) 1ul}) 
    (x:a)
  : Tot (r:vector a{len r =^ (len v) +^ 1ul})
  = v @@ (create1 x)

let lemma_cons_snoc 
    (#a:Type) 
    (hd:a) 
    (v:vector a{ok (+) (len v) 1ul /\ ok (+) (len v) 2ul}) 
    (tl:a)
  : Lemma 
    (requires True)
    (ensures (let q = snoc v tl in
              let r = cons hd q in
              let s = cons hd v in
              let t = snoc s tl in
             (r == t)))
  = Vector.Properties.lemma_cons_snoc hd (as_raw v) tl

let lemma_tail_snoc
    (#a:Type)
    (v:vector a{(len v) >^ 1ul /\ ok (+) (len v) 1ul})
    (x:a)
  : Lemma 
    (ensures (let r = coerce (tail (snoc v x)) (len v) in
              let s = coerce (snoc (tail v) x) (len v) in
              r == s))
  = let x1 = create1 x in
    lemma_slice_first_in_append v x1 1ul

let lemma_snoc_inj
    (#a:Type)
    (v1:vector a)
    (v2:vector a{len v1 =^ len v2 /\ ok (+) (len v1) 1ul})
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
    (v:vector a{ok (+) (len v) 1ul}) 
    (x:a)
  : Lemma (ensures (forall y. mem y (snoc v x) <==> mem y v \/ x=y))
  = lemma_append_count v (create1 x)

let find_l
    (#a:Type)
    (f:a -> Tot bool)
    (v:vector a)
  : Tot (o:option a{Some? o ==> f (Some?.v o)})
  = Vector.Properties.find_l f (as_raw v)
    
let find_append_some
    (#a:Type)
    (v1:vector a)
    (v2:vector a{ok (+) (len v1) (len v2)})
    (f:a -> Tot bool)
  : Lemma
    (requires (Some? (find_l f v1)))
    (ensures (find_l f (v1 @@ v2) == find_l f v1))
    = Vector.Properties.find_append_some (as_raw v1) (as_raw v2) f
  
let find_append_none
    (#a:Type)
    (v1:vector a)
    (v2:vector a{ok (+) (len v1) (len v2)})
    (f:a -> Tot bool)
  : Lemma
    (requires (None? (find_l f v1)))
    (ensures (find_l f (v1 @@ v2) == find_l f v2))
  = Vector.Properties.find_append_none (as_raw v1) (as_raw v2) f

let find_append_none_v2
    (#a:Type)
    (v1:vector a)
    (v2:vector a{ok (+) (len v1) (len v2)})
    (f:a -> Tot bool)
  : Lemma
    (requires (None? (find_l f v2)))
    (ensures  (find_l f (v1 @@ v2) == find_l f v1))
  = Vector.Properties.find_append_none_v2 (as_raw v1) (as_raw v2) f
  
let find_snoc
    (#a:Type)
    (v:vector a{ok (+) (len v) 1ul})
    (x:a)
    (f:a -> Tot bool)
  : Lemma 
    (ensures (let res = find_l f (snoc v x) in
              match res with 
              | None -> find_l f v == None /\ not (f x)
              | Some y -> res == find_l f v \/ (f x /\ x==y)))
  = if Some? (find_l f v) then find_append_some v (create1 x) f
    else find_append_none v (create1 x) f

let un_snoc 
    (#a:Type) 
    (v:vector a{len v >^ 0ul}) 
  : Tot (r:(vector a * a){(len (fst r) =^ len v -^ 1ul) /\ (equal v (snoc (fst r) (snd r)))})
  = let r, s = Vector.Properties.un_snoc (as_raw v) in
    (from_raw r, s)

let un_snoc_snoc 
    (#a:Type)
    (v:vector a{ok (+) (len v) 1ul})
    (x:a)
  : Lemma 
    (requires True)
    (ensures (un_snoc (snoc v x) == (v, x)))
  = Vector.Properties.un_snoc_snoc (as_raw v) x

let find_r
    (#a:Type)
    (f:a -> Tot bool)
    (v:vector a{ok (+) (len v) 1ul})
  : Tot (o:option a{Some? o ==> f (Some?.v o)})
  = Vector.Properties.find_r f (as_raw v)

let vector_find_aux
    (#a:Type)
    (f:a -> Tot bool)
    (v:vector a)
    (ctr:len_t{ctr <=^ len v})
  : Pure (option a)
    (requires (forall (i:vector_index v{i >=^ ctr}). not (f v.(i))))
    (ensures (function 
              | None -> forall (i:vector_index v). not (f v.(i))
              | Some x -> f x /\  
                (exists (i:vector_index v). {:pattern (found i)} found i /\ x == v.(i))))
  = Vector.Properties.raw_find_aux f (as_raw v) ctr

let vector_find
    (#a:Type)
    (f:a -> Tot bool)
    (v:vector a)
  : Pure (option a)
    (requires True)
    (ensures (function
              | None -> forall (i:vector_index v). not (f v.(i))
              | Some x -> f x /\ 
                (exists (i:vector_index v).{:pattern (found i)} found i /\ x == v.(i))))
  = vector_find_aux f v (len v)

let find_mem 
    (#a:eqtype)
    (v:vector a) 
    (f:a -> Tot bool) 
    (x:a{f x})
  : Lemma 
    (requires (mem x v))
    (ensures (Some? (vector_find f v) /\ f (Some?.v (vector_find f v))))
  = match vector_find f v with
    | None -> mem_index x v
    | Some _ -> ()

let for_all
    (#a: Type)
    (f:a -> Tot bool)
    (v:vector a)
  : Pure bool
    (requires True)
    (ensures (fun b -> (b == true <==> (forall (i:vector_index v) . f v.(i) == true))))
  = None? (vector_find (fun i -> not (f i)) v)

let vector_mem_k
    (#a:eqtype)
    (v:vector a)
    (n:vector_index v)
  : Lemma 
    (requires True)
    (ensures (mem v.(n) v))
    [SMTPat (mem v.(n) v)]
  = Vector.Properties.raw_mem_k (as_raw v) n

let vector_to_list
    (#a:Type)
    (v:vector a)
  : Tot (r:list a{L.length r = u32_to_int (len v)}) 
  = Vector.Properties.raw_to_list (as_raw v)

let vector_of_list
    (#a:Type)
    (l:list a{is_u32 (L.length l)})
  : Tot (r:vector a{len r =^ int_to_u32 (L.length l)})
  = from_raw (Vector.Properties.raw_of_list l)

let lemma_vector_list_bij
    (#a:Type)
    (v:vector a)
  : Lemma
    (requires (True))
    (ensures  (vector_of_list (vector_to_list v) == v))
  = Vector.Properties.lemma_raw_list_bij (as_raw v)
  
let lemma_list_vector_bij
    (#a:Type)
    (l:list a{is_u32 (L.length l)})
  : Lemma
    (requires (True))
    (ensures  (vector_to_list (vector_of_list l) == l))
  = Vector.Properties.lemma_list_raw_bij l

unfold 
let createL_post 
    (#a:Type0)
    (l:list a{is_u32 (L.length l)}) 
    (v:vector a{len v =^ int_to_u32 (L.length l)})
  : GTot Type0 
  = normalize (L.length l = (u32_to_int (len v))) /\ vector_to_list v == l /\ vector_of_list l == v

let createL
    (#a:Type0)
    (l:list a{is_u32 (L.length l)})
  : Pure (r:vector a{len r =^ int_to_u32 (L.length l)})
    (requires True)
    (ensures (fun s -> createL_post #a l s))
  = let s = vector_of_list l in
    lemma_list_vector_bij l;
    s

let lemma_index_is_nth
    (#a:Type)
    (v:vector a)
    (i:vector_index v)
  : Lemma
    (requires True)
    (ensures (L.index (vector_to_list v) (u32_to_int i) == v.(i)))
  = Vector.Properties.lemma_index_is_nth (as_raw v) i

////////////////////////////////////////////////////////////////////////////////
//s `contains` x : Type0
//    An undecidable version of `mem`, 
//    for when the vector payload is not an eqtype
  ////////////////////////////////////////////////////////////////////////////////
abstract 
let contains
    (#a:Type)
    (v:vector a) 
    (x:a) 
  : Tot Type0 
  = if len v =^ 0ul then false
    else (exists (k:vector_index v). v.(k) == x)
    
let contains_intro 
    (#a:Type)
    (v:vector a) 
    (k:vector_index v) 
    (x:a)
  : Lemma 
    (v.(k) == x ==> v `contains` x)
  = ()

let contains_elim 
    (#a:Type)
    (v:vector a) 
    (x:a)
  : Lemma (v `contains` x ==> (exists (k:vector_index v). v.(k) == x))
  = ()

let lemma_contains_empty 
    (#a:Type)
  : Lemma (forall (x:a). ~ (contains empty x)) 
  = ()

let lemma_contains_create1 
    (#a:Type) 
    (x:a) 
  : Lemma (forall (y:a). contains (create1 x) y ==> y == x) 
  = ()

#reset-options "--z3rlimit 20"
private
let intro_append_contains_from_disjunction 
    (#a:Type)
    (v1:vector a)
    (v2:vector a{ok (+) (len v1) (len v2)})
    (x:a) 
  : Lemma 
    (requires (v1 `contains` x \/ v2 `contains` x))
    (ensures (v1 @@ v2) `contains` x)
  = contains_elim v1 x;
    contains_elim v2 x;
    let v1v2 = v1 @@ v2 in
    assert ((exists i. (v1.(i) == x /\ v1v2.(reinx i v1v2) == x)) \/
            (exists j. (v2.(j) == x /\ v1v2.(reinx (j +^ len v1) v1v2) == x)))

#reset-options "--z3rlimit 20"
let append_contains_equiv 
    (#a:Type)
    (v1:vector a)
    (v2:vector a{ok (+) (len v1) (len v2)}) 
    (x:a)
  : Lemma ((v1 @@ v2) `contains` x
           <==>
           (v1 `contains` x \/ v2 `contains` x))
  = contains_elim (v1 @@ v2) x;
    let v1v2 = v1 @@ v2 in
    assert (v1v2 `contains` x ==>
            ((exists i. (v1.(i) == x /\ v1v2.(reinx i v1v2) == x)) \/
             (exists j. (v2.(j) == x /\ v1v2.(reinx (j +^ len v1) v1v2) == x))))
#reset-options

let snoc_v_x_contains_x
    (#a:Type)
    (v:vector a{ok (+) (len v) 1ul})
    (x:a)
  : Lemma ((snoc v x) `contains` x)
  = assert((snoc v x) == v @@ (create1 x)); 
    append_contains_equiv v (create1 x) x;
    assert (last (snoc v x) == x)

let snoc_v_x_contains_y
    (#a:Type)
    (v:vector a{ok (+) (len v) 1ul})
    (x:a)
    (y:a)
  : Lemma 
    (requires (x == y))
    (ensures ((snoc v x) `contains` y))
  = snoc_v_x_contains_x v x
  
let v_contains_x_snoc_y_contains_x
    (#a:Type)
    (v:vector a{ok (+) (len v) 1ul})
    (x:a)
    (y:a)
  : Lemma 
    (requires (v `contains` x))
    (ensures ((snoc v y) `contains` x))
  = append_contains_equiv v (create1 y) x
  
let contains_snoc_r_l_aux
    (#a:Type)
    (v:vector a{ok (+) (len v) 1ul})
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
    (v:vector a{ok (+) (len v) 1ul})
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
    (v:vector a{ok (+) (len v) 1ul})
    (x:a)
  : Lemma 
    (requires True)
    (ensures (forall y. v `contains` y \/ x==y ==> (snoc v x) `contains` y))
  = Classical.forall_intro (contains_snoc_r_l_aux2 v x)
  
#reset-options "--z3rlimit 20"
let contains_snoc_l_r
    (#a:Type)
    (v:vector a{ok (+) (len v) 1ul})
    (x:a)
  : Lemma 
    (ensures (forall y. (snoc v x) `contains` y ==> v `contains` y \/ x==y))
  = FStar.Classical.forall_intro (append_contains_equiv v (create1 x))
#reset-options 

let contains_snoc 
    (#a:Type)
    (v:vector a{ok (+) (len v) 1ul})
    (x:a)
  : Lemma 
    (ensures (forall y. (snoc v x) `contains` y <==> v `contains` y \/ x==y))
  = contains_snoc_r_l v x;
    contains_snoc_l_r v x

let lemma_find_l_exists_index
    (#a:Type) 
    (f:a -> Tot bool)
    (v:vector a)
  : Lemma 
    (requires (Some? (find_l f v)))
    (ensures (exists i. f v.(i)))
  = Vector.Properties.lemma_find_l_exists_index f (as_raw v)
  
let lemma_find_l_contains 
    (#a:Type) 
    (f:a -> Tot bool)
    (v:vector a)
  : Lemma 
    (requires (Some? (find_l f v)))
    (ensures (v `contains` (Some?.v (find_l f v))))
  = Vector.Properties.lemma_find_l_contains f (as_raw v)
  
let contains_cons 
    (#a:Type)
    (hd:a) 
    (tl:vector a{ok (+) (len tl) 1ul}) 
    (x:a)
  : Lemma ((cons hd tl) `contains` x
          ==>
          (x==hd \/ tl `contains` x))
  = append_contains_equiv (create1 hd) tl x

let append_cons_snoc
    (#a:Type) 
    (v1:vector a)
    (x:a)
    (v2:vector a{ok (+) (len v1) 1ul /\ ok (+) (len v2) 1ul /\ ok (+) 1ul (len v2) /\ ok (+) (len v2 +^ 1ul) (len v1) /\ ok (+) (len v1) (len v2)})
   : Lemma (let q = v1 @@ (cons x v2) in
            let r = coerce ((snoc v1 x) @@ v2) (len v1 +^ (1ul +^ len v2)) in
            q == r)
   = Vector.Properties.append_cons_snoc (as_raw v1) x (as_raw v2)
    
let append_slices 
    (#a:Type)
    (v1:vector a)
    (v2:vector a{ok (+) (len v1) (len v2)})
   : Lemma (v1 == (subv (v1 @@ v2) 0ul (len v1)) /\
            v2 == (subv (v1 @@ v2) (len v1) ((len v1) +^ (len v2))) /\
            (forall (i:len_t) (j:len_t). (
              i <=^ j /\ j <=^ len v2 
              ==> (let (q:vector a{len q =^ j -^ i}) = subv v2 i j in
                   let (r:vector a{len r =^ (len v1 +^ j) -^ (len v1 +^ i)}) = (subv (v1 @@ v2) (len v1 +^ i) (len v1 +^ j)) in
                   equal q r))))
   = Vector.Properties.append_subs (as_raw v1) (as_raw v2)

// cwinter: TODO
// let rec find_l_none_no_index 
//     (#a:Type)
//     (v:vector a{ok (+) (len v) 1ul})
//     (f:a -> Tot bool)
//   : Lemma 
//     (requires (None? (find_l f v)))
//     (ensures (forall (i:vector_index v). not (f v.(i))))
//     (decreases (length v))
//   = if len v =^ 0ul then ()
//     else let ls1 = len v -^ 1ul in
//          let m : (m:len_t{m >^ 0ul}) = len v in
//          let u = coerce v m in
//          let (hd:a{not (f hd)}) = head u in
//          let tl = tail u in
//          let hd1 = create1 #a hd in
//          assert (not (f hd) /\ hd1.(0ul) == hd /\ not (f hd1.(0ul)));
//          assert (None? (find_l f tl));
//          assert (None? (find_l f hd1)); // <-- find_append_none wants this.
//          find_l_none_no_index tl f;
//          assert (equal u (hd1 @@ tl));
//        	find_append_none hd1 tl f
// #reset-options

let suffix_of
    (#a:Type)
    (suffix:vector a)
    (v:vector a)
  : Tot Type0
  = if len suffix >^ len v then False
    else 
      let prelen = len v -^ len suffix in
      (exists (prefix:vector a{len prefix =^ prelen}). (v == prefix @@ suffix))

// MOVE TO BASE FROM HERE?

let rec lemma_index_create
    (#a:Type) 
    (n:len_t)
    (x:a)
    (i:len_t{i <^ n})
  : Lemma
    (requires True)
    (ensures ((createN #a n (fun _ -> x)).(i) == x))
    (decreases (u32_to_int n))
    [SMTPat ((createN #a n (fun _ -> x)).(i))]
  = if n =^ 0ul then ()
    else
      if i =^ 0ul then () 
      else lemma_index_create (n -^ 1ul) x (i -^ 1ul)

let lemma_index_upd1
    (#a:Type)
    (v:vector a)
    (n:len_t{n <^ len v})
    (x:a)
  : Lemma
    (requires True)
    (ensures ((v.(n) <- x).(n) == x)) 
    [SMTPat ((v.(n) <- x).(n))]
  = Vector.Properties.lemma_index_upd1 (as_raw v) n x

let lemma_index_upd2
    (#a:Type)
    (v:vector a)
    (n:len_t{n <^ len v})
    (x:a)
    (i:len_t{i <^ len v /\ i <> n})
  : Lemma
    (requires True)
    (ensures ((v.(n) <- x).(i) == v.(i))) 
    [SMTPat ((v.(n) <- x).(i))]
  = Vector.Properties.lemma_index_upd2 (as_raw v) n x i

abstract 
let lemma_index_app1
    (#a:Type) 
    (v1:vector a)
    (v2:vector a)
    (i:len_t{i <^ len v1 /\ ok (+) (len v1) (len v2)})
  : Lemma
    (requires True)
    (ensures ((v1 @@ v2).(i) == v1.(i))) 
    [SMTPat ((v1 @@ v2).(i))]
  = Vector.Properties.lemma_index_app1 (as_raw v1) (as_raw v2) i

abstract 
let lemma_index_app2
    (#a:Type)
    (v1:vector a)
    (v2:vector a)
    (i:vector_index v1{ok (+) (len v1) (len v2) /\ i <^ ((len v1) +^ (len v2)) /\ len v1 <=^ i})
  : Lemma
    (requires True)
    (ensures ((v1 @@ v2).(i) == v2.(i -^ len v1)))
    [SMTPat ((v1 @@ v2).(i))]
  = Vector.Properties.lemma_index_app2 (as_raw v1) (as_raw v2) i

abstract
let lemma_index_slice
    (#a:Type)
    (v:vector a)
    (i:vector_index v)
    (j:vector_index v{i <=^ j})
    (k:len_t{k <^ j -^ i})
  : Lemma
    (requires True)
    (ensures ((subv v i j).(k) == v.(k +^ i))) 
    [SMTPat ((subv v i j).(k))]
  = Vector.Properties.lemma_index_sub (as_raw v) i j k
 
abstract 
let lemma_eq_elim
    (#a:Type)
    (v1:vector a)
    (v2:vector a)
  : Lemma
     (requires (len v1 =^ len v2 /\ v1 == v2) \/ (v1 == v2))
     (ensures (v1 == v2))
     [SMTPat (equal v1 v2); SMTPat (v1 == v2)]
  = Vector.Properties.lemma_eq_elim (as_raw v1) (as_raw v2)

// MOVE TO BASE UP TO HERE?


let cons_head_tail
    (#a:Type)
    (v:vector a{len v >^ 0ul})
  : Lemma
    (requires True)
    (ensures (v == cons (head v) (tail v)))
    [SMTPat (cons (head v) (tail v))]
  = lemma_t_eq_intro v (cons (head v) (tail v))

let head_cons
    (#a:Type)
    (x:a)
    (v:vector a{ok (+) (len v) 1ul})
  : Lemma
    (ensures (head (cons x v) == x))
  = ()

let suffix_of_tail
    (#a:Type)
    (v:vector a{len v >^ 0ul})
  : Lemma
    (requires True)
    (ensures ((tail v) `suffix_of` v))
    [SMTPat ((tail v) `suffix_of` v)]
  = cons_head_tail v;
    let hd = head v in
    let tl = tail v in
    assert (v == (cons hd tl));
    assert (len tl =^ len v -^ 1ul);
    assert ((exists (p:vector a{len p =^ 1ul}). (v == p @@ tl)));
    Classical.exists_intro (fun (p:vector a{len p =^ 1ul}) -> v == p @@ tl) (create1 hd)

 let index_cons_l
    (#a:Type)
    (c:a)
    (v:vector a{len v >^ 0ul /\ ok (+) (len v) 1ul})
  : Lemma
    (ensures ((cons c v).(0ul) == c))
  = ()

let index_cons_r
    (#a:Type)
    (c:a)
    (v:vector a)
    (i:len_t{1ul <=^ i /\ i <=^ len v /\ ok (+) (len v) 1ul})
  : Lemma
    (ensures ((cons c v).(i) == v.(i -^ 1ul)))
  = ()

let append_cons
    (#a:Type)
    (c:a)
    (v1:vector a)
    (v2:vector a{ok (+) (len v1) (len v2) /\ ok (+) ((len v1) +^ (len v2)) 1ul})
  : Lemma
    (ensures (let v1v2 = v1 @@ v2 in
              let lv1v2 = (len v1) +^ (len v2) +^ 1ul in
              let appcons = coerce ((cons c v1) @@ v2) lv1v2 in
              let consapp = coerce (cons c v1v2) lv1v2 in
              appcons == consapp))
  = Vector.Properties.append_cons c (as_raw v1) (as_raw v2)

let vector_indexail
    (#a:Type)
    (v:vector a{len v >^ 0ul})
    (i:len_t{i <^ (len v) -^ 1ul})
  : Lemma
    (ensures ((tail v).(i) == v.(i +^ 1ul)))
  = ()

let mem_cons
    (#a:eqtype)
    (x:a)
    (v:vector a{ok (+) (len v) 1ul})
  : Lemma
    (ensures (forall y. mem y (cons x v) <==> mem y v \/ x=y))
  = lemma_append_count (create1 x) v

let snoc_slice_index
    (#a:Type)
    (v:vector a)
    (i:vector_index v)
    (j:vector_index v{i <=^ j})
  : Lemma
    (requires True)
    (ensures (snoc (subv v i j) v.(j) == coerce (subv v i (j +^ 1ul)) (j -^ i +^ 1ul)))
    [SMTPat (snoc (subv v i j) v.(j))]
  = Vector.Properties.snoc_sub_index (as_raw v) i j

let cons_index_slice
    (#a:Type)
    (v:vector a)
    (i:len_t)
    (j:len_t{i <^ j /\ j <=^ len v} )
  : Lemma
    (requires True)
    (ensures (cons v.(i) (subv v (i +^ 1ul) j) == coerce (subv v i j) (1ul +^ (j -^ (i +^ 1ul))) ))
    [SMTPat (cons v.(i) (subv v (i +^ 1ul) j))]
  = Vector.Properties.cons_index_sub (as_raw v) i j

let sub_is_empty
    (#a:Type)
    (v:vector a)
    (i:len_t{i <=^ len v})
  : Lemma
    (requires (True))
    (ensures (coerce (subv v i i) 0ul == empty))
    [SMTPat (subv v i i)]
  = Vector.Properties.sub_is_empty (as_raw v) i

let sub_length
    (#a:Type)
    (v:vector a)
  : Lemma
    (requires True)
    (ensures (subv v 0ul (len v) == v))
    [SMTPat (subv v 0ul (len v))]
  = lemma_eq_elim (subv v 0ul (len v)) v

let sub_slice
    (#a:Type)
    (v:vector a)
    (i1:len_t)
    (j1:len_t{i1 <=^ j1 /\ j1 <=^ len v} )
    (i2:len_t)
    (j2:len_t{i2 <=^ j2 /\ j2 <=^ j1 -^ i1})
  : Lemma
    (requires (ok (+) i1 i2 /\ ok (+) i1 j2)) 
    (ensures (subv (subv v i1 j1) i2 j2 == coerce (subv v (i1 +^ i2) (i1 +^ j2)) (j2 -^ i2)))
    [SMTPat (subv (subv v i1 j1) i2 j2)]
  = lemma_eq_elim (subv (subv v i1 j1) i2 j2) (subv v (i1 +^ i2) (i1 +^ j2))

#reset-options "--z3rlimit 30"
let vector_of_list_tl
    (#a: Type)
    (l:list a{is_u32 (L.length l) /\ L.length l > 0})
: Lemma
  (requires True)
  (ensures (vector_of_list (L.tl l) == tail (vector_of_list l)))
  [SMTPat (vector_of_list (L.tl l))]
= Vector.Properties.raw_of_list_tl l

#reset-options "--z3rlimit 30"
let mem_vector_of_list
    (#a:eqtype)
    (x:a)
    (l:list a{is_u32 (L.length l)})
  : Lemma
    (requires True)
    (ensures (mem x (vector_of_list l) == L.mem x l))
    (decreases (L.length l))
    [SMTPat (mem x (vector_of_list l))]
  = Vector.Properties.mem_raw_of_list x l
