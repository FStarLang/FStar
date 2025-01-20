(*
   Copyright 2008-2018 Microsoft Research

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
module LowStar.BufferView.Down
open LowStar.Monotonic.Buffer
open FStar.Mul
module HS=FStar.HyperStack
module B=LowStar.Monotonic.Buffer
module Math=FStar.Math.Lemmas

#set-options "--smtencoding.elim_box true"
#set-options "--smtencoding.l_arith_repr native"
#set-options "--smtencoding.nl_arith_repr wrapped"
#set-options "--z3rlimit_factor 4" //just being conservative
#set-options "--initial_fuel 1 --max_fuel 1"

noeq
type buffer_view (src:Type0) (rrel rel:B.srel src) (dest:Type u#b) : Type u#b =
  | BufferView: buf:B.mbuffer src rrel rel
              -> v:view src dest
              -> buffer_view src rrel rel dest

let mk_buffer_view (#src:Type0) (#rrel #rel:B.srel src) (#dest:Type)
                   (b:B.mbuffer src rrel rel)
                   (v:view src dest)
   : GTot (buffer dest)
   = (| src, rrel, rel, BufferView b v |)

let as_buffer (#b:Type) (v:buffer b) =
  let (| _, _, _, BufferView b _ |) = v in
  b

let as_buffer_mk_buffer_view
       (#src:Type0) (#rrel #rel:B.srel src) (#dest:Type)
       (b:B.mbuffer src rrel rel)
       (v:view src dest) =
   ()

let get_view  (#b : Type) (bv:buffer b) =
  let (| _, _, _, BufferView _ v |) = bv in
  v

let get_view_mk_buffer_view
       (#src:Type0) (#rrel #rel:B.srel src) (#dest:Type)
       (b:B.mbuffer src rrel rel)
       (v:view src dest)
  = ()

let length (#b: _) (vb:buffer b) =
  let b = as_buffer vb in
  let v = get_view vb in
  B.length b * View?.n v

let length_eq (#b: _) (vb:buffer b) = ()

let indexing' (#a #b: _) (v:view a b) (len_as:nat) (i:nat{i < len_as * View?.n v})
  : Lemma (let n = View?.n v in
           let vlen = len_as * n in
           n * (i / n) < vlen  /\
           n * (i / n) + n <= vlen)
  = let n = View?.n v in
    let vlen = len_as * n in
    assert (n * (i / n) < vlen);
    assert (i / n <= len_as - 1)

let indexing #b vb i = indexing' (get_view vb) (B.length (as_buffer vb)) i

let sel' (#a #b: _) (v:view a b)
         (es:Seq.seq a)
         (i:nat{i / View?.n v < Seq.length es})
   : GTot b
   = let n = View?.n v in
     let a_i = i / n in
     let bs = View?.get v (Seq.index es a_i) in
     Seq.index bs (i % n)

let sel (#b: _)
        (h:HS.mem)
        (vb:buffer b)
        (i:nat{i < length vb})
   : GTot b
   = indexing vb i;
     let es = B.as_seq h (as_buffer vb) in
     let v = get_view vb in
     sel' v es i

let lemma_g_upd_with_same_seq (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) (h:HS.mem{B.live h b}) (s:_)
  : Lemma (Seq.equal s (B.as_seq h b) ==>
           B.g_upd_seq b s h == h)
  = B.lemma_g_upd_with_same_seq b h

let mods (#b: _)
             (vb:buffer b)
             (h h':HS.mem)
    = B.modifies (B.loc_buffer (as_buffer vb)) h h'

val upd' (#b: _)
        (h:HS.mem)
        (vb:buffer b{live h vb})
        (i:nat{i < length vb})
        (x:b)
  : GTot (h':HS.mem{
           (indexing vb i;
            let b = as_buffer vb in
            let v = get_view vb in
            let n = View?.n v in
            let a_i = i / n in
            B.as_seq h' b ==
            Seq.upd (B.as_seq h b) a_i (Seq.index (B.as_seq h' b) a_i)) /\
            sel h' vb i == x /\
            (forall (j:nat{j< length vb}). i<>j ==> sel h' vb j == sel h vb j) /\
            (x == sel h vb i ==> h == h') /\
            mods vb h h' /\
            live h' vb /\
            FStar.HyperStack.ST.equal_domains h h'
          })
#push-options "--z3rlimit_factor 8"
let upd' #b h vb i x =
    indexing vb i;
    let es = B.as_seq h (as_buffer vb) in
    let v = get_view vb in
    let n = View?.n v in
    let a_i = i / n in
    let bs = View?.get v (Seq.index es a_i) in
    let bs' = Seq.upd bs (i % n) x in
    assert (x == sel h vb i ==> Seq.equal bs bs');
    let a' = View?.put v bs' in
    let mem = B.g_upd (as_buffer vb) a_i a' h in
    B.g_upd_seq_as_seq (as_buffer vb) (Seq.upd es a_i a') h;
    lemma_g_upd_with_same_seq (as_buffer vb) h (Seq.upd es a_i a');
    mem
#pop-options

let upd = upd'
let sel_upd #b vb i j x h = ()
let lemma_upd_with_sel #b vb i h = ()
let upd_modifies #b h vb i x = ()
let upd_equal_domains #b h vb i x = ()

let rec seq_fold_right_gtot #a #b (s:Seq.seq a) (f:a -> b -> GTot b) (acc:b)
  : GTot b (decreases (Seq.length s))
  = if Seq.length s = 0 then acc
    else f (Seq.head s) (seq_fold_right_gtot (Seq.tail s) f acc)

let cons_view #a #b (v:view a b) (x:a) (tl:Seq.seq b) : GTot (Seq.seq b) =
  Seq.append (View?.get v x) tl

let as_seq' (#a #b:_) (es:Seq.seq a) (v:view a b) : GTot (Seq.seq b) =
  seq_fold_right_gtot #a #(Seq.seq b) es (cons_view #a #b v) Seq.empty

let rec as_seq'_len (#a #b:_) (es:Seq.seq a) (v:view a b)
  : Lemma (ensures (Seq.length (as_seq' es v) == View?.n v * Seq.length es))
          (decreases (Seq.length es))
  = if Seq.length es = 0 then ()
    else as_seq'_len (Seq.tail es) v

let rec as_seq'_injective #a #b (v:view a b) (as1 as2:Seq.seq a)
  : Lemma
      (requires as_seq' as1 v `Seq.equal` as_seq' as2 v)
      (ensures  as1 `Seq.equal` as2)
      (decreases (Seq.length as1))
  = as_seq'_len as1 v;
    as_seq'_len as2 v;
    assert (Seq.length as1 == Seq.length as2);
    if Seq.length as1 = 0 then ()
    else let n = View?.n v in
         as_seq'_len (Seq.tail as1) v;
         as_seq'_len (Seq.tail as2) v;
         Seq.lemma_append_inj
               (View?.get v (Seq.head as1))
               (as_seq' (Seq.tail as1) v)
               (View?.get v (Seq.head as2))
               (as_seq' (Seq.tail as2) v);
         as_seq'_injective v (Seq.tail as1) (Seq.tail as2);
         assert (as1 `Seq.equal` (Seq.head as1 `Seq.cons` Seq.tail as1));
         assert (as2 `Seq.equal` (Seq.head as2 `Seq.cons` Seq.tail as2))

let as_seq #b h vb =
  let (| a, _, _, BufferView buf v |) = vb in
  let es = B.as_seq h buf in
  let bs = as_seq' #a #b es v in
  as_seq'_len es v;
  bs

#push-options "--max_ifuel 0"
val sel'_tail (#a #b:_) (v:view a b) (es:Seq.seq a{Seq.length es > 0})
              (i:nat{View?.n v <= i /\ i < Seq.length es * View?.n v})
  : Lemma (let j = i - View?.n v in
           sel' v es i == sel' v (Seq.tail es) j)
let sel'_tail #a #b v es i =
  let len_as = Seq.length es in
  indexing' v len_as i;
  let n = View?.n v in
  let j = i - n in
  let a_i = i / n in
  assert (sel' v es i == Seq.index (View?.get v (Seq.index es a_i)) (i % n));
  FStar.Math.Lemmas.lemma_mod_sub i n 1;
  FStar.Math.Lemmas.add_div_mod_1 j n;
  assert (j / n == (i / n) - 1)
#pop-options

val as_seq'_sel' (#a #b: _)
                 (v:view a b)
                 (es:Seq.seq a)
                 (i:nat{i < Seq.length es * View?.n v})
  : Lemma
     (ensures (
       as_seq'_len es v;
       sel' v es i == Seq.index (as_seq' es v) i))
     (decreases (Seq.length es))

let rec as_seq'_sel' #a #b v es i =
  as_seq'_len es v;
  let n : pos = View?.n v in
  assert (i / n < Seq.length es);
  if Seq.length es = 0 then ()
  else let bs = as_seq' es v in
       assert (Seq.length bs = n + Seq.length (as_seq' (Seq.tail es) v));
       if (i < n) then
         begin
           assert (Seq.index bs i == Seq.index (View?.get v (Seq.head es)) i)
         end
       else
         begin
           let as' = Seq.tail es in
           as_seq'_len as' v;
           let j = i - n in
           assert (j / n < Seq.length as');
           assert (j < Seq.length (as_seq' as' v));
           as_seq'_sel' v as' j;
           assert (sel' v as' j == Seq.index (as_seq' as' v) j);
           assert (Seq.index (as_seq' es v) i ==
                   Seq.index (as_seq' as' v) j);
           sel'_tail v es i
         end

let as_seq_sel #b h vb i =
  indexing vb i;
  let (| a, _, _, BufferView buf v |) = vb in
  let es = B.as_seq h buf in
  as_seq'_len es v;
  as_seq'_sel' v es i

let get_sel #b h vb i = as_seq_sel h vb i

val as_seq'_slice (#a #b: _)
                  (v:view a b)
                  (es:Seq.seq a)
                  (i:nat{i < Seq.length es * View?.n v})
  : Lemma
    (ensures (
      as_seq'_len es v;
      indexing' v (Seq.length es) i;
      let n = View?.n v in
      View?.get v (Seq.index es (i / n)) ==
      Seq.slice (as_seq' es v) (n * (i /n)) (n * (i / n) + n)))
    (decreases (Seq.length es))

#push-options "--z3rlimit 100"
let rec as_seq'_slice #a #b v es i =
  let n = View?.n v in
  if Seq.length es = 0 then ()
  else let bs = as_seq' es v in
       if i < n then
         begin
         assert (View?.get v (Seq.index es (i / n)) `Seq.equal`
                 Seq.slice (as_seq' es v) (n * (i /n)) (n * (i / n) + n))
         end
       else let as' = Seq.tail es in
            let j  = i - n in
            as_seq'_slice v (Seq.tail es) (i - n);
            as_seq'_len as' v;
            indexing' v (Seq.length as') j;
            FStar.Math.Lemmas.add_div_mod_1 j n;
            assert (View?.get v (Seq.index as' (j / n)) `Seq.equal`
                    Seq.slice (as_seq' as' v) (n * (j / n)) (n * (j / n) + n));
            assert (Seq.slice (as_seq' as' v) (n * (j / n)) (n * (j / n) + n) `Seq.equal`
                    Seq.slice (as_seq' es v) (n * (j / n) + n) (n * (j / n) + n + n));
            FStar.Math.Lemmas.add_div_mod_1 j n;
            assert (j / n == i / n - 1)
#pop-options

let put_sel #b h vb i =
    indexing vb i;
    let v = get_view vb in
    let n = View?.n v in
    let es = (B.as_seq h (as_buffer vb)) in
    as_seq'_slice v es i;
    as_seq'_len es v;
    assert (View?.put v (View?.get v (Seq.index es (i / n))) ==
            View?.put v (Seq.slice (as_seq' es v) (n * (i /n)) (n * (i / n) + n)))

let rec upd_seq' (#a #b: _) (v:view a b) (s:Seq.seq b{Seq.length s % View?.n v = 0}) (acc:Seq.seq a)
  : GTot (Seq.lseq a (Seq.length acc + Seq.length s / View?.n v))
         (decreases (Seq.length s)) =
  let n = View?.n v in
  if Seq.length s = 0 then acc
  else let pfx, suffix = Seq.split s n in
       Math.lemma_mod_sub (Seq.length s) n 1;
       let es = upd_seq' v suffix acc in
       Seq.cons (View?.put v pfx) es

let upd_seq #b h vb s =
  let (| a, _, _, BufferView b v |) = vb in
  Math.cancel_mul_mod (B.length b) (View?.n v);
  let es : Seq.seq a = upd_seq' v s Seq.empty in
  B.g_upd_seq b es h

let as_seq'_cons (#a #b:_) (v:view a b) (hd:a) (tl:Seq.seq a)
  : Lemma (as_seq' (Seq.cons hd tl) v == View?.get v hd `Seq.append` as_seq' tl v)
  = let s = Seq.cons hd tl in
    assert (Seq.head s == hd);
    assert (Seq.tail s `Seq.equal` tl)

let rec upd_seq'_spec (#a #b: _) (v:view a b) (s:Seq.seq b{Seq.length s % View?.n v = 0}) (acc:Seq.seq a)
  : Lemma
      (ensures (
        let es = upd_seq' v s acc in
        as_seq' es v `Seq.equal` Seq.append s (as_seq' acc v)))
      (decreases (Seq.length s))
  = if Seq.length s = 0 then ()
    else let n = View?.n v in
         let pfx, suffix = Seq.split s n in
         Math.lemma_mod_sub (Seq.length s) n 1;
         upd_seq'_spec v suffix acc;
         as_seq'_slice v (upd_seq' v s acc) 0;
         let as' = upd_seq' v suffix acc in
         assert (as_seq' as' v `Seq.equal` Seq.append suffix (as_seq' acc v));
         let es = upd_seq' v s acc in
         assert (es `Seq.equal` Seq.cons (View?.put v pfx) as');
         as_seq'_cons v (View?.put v pfx) as'

#push-options "--z3rlimit 20"
let upd_seq_spec (#b: _) (h:HS.mem) (vb:buffer b{live h vb}) (s:Seq.seq b{Seq.length s = length vb})
  = let h' = upd_seq h vb s in
    Math.cancel_mul_mod (B.length (as_buffer vb)) (View?.n (get_view vb));
    let es = upd_seq' (get_view vb) s Seq.empty in
    B.g_upd_seq_as_seq (as_buffer vb) es h;
    lemma_g_upd_with_same_seq (as_buffer vb) h es;
    assert (FStar.HyperStack.ST.equal_domains h h');
    assert (modifies vb h h');
    upd_seq'_spec (get_view vb) s Seq.empty;
    assert (as_seq h' vb `Seq.equal` s);
    assert (as_seq h vb == as_seq' (B.as_seq h (as_buffer vb)) (get_view vb));
    assert (as_seq h' vb == s);
    assert (es == B.as_seq h' (as_buffer vb));
    let v= get_view vb in
    FStar.Classical.forall_intro_2 (fun as1 as2 ->
      Classical.move_requires (as_seq'_injective v as1) as2
         <: Lemma ((as_seq' as1 v `Seq.equal` as_seq' as2 v) ==> (as1 `Seq.equal` as2)))
#pop-options
