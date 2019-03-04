(*
   Copyright 2008-2019 Microsoft Research

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
module LowStar.Lens.Tuple2
open LowStar.Lens
open FStar.HyperStack.ST
module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module LB = LowStar.Lens.Buffer

/// `composable`: A product lens can be constructed from lenses with
/// disjoint footprints and identical snapshots
let composable (l1:hs_lens 'a 'b) (l2:hs_lens 'c 'd) =
    B.all_disjoint [Ghost.reveal l1.footprint;
                    Ghost.reveal l2.footprint] /\
    l1.snapshot == l2.snapshot

///  `mk`: An abstract product of lenses. Typically, one would instead
/// use the product of buffer lenses, see below
//abstract
let mk #a1 #b1 (l1 : hs_lens a1 b1)
       #a2 #b2 (l2 : hs_lens a2 b2{composable l1 l2})
  : hs_lens (a1 & a2) (b1 & b2)
  = let fp =
      Ghost.hide (
        B.loc_union_l [Ghost.reveal l1.footprint;
                       Ghost.reveal l2.footprint
                      ])
    in
    let inv (a, b) h : prop =
      l1.invariant a h /\
      l2.invariant b h
    in
    let x = l1.x, l2.x in
    let snap : imem (inv x) = l1.snapshot in
    let get : get_t (imem (inv x)) (b1 & b2) =
      fun h ->
        l1.l.get h,
        l2.l.get h
      in
    let put : put_t (imem (inv x)) (b1 & b2) =
      fun (v1, v2) h ->
         l2.l.put v2
        (l1.l.put v1 h)
    in
    let l : imem_lens (inv x) (b1 & b2) fp =
      {
        get = get;
        put = put;
        lens_laws = ()
      }
    in
    {
      footprint = fp;
      invariant = inv;
      x = x;
      l = l;
      snapshot = snap
    }

/// `op_fst`: Generically lift an operation on
/// the first component
let op_fst #a #b #c #d #result #pre #post
      (l1:hs_lens a b)
      (l2:hs_lens c d{composable l1 l2})
      (op:with_snapshot l1 result pre post)
  : LensST result (mk l1 l2)
    (requires fun (b0, d0) -> pre b0)
    (ensures fun (b0, d0) r (b1, d1) ->
      d0 == d1 /\
      post b0 r b1)
  = reveal_inv ();
    let s = FStar.HyperStack.ST.get () in
    op s

/// `op_fst`: Generically lift an operation on
/// the second component
let op_snd #a #b #c #d #result #pre #post
      (l1:hs_lens a b)
      (l2:hs_lens c d{composable l1 l2})
      (op:with_snapshot l2 result pre post)
  : LensST result (mk l1 l2)
    (requires fun (b0, d0) -> pre d0)
    (ensures fun (b0, d0) r (b1, d1) ->
      b0 == b1 /\
      post d0 r d1)
  = reveal_inv ();
    let s = FStar.HyperStack.ST.get () in
    op s

(* Rather than generic operations, it is more common to work
   with tuples of buffers and pointers.

   We provide special support for operations on pairs for
   buffer/pointer lenses.
*)

/// `lens_fst`: A pure lens for the first component of a pair
unfold
let lens_fst #a #b : lens (a & b) a =
  {
    get = (fun (x, y) -> x);
    put = (fun x (_, y) -> x, y);
    lens_laws = ()
  }

/// `lens_snd`: A pure lens for the first component of a pair
unfold
let lens_snd #a #b : lens (a & b) b =
  {
    get = (fun (x, y) -> y);
    put = (fun y (x, _) -> x, y);
    lens_laws = ()
  }

/// `tup2_t f1 f2`:
/// Encapsulates a product lens on f1 and f2-flavored buffer lenses
noeq
type tup2_t
       (#a1:_) (#p1:_) (#q1:_) (#b1:B.mbuffer a1 p1 q1) (f1:LB.flavor b1)
       (#a2:_) (#p2:_) (#q2:_) (#b2:B.mbuffer a2 p2 q2) (f2:LB.flavor b2) =
  | Mk : bl1:LB.buffer_lens b1 f1 ->
         bl2:LB.buffer_lens b2 f2{composable (LB.lens_of bl1) (LB.lens_of bl2)} ->
         read_fst:LB.reader_t f1
                              (lens_fst #(LB.view_type_of f1) #(LB.view_type_of f2))
                              (mk (LB.lens_of bl1) (LB.lens_of bl2)) ->
         read_snd:LB.reader_t f2
                              (lens_snd #(LB.view_type_of f1) #(LB.view_type_of f2))
                              (mk (LB.lens_of bl1) (LB.lens_of bl2)) ->
         write_fst:LB.writer_t f1
                              (lens_fst #(LB.view_type_of f1) #(LB.view_type_of f2))
                              (mk (LB.lens_of bl1) (LB.lens_of bl2)) ->
         write_snd:LB.writer_t f2
                              (lens_snd #(LB.view_type_of f1) #(LB.view_type_of f2))
                              (mk (LB.lens_of bl1) (LB.lens_of bl2)) ->
         tup2_t f1 f2

/// `mk_tup2`: Constructing a tup2_t from a pair of buffer lenses
let mk_tup2
       (#a1:_) (#p1:_) (#q1:_) (#b1:B.mbuffer a1 p1 q1) (#f1:LB.flavor b1)
       (#a2:_) (#p2:_) (#q2:_) (#b2:B.mbuffer a2 p2 q2) (#f2:LB.flavor b2)
       (bl1:LB.buffer_lens b1 f1)
       (bl2:LB.buffer_lens b2 f2{composable (LB.lens_of bl1) (LB.lens_of bl2)})
  : tup2_t f1 f2
  = let pl = mk (LB.lens_of bl1) (LB.lens_of bl2) in
    let l_fst = lens_fst #(LB.view_type_of f1) #(LB.view_type_of f2) in
    let l_snd = lens_snd #(LB.view_type_of f1) #(LB.view_type_of f2) in
    let read_fst
       : LB.reader_t f1 l_fst pl
       = fun i ->
          reveal_inv();
          let s = HST.get () in
          LB.(bl1.reader s i)
    in
    let read_snd
       : LB.reader_t f2 l_snd pl
       = fun i ->
          reveal_inv();
          let s = HST.get () in
          LB.(bl2.reader s i)
    in
    let write_fst
      : LB.writer_t f1 l_fst pl
      = fun i v ->
          reveal_inv ();
          let s = HST.get () in
          LB.(bl1.writer s i v)
    in
    let write_snd
      : LB.writer_t f2 l_snd pl
      = fun i v ->
          reveal_inv ();
          let s = HST.get () in
          LB.(bl2.writer s i v)
    in
    Mk bl1 bl2 read_fst read_snd write_fst write_snd

/// `lens_of`: Projecting a product lens from a tup2_t
let lens_of (#b1:B.mbuffer 'a 'b 'c) (#f1:LB.flavor b1)
            (#b2:B.mbuffer 'p 'q 'r) (#f2:LB.flavor b2)
            (t:tup2_t f1 f2)
   : hs_lens (B.mbuffer 'a 'b 'c & B.mbuffer 'p 'q 'r)
          LB.(view_type_of f1 & view_type_of f2) =
  mk (LB.lens_of t.bl1) (LB.lens_of t.bl2)

(* Exporting the projectors at cleaner types for tighter VC generation *)
unfold
let l_fst (#b1:B.mbuffer 'a 'b 'c) (#f1:LB.flavor b1)
          (#b2:B.mbuffer 'p 'q 'r) (#f2:LB.flavor b2)
    = lens_fst #(LB.view_type_of f1) #(LB.view_type_of f2)

unfold
let l_snd (#b1:B.mbuffer 'a 'b 'c) (#f1:LB.flavor b1)
          (#b2:B.mbuffer 'p 'q 'r) (#f2:LB.flavor b2)
    = lens_snd #(LB.view_type_of f1) #(LB.view_type_of f2)

let read_fst (#b1:B.mbuffer 'a 'b 'c) (#f1:LB.flavor b1)
             (#b2:B.mbuffer 'p 'q 'r) (#f2:LB.flavor b2)
             (t:tup2_t f1 f2)
   : LB.reader_t f1 lens_fst (lens_of t)             
   = t.read_fst

let read_snd (#b1:B.mbuffer 'a 'b 'c) (#f1:LB.flavor b1)
             (#b2:B.mbuffer 'p 'q 'r) (#f2:LB.flavor b2)
             (t:tup2_t f1 f2)
   : LB.reader_t f2 lens_snd (lens_of t)             
   = t.read_snd

let write_fst (#b1:B.mbuffer 'a 'b 'c) (#f1:LB.flavor b1)
             (#b2:B.mbuffer 'p 'q 'r) (#f2:LB.flavor b2)
             (t:tup2_t f1 f2)
   : LB.writer_t f1 lens_fst (lens_of t)             
   = t.write_fst

let write_snd (#b1:B.mbuffer 'a 'b 'c) (#f1:LB.flavor b1)
             (#b2:B.mbuffer 'p 'q 'r) (#f2:LB.flavor b2)
             (t:tup2_t f1 f2)
   : LB.writer_t f2 lens_snd (lens_of t)             
   = t.write_snd

(* Now a few tests *)

/// `test_read_ptr_fst`: Reading a pointer in the first component
/// is just applying `read_fst` 
let test_read_ptr_fst
         (#b1:B.pointer 'a)
         (#b2:B.mbuffer 'p 'q 'r)
         (t:tup2_t (LB.ptr b1) (LB.buf b2))
  : LensST 'a (lens_of t)
    (requires (fun _ -> True))
    (ensures (fun (a0, b0) a (a1, b1) ->
      a0 == a1 /\
      b0 == b1 /\
      a == a1))
  = read_fst t 0ul

/// `test_read_buf_snd`: Reading a buffer in the second component
/// is just applying `read_snd` 
let test_read_buf_snd
          (#b1:B.pointer 'a)
          (#b2:B.mbuffer 'p 'q 'r)
          (t:tup2_t (LB.ptr b1) (LB.buf b2)) (i:LB.ix b2)
  : LensST 'p (lens_of t)
    (requires (fun b0 -> True))
    (ensures (fun (a0, b0) b (a1, b1) ->
      a0 == a1 /\
      b0 == b1 /\
      b == Seq.index b1 (UInt32.v i)))
  = read_snd t i

/// `test_write_ptr_fst`: Writing a pointer in the first component
/// is just applying `write_fst`
let test_write_ptr_fst
         (#b1:B.pointer 'a)
         (#b2:B.mbuffer 'p 'q 'r)
         (t:tup2_t (LB.ptr b1) (LB.buf b2)) (v:'a)
  : LensST unit (lens_of t)
    (requires (fun _ -> True))
    (ensures (fun (a0, b0) a (a1, b1) ->
      b0 == b1 /\
      v == a1))
  = write_fst t 0ul v

/// `test_write_buf_snd`: Writing a buffer in the second component
/// is just applying `write_snd`
/// Note the use of the preorder in the precondition
let test_write_buf (#a #p:_) (#q #r: _)
         (#b1:B.pointer a)
         (#b2:B.mbuffer p q r)
         (t:tup2_t (LB.ptr b1) (LB.buf b2))
         (i:LB.ix b2) (v:p)
  : LensST unit (lens_of t)
    (requires (fun (_, b0) -> b0 `r` Seq.upd b0 (UInt32.v i) v))
    (ensures (fun (a0, b0) _ (a1, b1) ->
      a0 == a1 /\
      b1 == Seq.upd b0 (UInt32.v i) v))
  = write_snd t i v

let elim_tup2_inv
       (#a1:_) (#p1:_) (#q1:_) (#b1:B.mbuffer a1 p1 q1) (#f1:LB.flavor b1)
       (#a2:_) (#p2:_) (#q2:_) (#b2:B.mbuffer a2 p2 q2) (#f2:LB.flavor b2)
       (bl1:LB.buffer_lens b1 f1)
       (bl2:LB.buffer_lens b2 f2{composable (LB.lens_of bl1) (LB.lens_of bl2)})
   : Lemma (let t = mk_tup2 bl1 bl2 in
            reveal_inv();
            (forall h. {:pattern inv (lens_of t) h}
              inv (lens_of t) h ==>
              (LB.lens_of bl1).invariant b1 h /\
              (LB.lens_of bl2).invariant b2 h /\              
              B.modifies (B.loc_union (B.loc_buffer b1) (B.loc_buffer b2))
                         (LB.lens_of bl1).snapshot
                         h /\
              HST.equal_stack_domains (LB.lens_of bl1).snapshot h /\
              view (lens_of t) h ==
               (view (snap (LB.lens_of bl1) h) h, 
                view (snap (LB.lens_of bl2) h) h)))

   = reveal_inv()
