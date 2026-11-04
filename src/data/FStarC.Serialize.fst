(*
   Copyright 2008-2026 Microsoft Research

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
module FStarC.Serialize

open FStarC.Effect
open FStarC.Class.Deq
open FStarC.Class.Hashable
module BB = FStarC.ByteBuffer
module I = FStarC.SmallInt
module A = FStarC.Array
module HT = FStarC.HashTable
module D = FStar.Dyn

(* The sharing tables of a writer or reader, indexed by slot: [None] until
   the first value of the slot's type is written or read. *)
let max_slots : I.t = I.of_int 64

type slot = I.t

let slot_names : ref (list string) = mk_ref []
let next_slot : ref I.t = mk_ref I.zero

let new_slot name =
  let s = !next_slot in
  if I.(s >= max_slots) then failwith "FStarC.Serialize.new_slot: too many slots";
  next_slot := I.(s + one);
  slot_names := name :: !slot_names;
  s

noeq type writer = {
  wbuf    : BB.writer;
  wtables : A.array (option D.dyn);
}

(* Slot [s] of [rtables] holds the values read so far as an [A.array a]
   (once there is one), and [rcounts] how many there are.  Boxed, since a
   reader is passed to every deserializer. *)
[@@cherry_boxed]
noeq type reader = {
  rbuf    : BB.reader;
  rtables : A.array (option D.dyn);
  rcounts : A.array I.t;
}

let writer_create () = { wbuf = BB.writer_create (); wtables = A.make max_slots None }
let writer_contents w = BB.writer_contents w.wbuf
let raw_writer w = w.wbuf

let reader_create s off =
  { rbuf = BB.reader_create s off; rtables = A.make max_slots None; rcounts = A.make max_slots I.zero }
let raw_reader r = r.rbuf

let malformed #a what = raise (BB.Malformed what)

let serialize #a {| serializable a |} x =
  let w = writer_create () in
  ser w x;
  writer_contents w

let deserialize #a {| serializable a |} s =
  let r = reader_create s I.zero in
  let x = deser r in
  if BB.reader_pos r.rbuf <> FStarC.String.byte_length s then malformed "trailing data";
  x

let write_tag w t = BB.write_byte w.wbuf (I.of_int t)
let read_tag r = I.to_int (BB.read_byte r.rbuf)

let bad_tag #a ty t = malformed (Format.fmt2 "bad tag %s for %s" (string_of_int t) ty)

instance serializable_unit : serializable unit = {
  ser = (fun _ _ -> ());
  deser = (fun _ -> ());
}

instance serializable_bool : serializable bool = {
  ser = (fun w b -> BB.write_byte w.wbuf (if b then I.one else I.zero));
  deser = (fun r ->
    let b = BB.read_byte r.rbuf in
    if b = I.zero then false
    else if b = I.one then true
    else malformed "bad bool");
}

instance serializable_int : serializable int = {
  ser = (fun w x -> BB.write_int w.wbuf x);
  deser = (fun r -> BB.read_int r.rbuf);
}

instance serializable_smallint : serializable I.t = {
  ser = (fun w x -> BB.write_varint w.wbuf x);
  deser = (fun r -> BB.read_varint r.rbuf);
}

instance serializable_char : serializable FStar.Char.char = {
  ser = (fun w c -> BB.write_uvarint w.wbuf (I.of_char c));
  deser = (fun r ->
    let n = I.to_int (BB.read_uvarint r.rbuf) in
    if (0 <= n && n < 0xd7ff) || (0xe000 <= n && n <= 0x10ffff)
    then FStar.Char.char_of_int n
    else malformed "bad char");
}

(* The writer's table of a slot: the values written so far, numbered. *)
(* A writer's table maps the hash of a value to the values with that hash
   written so far, and their numbers.  It is keyed by the hash, rather than
   by the value, so that every slot uses the same instance of [HT.t] (on the
   OCaml backend, every key type is a functor application of its own). *)
let deq_hash_code : deq FStarC.Hash.hash_code = { (=?) = (fun h1 h2 -> h1 =? h2) }
let hashable_hash_code : hashable FStarC.Hash.hash_code = { hash = (fun h -> h) }

type wtable_t (a:Type0) =
  HT.t FStarC.Hash.hash_code #deq_hash_code #hashable_hash_code (list (a & I.t)) & ref I.t

let wtable (#a:Type0) (w:writer) (s:slot) : ML (wtable_t a) =
  match A.get w.wtables s with
  | Some d -> D.undyn d
  | None ->
    let t : wtable_t a = (HT.create #_ #deq_hash_code #hashable_hash_code #_ 1024, mk_ref I.zero) in
    A.set w.wtables s (Some (D.mkdyn t));
    t

let rec assoc_deq (#a:Type0) {| deq a |} (x:a) (l:list (a & I.t)) : ML (option I.t) =
  match l with
  | [] -> None
  | (y, k) :: l -> if x =? y then Some k else assoc_deq x l

let wtable_find (#a:Type0) {| deq a |} (h:FStarC.Hash.hash_code) (t:wtable_t a) (x:a)
  : ML (option I.t) =
  match HT.try_find #_ #deq_hash_code #hashable_hash_code #_ (fst t) h with
  | Some l -> assoc_deq x l
  | None -> None

(* Numbers [x] as the next value of [t]. *)
let wtable_add (#a:Type0) (h:FStarC.Hash.hash_code) (t:wtable_t a) (x:a) : ML I.t =
  let (tbl, count) = t in
  let l = match HT.try_find #_ #deq_hash_code #hashable_hash_code #_ tbl h with
          | Some l -> l
          | None -> [] in
  let k = !count in
  HT.add #_ #deq_hash_code #hashable_hash_code #_ tbl h ((x, k) :: l);
  count := I.(k + one);
  k

(* The tables are looked up in place: the reader is borrowed, so its fields
   are not counted. *)
let rtable_push (#a:Type) ([@@@FStar.Attributes.cherry_borrowed] r:reader) (s:slot) (x:a) : ML unit =
  let k = A.get r.rcounts s in
  (if k = I.zero then A.set r.rtables s (Some (D.mkdyn (A.make (I.of_int 1024) x)))
   else match A.get r.rtables s with
   | Some d ->
     let v : A.array a = D.undyn d in
     if I.(k >= A.length v) then begin
       let v = A.append v v in
       A.set v k x;
       A.set r.rtables s (Some (D.mkdyn v))
     end else A.set v k x
   | None -> malformed "reader table");
  A.set r.rcounts s I.(k + one)

let rtable_get (#a:Type) ([@@@FStar.Attributes.cherry_borrowed] r:reader) (s:slot) (k:I.t) : ML a =
  if I.(k >= zero && k < A.get r.rcounts s) then
    match A.get r.rtables s with
    | Some d -> A.get (D.undyn d <: A.array a) k
    | None -> malformed "bad back-reference"
  else malformed "bad back-reference"

let write_shared #a {| deq a |} {| hashable a |} s w x f =
  let t = wtable #a w s in
  let h = hash x in
  match wtable_find h t x with
  | Some k -> BB.write_uvarint w.wbuf I.(k + one)
  | None ->
    BB.write_uvarint w.wbuf I.zero;
    f w x;
    let _ = wtable_add h t x in
    ()

let read_shared #a s r f =
  let k = BB.read_uvarint r.rbuf in
  if k = I.zero then begin
    let x = f r in
    rtable_push r s x;
    x
  end else rtable_get #a r s I.(k - one)

let shared #a {| deq a |} {| hashable a |} s inner = {
  ser = (fun w x -> write_shared s w x inner.ser);
  deser = (fun r -> read_shared s r inner.deser);
}

let dag_node #k {| deq k |} {| hashable k |} s w key f =
  let t = wtable #k w s in
  let h = hash key in
  match wtable_find h t key with
  | Some n -> n
  | None ->
    BB.write_uvarint w.wbuf I.zero;
    f w;
    wtable_add h t key

let dag_end w n = BB.write_uvarint w.wbuf I.(n + one)

let rec dag_read #a s r f =
  let k = BB.read_uvarint r.rbuf in
  if k = I.zero then begin
    let x = f r in
    rtable_push r s x;
    dag_read s r f
  end else rtable_get #a r s I.(k - one)

let dag_write_child w n = BB.write_uvarint w.wbuf n

let dag_read_child #a s r =
  let k = BB.read_uvarint r.rbuf in
  rtable_get #a r s k

let rec ser_elems (#a:Type) ([@@@FStar.Attributes.monomorphize] f:writer -> a -> ML unit)
  (w:writer) (l:list a) : ML unit =
  match l with
  | [] -> ()
  | x :: xs -> f w x; ser_elems f w xs

let rec deser_elems (#a:Type) ([@@@FStar.Attributes.monomorphize] f:reader -> ML a)
  (r:reader) (n:I.t) (acc:list a) : ML (list a) =
  if n = I.zero then List.rev acc
  else
    let x = f r in
    deser_elems f r I.(n - one) (x :: acc)

let ser_list #a f w l =
  BB.write_uvarint w.wbuf (I.of_int (List.length l));
  ser_elems f w l

let deser_list #a f r =
  let n = BB.read_uvarint r.rbuf in
  deser_elems f r n []

let ser_option #a f w o =
  match o with
  | None -> write_tag w 0
  | Some v -> write_tag w 1; f w v

let deser_option #a f r =
  match read_tag r with
  | 0 -> None
  | 1 -> Some (f r)
  | t -> bad_tag "option" t

let string_slot = new_slot "string"

instance serializable_string : serializable string =
  shared string_slot {
    ser = (fun w s -> BB.write_string w.wbuf s);
    deser = (fun r -> BB.read_string r.rbuf);
  }

instance serializable_option #a (_ : serializable a) : serializable (option a) = {
  ser = (fun w x -> ser_option ser w x);
  deser = (fun r -> deser_option deser r);
}

instance serializable_list #a (_ : serializable a) : serializable (list a) = {
  ser = (fun w l -> ser_list ser w l);
  deser = (fun r -> deser_list deser r);
}

instance serializable_either #a #b (_ : serializable a) (_ : serializable b)
  : serializable (either a b) = {
  ser = (fun w x ->
    match x with
    | Inl v -> write_tag w 0; ser w v
    | Inr v -> write_tag w 1; ser w v);
  deser = (fun r ->
    match read_tag r with
    | 0 -> Inl (deser r)
    | 1 -> Inr (deser r)
    | t -> bad_tag "either" t);
}

instance serializable_tuple2 #a #b (_ : serializable a) (_ : serializable b)
  : serializable (a & b) = {
  ser = (fun w (x, y) -> ser w x; ser w y);
  deser = (fun r ->
    let x = deser r in
    let y = deser r in
    (x, y));
}

instance serializable_tuple3 #a #b #c (_ : serializable a) (_ : serializable b)
  (_ : serializable c) : serializable (a & b & c) = {
  ser = (fun w (x, y, z) -> ser w x; ser w y; ser w z);
  deser = (fun r ->
    let x = deser r in
    let y = deser r in
    let z = deser r in
    (x, y, z));
}

instance serializable_tuple4 #a #b #c #d (_ : serializable a) (_ : serializable b)
  (_ : serializable c) (_ : serializable d) : serializable (a & b & c & d) = {
  ser = (fun w (x, y, z, u) -> ser w x; ser w y; ser w z; ser w u);
  deser = (fun r ->
    let x = deser r in
    let y = deser r in
    let z = deser r in
    let u = deser r in
    (x, y, z, u));
}
