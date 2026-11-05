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

(* A binary serialization format for the compiler's persistent data
   (.checked files), written in F* so that every backend reads and writes
   the same bytes.  Instances are hand-written, one per type, and must read
   back exactly what they write.

   Sharing: a value of a type whose instance is built with [shared] is
   written once; every later occurrence that the table deems equal is a
   reference to it, and is read back as the same (physically equal) value.
   This keeps the format compact and the loaded data shared in memory.  A
   shared value is written as the unsigned varint 0 followed by its
   contents, and a reference to the [k]-th shared value of its table as
   [k + 1].  Values are numbered when they have been written, children
   first, so the reader numbers them in the same order. *)

open FStarC.Effect
open FStarC.Class.Deq
open FStarC.Class.Hashable
module BB = FStarC.ByteBuffer
module I = FStarC.SmallInt

(* A sharing table: one per shared type, allocated once at the top level. *)
new val slot : Type0
val new_slot : string -> ML slot

new val writer : Type0
new val reader : Type0

val writer_create : unit -> ML writer
val writer_contents : writer -> ML string
val raw_writer : writer -> BB.writer

(* A reader of [s] from byte offset [off] on. *)
val reader_create : s:string -> off:I.t -> ML reader
val raw_reader : reader -> BB.reader

(* Raises [BB.Malformed], as do the readers on a malformed input. *)
val malformed (#a:Type) (what:string) : ML a

class serializable (a:Type) = {
  ser   : writer -> a -> ML unit;
  deser : reader -> ML a;
}

(* The whole of [s] must be consumed. *)
val serialize   (#a:Type) {| serializable a |} (x:a) : ML string
val deserialize (#a:Type) {| serializable a |} (s:string) : ML a

(* Constructor tags. *)
val write_tag : writer -> FStar.UInt8.t -> ML unit
val read_tag  : reader -> ML FStar.UInt8.t
(* A tag that does not belong to the type being read. *)
val bad_tag (#a:Type) (ty:string) (t:FStar.UInt8.t) : ML a

instance val serializable_unit   : serializable unit
instance val serializable_bool   : serializable bool
instance val serializable_int    : serializable int
instance val serializable_smallint : serializable I.t
instance val serializable_char   : serializable FStar.Char.char

(* Writes [x] with [f], or a reference to an equal value (by [deq] and
   [hashable]) written before.  For recursive types, whose serializers
   cannot be built with [shared]. *)
val write_shared (#a:Type0) {| deq a |} {| hashable a |}
  (s:slot) (w:writer) (x:a) (f:writer -> a -> ML unit) : ML unit
(* Reads what [write_shared] wrote, using [f] for a new value. *)
val read_shared (#a:Type0) (s:slot) (r:reader) (f:reader -> ML a) : ML a

(* Shares the values that are equal by [deq] and [hashable] ([inner] writes
   and reads one). *)
val shared (#a:Type0) {| deq a |} {| hashable a |} (s:slot) (inner:serializable a)
  : serializable a

(* Directed acyclic graphs, for recursive types whose values cannot be
   cheaply hashed physically.  A value is written as the definitions of
   the nodes not written before, children first, each as the unsigned
   varint 0 followed by the node, and then as [k + 1] for its node [k].
   Nodes are identified by a [key] that includes the numbers of their
   children, so equal subterms are written once (hash-consing).  Within a
   node, children are referred to by number, see [dag_child]. *)

(* Defines the node [key] with [f], unless it was defined before; returns
   its number. *)
val dag_node (#k:Type0) {| deq k |} {| hashable k |}
  (s:slot) (w:writer) (key:k) (f:writer -> ML unit) : ML I.t
(* Ends a value: a reference to its root node. *)
val dag_end : writer -> I.t -> ML unit
(* Reads a value, using [f] to read a node. *)
val dag_read (#a:Type) (s:slot) (r:reader) (f:reader -> ML a) : ML a
(* Writes and reads a reference to a node, within a node. *)
val dag_write_child : writer -> I.t -> ML unit
val dag_read_child (#a:Type) (s:slot) (r:reader) : ML a

(* Lists and options with an explicit element serializer, in the format of
   [serializable_list] and [serializable_option].  For recursive types. *)
val ser_list (#a:Type) ([@@@FStar.Attributes.monomorphize] f:writer -> a -> ML unit)
  (w:writer) (l:list a) : ML unit
val deser_list (#a:Type) ([@@@FStar.Attributes.monomorphize] f:reader -> ML a)
  (r:reader) : ML (list a)
val ser_option (#a:Type) ([@@@FStar.Attributes.monomorphize] f:writer -> a -> ML unit)
  (w:writer) (o:option a) : ML unit
val deser_option (#a:Type) ([@@@FStar.Attributes.monomorphize] f:reader -> ML a)
  (r:reader) : ML (option a)

(* Strings are shared. *)
instance val serializable_string : serializable string

instance val serializable_option
  (#a:Type) (_ : serializable a) : serializable (option a)
instance val serializable_list
  (#a:Type) (_ : serializable a) : serializable (list a)
instance val serializable_either
  (#a #b:Type) (_ : serializable a) (_ : serializable b) : serializable (either a b)
instance val serializable_tuple2
  (#a #b:Type) (_ : serializable a) (_ : serializable b) : serializable (a & b)
instance val serializable_tuple3
  (#a #b #c:Type) (_ : serializable a) (_ : serializable b) (_ : serializable c)
  : serializable (a & b & c)
instance val serializable_tuple4
  (#a #b #c #d:Type) (_ : serializable a) (_ : serializable b) (_ : serializable c)
  (_ : serializable d) : serializable (a & b & c & d)

