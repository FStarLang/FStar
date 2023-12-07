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
(*rename mvector to vector. The word sstarray is used for memory-stored vectors *)
module FStar.Regions.RSTArray
open FStar.Regions.RSTWhile
open FStar.Regions.Regions  open FStar.Regions.Heap  open FStar.Regions.Located
open FStar.Regions.RST
open MachineWord
open FStar.Heap
open Stack
open FStar.Set
open FStar.Seq

type sstarray (a:Type) = lref (seq a)


(*Can we reinclude the types here, even when they are included in .fsi?
  F* does not complain, even if we change the types*)
 (*val length : #a:Type -> (sstarray a) -> Tot string
 let length v = "cat"*)

open FStar.Ghost
let asRef va = hide va

let readIndex 'a r index =
  let rv = (memread (r)) in (Seq.index rv index)

let writeIndex 'a r index newV =
  let rv = (memread (r) ) in
  memwrite (r) (Seq.upd rv index newV)

let screateSeq init = (ralloc init)

let hcreateSeq init = (halloc init)

let screate len init = (ralloc (Seq.create len init))

let hcreate len init = (halloc (Seq.create len init))

let to_seq  r = memread (r)

let length r = Seq.length (memread r)
