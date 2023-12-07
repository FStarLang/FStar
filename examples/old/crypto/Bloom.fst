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
module Bloom

open FStar.All
open FStar.String
open FStar.IO
open FStar.Heap
open FStar.Seq

open Format

type Pos (i: int) = (i > 0)
type ln_t = ln:uint16{Pos ln}
type hash = h:seq byte{Seq.length h >= 2}
type text = seq byte
type hash_fn = text -> Tot hash
type bloom (ln:ln_t) = bl:seq bool{Seq.length bl = ln}

type Le (ln:ln_t) (bl1:bloom ln) (bl2:bloom ln) =
  forall i . (0 <= i && i < ln) ==> ((not (Seq.index bl1 i)) || (Seq.index bl2 i))

val create: ln:ln_t -> Tot (bl:bloom ln)
let create ln = Seq.create ln false

val check: ln:ln_t -> h:hash_fn -> n:uint16 -> x:text -> bl:bloom ln -> Tot (b:bool)
let rec check ln h n x bl =
  if n > 0 then
  begin
    let pt = Seq.append (uint16_to_bytes n) x in
    let hs = Seq.slice (h pt) 0 2 in
    let i = op_Modulus (bytes_to_uint16 hs) ln in
    let b = Seq.index bl i in
    if b then check ln h (n-1) x bl
    else false
  end
  else true

val add: ln:ln_t -> h:hash_fn -> n:uint16 -> x:text -> bl:bloom ln -> Tot (bl':bloom ln{Le ln bl bl' /\ check ln h n x bl'})
let rec add ln h n x bl =
  if n > 0 then
  begin
    let pt = Seq.append (uint16_to_bytes n) x in
    let hs = Seq.slice (h pt) 0 2 in
    let i = op_Modulus (bytes_to_uint16 hs) ln in
    let bl' = Seq.upd bl i true in
    let bl'' = add ln h (n-1) x bl' in
    bl''
  end
  else bl
