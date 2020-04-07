(*
   Copyright 2020 Microsoft Research

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
module Steel.PCM.ArrayStruct.Memory
module U32 = FStar.UInt32

open FStar.FunctionalExtensionality
open Steel.PCM

type usize = U32.t
let v_usize = U32.v

//TODO: change contents to descriptor
//TODO: use Steel.SizeT

#set-options "--fuel 1 --ifuel 1"

noeq type array_struct_contents : Type u#(a+1) =
  | Base: a: Type u#a -> pcm: pcm a -> array_struct_contents
  | Array: t:array_struct_contents u#a -> len:usize -> array_struct_contents

let rec array_struct_type (contents: array_struct_contents) : Tot Type (decreases contents) =
  match contents with
  | Base a pcm -> a
  | Array contents' len ->
    let type' = array_struct_type contents' in
    Seq.lseq type' (v_usize len)

noeq type array_struct : Type u#(a+1) =
  | ArrayStruct:
    contents: array_struct_contents u#a ->
    value:(array_struct_type contents) ->
    array_struct

let rec composable_array_struct' (s0 s1: array_struct) : Tot prop (decreases s0.contents) =
  match s0.contents, s1.contents with
  | Base a0 pcm0, Base a1 pcm1 ->
    a0 == a1 /\ pcm0 == pcm1 /\
    composable pcm0 s0.value s1.value
  | Array contents0 len0, Array contents1 len1 ->
    contents0 == contents1 /\ len0 == len1 /\
    begin forall (i:nat{i < v_usize len0}).
      let val0 = Seq.index s0.value i in
      let val1 = Seq.index s1.value i in
      let sub_s0 = ArrayStruct contents0 val0 in
      let sub_s1 = ArrayStruct contents1 val1 in
      composable_array_struct' sub_s0 sub_s1
    end
  | _ -> False

let rec composable_sym (s0 s1: array_struct)
    : Lemma(composable_array_struct' s0 s1 <==> composable_array_struct' s1 s0) =
  match s0.contents, s1.contents with
  | Base a0 pcm0, Base a1 pcm1 ->
    ()
  | Array contents0 len0, Array contents1 len1 ->
    let aux (_ : squash (composable_array_struct' s0 s1))
        : Lemma (composable_array_struct' s1 s0) =
      let aux (i:nat{i < v_usize len0}) : Lemma (
        let val0 = Seq.index s0.value i in
        let val1 = Seq.index s1.value i in
        let sub_s0 = ArrayStruct contents0 val0 in
        let sub_s1 = ArrayStruct contents1 val1 in
        composable_array_struct' sub_s1 sub_s0
      ) =
        let val0 = Seq.index s0.value i in
        let val1 = Seq.index s1.value i in
        let sub_s0 = ArrayStruct contents0 val0 in
        let sub_s1 = ArrayStruct contents1 val1 in
        assume(sub_s0 << s0);
        assume(sub_s1 << s1);
        composable_sym sub_s0 sub_s1
      in
      Classical.forall_intro aux
    in
    Classical.impl_intro aux;
    let aux (_ : squash (composable_array_struct' s1 s0))
        : Lemma (composable_array_struct' s0 s1) =
      let aux (i:nat{i < v_usize len0}) : Lemma (
        let val0 = Seq.index s0.value i in
        let val1 = Seq.index s1.value i in
        let sub_s0 = ArrayStruct contents0 val0 in
        let sub_s1 = ArrayStruct contents1 val1 in
        composable_array_struct' sub_s0 sub_s1
      ) =
        let val0 = Seq.index s0.value i in
        let val1 = Seq.index s1.value i in
        let sub_s0 = ArrayStruct contents0 val0 in
        let sub_s1 = ArrayStruct contents1 val1 in
        assume(sub_s0 << s0);
        assume(sub_s1 << s1);
        composable_sym sub_s0 sub_s1
      in
      Classical.forall_intro aux
    in
    Classical.impl_intro aux
  | _ -> ()

let composable_array_struct : symrel array_struct =
  Classical.forall_intro_2 composable_sym;
  composable_array_struct'

let rec compose_array_struct
  (s0 : array_struct)
  (s1: array_struct{s0 `composable_array_struct` s1})
    : Tot (s':array_struct{s'.contents == s0.contents})
  =
  match s0.contents, s1.contents with
  | Base a0 pcm0, Base a1 pcm1 ->
    ArrayStruct s0.contents (op pcm0 s0.value s1.value)
  | Array contents0 len0, Array contents1 len1 ->
    let new_val : Seq.lseq (array_struct_type contents0) (v_usize len0) =
      Seq.init (v_usize len0) (fun i ->
        let val0 = Seq.index s0.value i in
        let val1 = Seq.index s1.value i in
        let sub_s0 = ArrayStruct contents0 val0 in
        let sub_s1 = ArrayStruct contents1 val1 in
        assume(sub_s0 << s0);
        assume(sub_s1 << s1);
        let new_as : array_struct = compose_array_struct sub_s0 sub_s1 in
        let out : (array_struct_type contents0) = new_as.value in
        out
      )
    in
    ArrayStruct s0.contents new_val


let one_array_struct = ArrayStruct (Base unit (magic())) ()

let array_struct_pcm' : pcm' array_struct = {
  composable = composable_array_struct;
  op = compose_array_struct;
  one = one_array_struct
}
