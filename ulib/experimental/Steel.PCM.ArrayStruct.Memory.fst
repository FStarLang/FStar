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
module Univ = FStar.Universe
module DepMap = FStar.DependentMap

open FStar.FunctionalExtensionality
open Steel.PCM

type usize = U32.t
let v_usize = U32.v

//TODO: use Steel.SizeT

#set-options "--fuel 1 --ifuel 1 --print_universes"

type field_id = string

noeq type array_struct_descriptor : Type u#(a+1) =
  // You can store your own funky PCM in the Base case
  | Base: a: Type u#a -> pcm: pcm a -> array_struct_descriptor
  | Array: t:array_struct_descriptor u#a -> len:usize -> array_struct_descriptor
  | Struct: field_descriptors: (field_id ^-> option (array_struct_descriptor u#a)) ->
    array_struct_descriptor
  // Missing: untagged unions (not must have)


let rec array_struct_type (descriptor: array_struct_descriptor u#a) : Tot (Type u#a) (decreases descriptor) =
  match descriptor with
  | Base a pcm -> a
  | Array descriptor' len ->
    let type' = array_struct_type descriptor' in
    Seq.lseq type' (v_usize len)
  | Struct field_descriptors ->
    DepMap.t field_id (fun field_id -> match field_descriptors field_id with
      | Some descr ->
        FStar.WellFounded.axiom1 field_descriptors field_id;
        array_struct_type descr
      | None -> Univ.raise_t u#0 u#a False)

noeq type array_struct : Type u#(a+1) =
  | ArrayStruct:
    descriptor: array_struct_descriptor u#a ->
    value:(array_struct_type  descriptor) -> array_struct

let field_type
  (s: array_struct u#a{Struct? s.descriptor})
  (field: field_id)
    : Tot (Type u#a) =
  match (Struct?.field_descriptors s.descriptor) field with
  | Some descr ->
    array_struct_type descr
  | None -> Univ.raise_t u#0 u#a False

let field_type_unroll_lemma
  (s: array_struct u#a{Struct? s.descriptor})
  (field: field_id)
  : Lemma (DependentMap.t field_id (field_type s) == array_struct_type s.descriptor)
  =
  let open FStar.Tactics in
  // TODO: prove that using some kind of normalization ?
  admit();
  assert (DependentMap.t field_id (field_type s) == array_struct_type s.descriptor) by begin
    norm [delta_only ["Steel.PCM.ArrayStruct.Memory.field_type"]];
    // TODO: how to unroll array_struct_type recursive definition here? zeta(_full) does not work
    fail "HERE"
  end

let rec composable_array_struct' (s0 s1: array_struct) : Tot prop (decreases s0.descriptor) =
  match s0.descriptor, s1.descriptor with
  | Base a0 pcm0, Base a1 pcm1 ->
    a0 == a1 /\ pcm0 == pcm1 /\
    composable pcm0 s0.value s1.value
  | Array descriptor0 len0, Array descriptor1 len1 ->
    descriptor0 == descriptor1 /\ len0 == len1 /\
    begin forall (i:nat{i < v_usize len0}).
      let val0 = Seq.index s0.value i in
      let val1 = Seq.index s1.value i in
      let sub_s0 = ArrayStruct descriptor0 val0 in
      let sub_s1 = ArrayStruct descriptor1 val1 in
      composable_array_struct' sub_s0 sub_s1
    end
  | Struct field_descriptors0, Struct field_descriptors1 ->
    field_descriptors0 == field_descriptors1 /\ begin forall (field: field_id). begin
      match field_descriptors0 field, field_descriptors1 field with
      | Some sub_descriptor0, Some sub_descriptor1 ->
        field_type_unroll_lemma s0 field;
        let v0 : DependentMap.t field_id (field_type s0) = s0.value in
        let sub_v0 = DepMap.sel #_ #(field_type s0) v0 field in
        field_type_unroll_lemma s1 field;
        let v1 : DependentMap.t field_id (field_type s1) = s1.value in
        let sub_v1 = DepMap.sel #_ #(field_type s1) v1 field in
        let sub_s0 = ArrayStruct sub_descriptor0 sub_v0 in
        let sub_s1 = ArrayStruct sub_descriptor1 sub_v1 in
         FStar.WellFounded.axiom1 field_descriptors0 field;
        composable_array_struct' sub_s0 sub_s1
      | None, None -> True
    end end
  | _ -> False

#push-options "--warn_error -271"
let rec composable_sym (s0 s1: array_struct)
    : Lemma
      (requires True)
      (ensures (composable_array_struct' s0 s1 <==> composable_array_struct' s1 s0))
      (decreases s0.descriptor)
  =
  match s0.descriptor, s1.descriptor with
  | Base a0 pcm0, Base a1 pcm1 ->
    ()
  | Array descriptor0 len0, Array descriptor1 len1 ->
    let aux (_ : squash (composable_array_struct' s0 s1))
        : Lemma (composable_array_struct' s1 s0) =
      let aux (i:nat{i < v_usize len0}) : Lemma (
        let val0 = Seq.index s0.value i in
        let val1 = Seq.index s1.value i in
        let sub_s0 = ArrayStruct descriptor0 val0 in
        let sub_s1 = ArrayStruct descriptor1 val1 in
        composable_array_struct' sub_s1 sub_s0
      ) =
        let val0 = Seq.index s0.value i in
        let val1 = Seq.index s1.value i in
        let sub_s0 = ArrayStruct descriptor0 val0 in
        let sub_s1 = ArrayStruct descriptor1 val1 in
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
        let sub_s0 = ArrayStruct descriptor0 val0 in
        let sub_s1 = ArrayStruct descriptor1 val1 in
        composable_array_struct' sub_s0 sub_s1
      ) =
        let val0 = Seq.index s0.value i in
        let val1 = Seq.index s1.value i in
        let sub_s0 = ArrayStruct descriptor0 val0 in
        let sub_s1 = ArrayStruct descriptor1 val1 in
        composable_sym sub_s0 sub_s1
      in
      Classical.forall_intro aux
    in
    Classical.impl_intro aux
  | Struct field_descriptors0, Struct field_descriptors1 ->
    let aux (_ : squash (composable_array_struct' s0 s1))
       : Lemma (composable_array_struct' s1 s0) =
      let aux' (field: field_id) : Lemma (
        match field_descriptors0 field, field_descriptors1 field with
        | Some sub_descriptor0, Some sub_descriptor1 ->
          field_type_unroll_lemma s0 field;
          let v0 : DependentMap.t field_id (field_type s0) = s0.value in
          let sub_v0 = DepMap.sel #_ #(field_type s0) v0 field in
          field_type_unroll_lemma s1 field;
          let v1 : DependentMap.t field_id (field_type s1) = s1.value in
          let sub_v1 = DepMap.sel #_ #(field_type s1) v1 field in
          let sub_s0 = ArrayStruct sub_descriptor0 sub_v0 in
          let sub_s1 = ArrayStruct sub_descriptor1 sub_v1 in
          FStar.WellFounded.axiom1 field_descriptors0 field;
          composable_array_struct' sub_s0 sub_s1
        | None, None -> True
      ) =
        match field_descriptors0 field, field_descriptors1 field with
        | Some sub_descriptor0, Some sub_descriptor1 ->
          field_type_unroll_lemma s0 field;
          let v0 : DependentMap.t field_id (field_type s0) = s0.value in
          let sub_v0 = DepMap.sel #_ #(field_type s0) v0 field in
          field_type_unroll_lemma s1 field;
          let v1 : DependentMap.t field_id (field_type s1) = s1.value in
          let sub_v1 = DepMap.sel #_ #(field_type s1) v1 field in
          let sub_s0 = ArrayStruct sub_descriptor0 sub_v0 in
          let sub_s1 = ArrayStruct sub_descriptor1 sub_v1 in
          FStar.WellFounded.axiom1 field_descriptors0 field;
          composable_sym sub_s1 sub_s0
        | None, None -> ()
      in
      admit();
      //TODO: why is the forall_intro not working?
      Classical.forall_intro aux';
      admit()
    in
    Classical.impl_intro aux;
    assume(composable_array_struct' s1 s0 ==> composable_array_struct' s0 s1)
  | _ -> ()

let composable_array_struct : symrel array_struct =
  Classical.forall_intro_2 composable_sym;
  composable_array_struct'

let rec compose_array_struct
  (s0 : array_struct)
  (s1: array_struct{s0 `composable_array_struct` s1})
    : Tot (s':array_struct{s'.descriptor == s0.descriptor})
      (decreases s0.descriptor)
  =
  match s0.descriptor, s1.descriptor with
  | Base a0 pcm0, Base a1 pcm1 ->
    ArrayStruct s0.descriptor (op pcm0 s0.value s1.value)
  | Array descriptor0 len0, Array descriptor1 len1 ->
    let new_val : Seq.lseq (array_struct_type descriptor0) (v_usize len0) =
      Seq.init (v_usize len0) (fun i ->
        let val0 = Seq.index s0.value i in
        let val1 = Seq.index s1.value i in
        let sub_s0 = ArrayStruct descriptor0 val0 in
        let sub_s1 = ArrayStruct descriptor1 val1 in
        let new_as : array_struct = compose_array_struct sub_s0 sub_s1 in
        let out : (array_struct_type descriptor0) = new_as.value in
        out
      )
    in
    ArrayStruct s0.descriptor new_val
  | Struct field_descriptors0, Struct field_descriptors1 ->
    admit()

let unit_pcm : pcm unit = {
  p = {
    composable = (fun () () -> True);
    op = (fun () () -> ());
    one = ()
  };
  comm = (fun _ _  -> ());
  assoc = (fun _ _ _ -> ());
  assoc_r = (fun _ _ _ -> ());
  is_unit = (fun _ -> ())
}

let one_array_struct = ArrayStruct (Base unit unit_pcm) ()

let array_struct_pcm' : pcm' array_struct = {
  composable = composable_array_struct;
  op = compose_array_struct;
  one = one_array_struct
}
