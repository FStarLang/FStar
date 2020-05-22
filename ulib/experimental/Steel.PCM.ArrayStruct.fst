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

module Steel.PCM.ArrayStruct
module U32 = FStar.UInt32
module Univ = FStar.Universe
module DepMap = FStar.DependentMap

open FStar.FunctionalExtensionality
open Steel.PCM
open Steel.PCM.Unitless
module SizeT = Steel.SizeT

#set-options "--fuel 1 --ifuel 1"

let struct_field_type_unroll_lemma
  (field_descriptors: (field_id ^-> option (array_struct_descriptor u#a)))
    : Lemma
    (DependentMap.t u#a field_id (struct_field_type u#a field_descriptors) ==
      array_struct_type u#a (DStruct u#a field_descriptors)) =
  let open FStar.Tactics in
  FStar.Tactics.Effect.assert_by_tactic (DependentMap.t field_id
        (struct_field_type field_descriptors) ==
      array_struct_type (DStruct field_descriptors))
    (fun _ -> compute ())

let pointwise_array_pcm (cell_type: Type u#a) (len: SizeT.t) (base_pcm: unitless_pcm cell_type)
    : unitless_pcm (array_type cell_type len) =
  let pcm':unitless_pcm' (array_type cell_type len) =
    { unitless_composable = composable_array base_pcm; unitless_op = compose_array base_pcm }
  in
  {
    unitless_p = pcm';
    unitless_comm
    =
    (fun x y ->
        let xy = pcm'.unitless_op x y in
        let yx = pcm'.unitless_op y x in
        let aux (i: nat{i < SizeT.v len}) : Lemma (Seq.index xy i == Seq.index yx i) =
          base_pcm.unitless_comm (Seq.index x i) (Seq.index y i)
        in
        Classical.forall_intro aux;
        assert (xy `Seq.equal` yx));
    unitless_assoc
    =
    (fun x y z ->
        let x_yz = pcm'.unitless_op x (pcm'.unitless_op y z) in
        let aux (i: nat{i < SizeT.v len})
            : Lemma
            (let xi = Seq.index x i in
              let yi = Seq.index y i in
              let zi = Seq.index z i in
              base_pcm.unitless_p.unitless_composable xi yi /\
              base_pcm.unitless_p.unitless_composable (base_pcm.unitless_p.unitless_op xi yi) zi /\
              base_pcm.unitless_p.unitless_op xi (base_pcm.unitless_p.unitless_op yi zi) ==
              base_pcm.unitless_p.unitless_op (base_pcm.unitless_p.unitless_op xi yi) zi) =
          let xi = Seq.index x i in
          let yi = Seq.index y i in
          let zi = Seq.index z i in
          base_pcm.unitless_assoc xi yi zi
        in
        Classical.forall_intro aux;
        let xy_z = pcm'.unitless_op (pcm'.unitless_op x y) z in
        assert (x_yz `Seq.equal` xy_z));
    unitless_assoc_r
    =
    (fun x y z ->
        let xy_z = pcm'.unitless_op (pcm'.unitless_op x y) z in
        let aux (i: nat{i < SizeT.v len})
            : Lemma
            (let xi = Seq.index x i in
              let yi = Seq.index y i in
              let zi = Seq.index z i in
              base_pcm.unitless_p.unitless_composable yi zi /\
              base_pcm.unitless_p.unitless_composable xi (base_pcm.unitless_p.unitless_op yi zi) /\
              base_pcm.unitless_p.unitless_op (base_pcm.unitless_p.unitless_op xi yi) zi ==
              base_pcm.unitless_p.unitless_op xi (base_pcm.unitless_p.unitless_op yi zi)) =
          let xi = Seq.index x i in
          let yi = Seq.index y i in
          let zi = Seq.index z i in
          base_pcm.unitless_assoc_r xi yi zi
        in
        Classical.forall_intro aux;
        let x_yz = pcm'.unitless_op x (pcm'.unitless_op y z) in
        assert (x_yz `Seq.equal` xy_z))
  }

let reveal_pointwise_array_pcm
      (cell_type: Type u#a)
      (len: SizeT.t)
      (base_pcm: unitless_pcm cell_type)
    : Lemma
    (let pcm = pointwise_array_pcm cell_type len base_pcm in
      pcm.unitless_p.unitless_composable == composable_array base_pcm /\
      pcm.unitless_p.unitless_op == compose_array base_pcm) = ()

let pointwise_struct_pcm
      (field_types: (field_id -> Type u#a))
      (base_pcms: (field: field_id -> unitless_pcm (field_types field)))
    : unitless_pcm (struct_type field_types) =
  let pcm':unitless_pcm' (struct_type field_types) =
    { unitless_composable = composable_struct base_pcms; unitless_op = compose_struct base_pcms }
  in
  {
    unitless_p = pcm';
    unitless_comm
    =
    (fun x y ->
        let xy = pcm'.unitless_op x y in
        let yx = pcm'.unitless_op y x in
        let aux (f: field_id) : Lemma (DepMap.sel xy f == DepMap.sel yx f) =
          (base_pcms f).unitless_comm (DepMap.sel x f) (DepMap.sel y f)
        in
        Classical.forall_intro aux;
        assert (xy `DepMap.equal` yx));
    unitless_assoc
    =
    (fun x y z ->
        let x_yz = pcm'.unitless_op x (pcm'.unitless_op y z) in
        let aux (f: field_id)
            : Lemma
            (let xf = DepMap.sel x f in
              let yf = DepMap.sel y f in
              let zf = DepMap.sel z f in
              (base_pcms f).unitless_p.unitless_composable xf yf /\
              (base_pcms f).unitless_p.unitless_composable ((base_pcms f).unitless_p.unitless_op xf
                    yf)
                zf /\
              (base_pcms f).unitless_p.unitless_op xf ((base_pcms f).unitless_p.unitless_op yf zf) ==
              (base_pcms f).unitless_p.unitless_op ((base_pcms f).unitless_p.unitless_op xf yf) zf)
        =
          let xf = DepMap.sel x f in
          let yf = DepMap.sel y f in
          let zf = DepMap.sel z f in
          (base_pcms f).unitless_assoc xf yf zf
        in
        Classical.forall_intro aux;
        let xy_z = pcm'.unitless_op (pcm'.unitless_op x y) z in
        assert (x_yz `DepMap.equal` xy_z));
    unitless_assoc_r
    =
    (fun x y z ->
        let xy_z = pcm'.unitless_op (pcm'.unitless_op x y) z in
        let aux (f: field_id)
            : Lemma
            (let xf = DepMap.sel x f in
              let yf = DepMap.sel y f in
              let zf = DepMap.sel z f in
              (base_pcms f).unitless_p.unitless_composable yf zf /\
              (base_pcms f).unitless_p.unitless_composable xf
                ((base_pcms f).unitless_p.unitless_op yf zf) /\
              (base_pcms f).unitless_p.unitless_op ((base_pcms f).unitless_p.unitless_op xf yf) zf ==
              (base_pcms f).unitless_p.unitless_op xf ((base_pcms f).unitless_p.unitless_op yf zf))
        =
          let xf = DepMap.sel x f in
          let yf = DepMap.sel y f in
          let zf = DepMap.sel z f in
          (base_pcms f).unitless_assoc_r xf yf zf
        in
        Classical.forall_intro aux;
        let x_yz = pcm'.unitless_op x (pcm'.unitless_op y z) in
        assert (x_yz `DepMap.equal` xy_z))
  }

let reveal_pointwise_struct_pcm
      (field_types: (field_id -> Type u#a))
      (base_pcms: (field: field_id -> unitless_pcm (field_types field)))
    : Lemma
    (let pcm = pointwise_struct_pcm field_types base_pcms in
      pcm.unitless_p.unitless_composable == composable_struct base_pcms /\
      pcm.unitless_p.unitless_op == compose_struct base_pcms) = ()
