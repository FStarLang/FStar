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

module Steel.PCM.ArrayStruct.Pointer

module AS = Steel.PCM.ArrayStruct
module Mem = Steel.PCM.Memory
module SizeT = Steel.SizeT
module Map = FStar.Map


open FStar.FunctionalExtensionality
module PCM = Steel.PCM
module UPCM = Steel.PCM.Unitless
module UPCMBase = Steel.PCM.Unitless.Base

#set-options "--fuel 2 --ifuel 2"

noeq type declared_array_struct : Type u#(a+1) = {
  descriptor: AS.array_struct_descriptor u#a;
  pcm: UPCM.unitless_pcm (AS.array_struct_type descriptor)
}

let declared_array_struct_type (a: declared_array_struct u#a) : Type u#a =
  AS.array_struct_type a.descriptor

let declared_array_struct_pcm
  (a: declared_array_struct u#a)
    : UPCM.unitless_pcm (declared_array_struct_type a) =
  a.pcm


let declare_base (a: Type u#a) (pcm: UPCM.unitless_pcm a) : declared_array_struct u#a = {
  descriptor = AS.DBase a;
  pcm = pcm
}

let declare_array (base: declared_array_struct u#a) (len: Steel.SizeT.t)
    : declared_array_struct u#a
  =
  {
    descriptor = AS.DArray (base.descriptor) len;
    pcm = AS.pointwise_array_pcm (AS.array_struct_type base.descriptor) len base.pcm;
  }

let declare_struct
  (base: (AS.field_id ^-> option (declared_array_struct u#a)))
  (name: string)
    : declared_array_struct u#a
  =
  let field_descriptors = on _ (fun f ->
      match base f with
      | None -> None
      | Some b -> Some b.descriptor
  ) in
  let field_types = AS.struct_field_type field_descriptors in
  let field_pcms : (field: AS.field_id -> (UPCM.unitless_pcm (field_types field))) = fun f ->
    match base f with
    | None -> UPCMBase.exclusive_unitless_pcm
    | Some b -> b.pcm
  in
  AS.struct_field_type_unroll_lemma field_descriptors;
  {
    descriptor = AS.DStruct (field_descriptors);
    pcm = AS.pointwise_struct_pcm field_types field_pcms;
  }

type path_item : Type u#0 =
  | PEnd
  | PIndex: i:SizeT.t -> path_item
  | PField: field: AS.field_id -> path_item

let path : Type u#0 = list path_item

let rec valid_path
  (d: AS.array_struct_descriptor u#a)
  (path: path)
  : Tot prop (decreases path)
  =
  match d, path with
  | AS.DBase _, [PEnd] -> True
  | AS.DArray sub_d len, (PIndex i)::sub_path ->
    SizeT.v i < SizeT.v len /\
    valid_path sub_d sub_path
  | AS.DStruct fields, (PField field)::sub_path -> begin
    match fields field with
    | None -> False
    | Some sub_descr ->
      valid_path sub_descr sub_path
    end
  | _ -> False

let qualified
  (p: path)
  (a: declared_array_struct u#a)
  : Tot prop
  = valid_path a.descriptor p

let rec sub_array_struct
  (a: declared_array_struct u#a)
  (p: path{p `qualified` a})
  : declared_array_struct u#a
  =
  match a.descriptor, p with
  | AS.DBase _, _ ->
     a
  | AS.DArray sub_d len, (PIndex i)::sub_path ->
    let sub_pcm : UPCM.unitless_pcm (AS.array_struct_type sub_d) =
      admit()
    in
    sub_array_struct ({ descriptor = sub_d; pcm = sub_pcm }) sub_path
  | _ -> admit()


noeq type array_struct_ref
  (a: declared_array_struct u#a)
  : Type u#0
  = {
  mem_ref: Mem.ref
    (option (AS.array_struct_type a.descriptor))
    (UPCM.to_full_pcm_with_unit a.pcm);
  path: (path:path{path `qualified` a})
}

open Steel.PCM.Memory

let pts_to_array_struct
  (#a: declared_array_struct)
  (r: array_struct_ref a)
  (v : declared_array_struct_type a)
  : slprop u#a
  = pts_to r.mem_ref (Some v)

assume val read_array_struct
  (#a: declared_array_struct)
  (r: array_struct_ref a)
  (e: inames)
  (v0: Ghost.erased (declared_array_struct_type a))
  : action_except
    (v:(declared_array_struct_type a){
      UPCM.compatible (declared_array_struct_pcm a) v0 v
    })
    e
    (pts_to_array_struct r v0)
    (fun v -> pts_to_array_struct r v)
