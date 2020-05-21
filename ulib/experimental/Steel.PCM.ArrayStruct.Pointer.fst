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

module PCM = Steel.PCM
module UPCM = Steel.PCM.Unitless

#set-options "--fuel 1 --ifuel 1"

type path_item : Type u#0 =
  | PEnd
  | PIndex: i:SizeT.t -> path_item
  | PField: field: AS.field_id -> path_item

let path : Type u#0 = list path_item

let array_structs_context : Type u#(a+1) = Map.t string (AS.array_struct_descriptor u#a)

let declared_array_struct
  (c: array_structs_context u#a)
  = s:string{Map.contains c s}

let declared_array_struct_descriptor
  (#c: array_structs_context u#a)
  (a: declared_array_struct c)
  : Tot (AS.array_struct_descriptor u#a)
  =
  Map.sel c a

let declared_array_struct_type
  (#c: array_structs_context u#a)
  (a: declared_array_struct c)
  : Tot Type
  =
  AS.array_struct_type (declared_array_struct_descriptor a)

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
  | AS.DStruct fields, (PField field)::sub_path ->
    valid_path (fields field) sub_path
  | _ -> False

let qualified
  (p: path)
  (#c: array_structs_context u#a)
  (a: declared_array_struct c)
  : Tot prop
  = valid_path (declared_array_struct_descriptor a) p

noeq type array_struct_ref
  (#c: array_structs_context u#a)
  (a: declared_array_struct c)
  (pcm: UPCM.unitless_pcm (declared_array_struct_type a))
  : Type u#0
  = {
  mem_ref: Mem.ref
    (option (declared_array_struct_type a))
    (UPCM.to_full_pcm_with_unit pcm);
  path: (path:path{path `qualified` a})
}
