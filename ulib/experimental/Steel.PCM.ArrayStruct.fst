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

type usize = U32.t
let v_usize = U32.v

//TODO: use Steel.SizeT

#set-options "--fuel 1 --ifuel 1"

type field_id = string

noeq type array_struct_descriptor : Type u#(a+1) =
  | DBase:
    a: Type u#a ->
    array_struct_descriptor
  | DArray:
    cell_descriptor:array_struct_descriptor u#a ->
    len:usize ->
    array_struct_descriptor
  | DStruct:
    field_descriptors: (field_id ^-> array_struct_descriptor u#a) ->
    array_struct_descriptor
  // Missing: untagged unions (not must have)

unfold let struct_field_type'
  (field_descriptors: (field_id ^-> array_struct_descriptor u#a))
  (array_struct_type: (descriptor: array_struct_descriptor u#a{
    descriptor << field_descriptors
  }) -> Tot (Type u#a))
  (field: field_id)
  : Tot (Type u#a) =
  let descr = field_descriptors field in
  FStar.WellFounded.axiom1 field_descriptors field;
  array_struct_type descr

let array_type (cell_type: Type u#a) (len: usize) : Type u#a =
  Seq.lseq cell_type (v_usize len)

let struct_type (field_typs: field_id -> Type u#a) : Type u#a =
  DepMap.t field_id field_typs

let rec array_struct_type (descriptor: array_struct_descriptor u#a) : Tot (Type u#a) (decreases descriptor) =
  match descriptor with
  | DBase a -> a
  | DArray descriptor' len ->
    let typ' = array_struct_type descriptor' in
    array_type typ' len
  | DStruct field_descriptors ->
    let typs' = struct_field_type' field_descriptors array_struct_type in
    struct_type typs'

unfold let struct_field_type
  (field_descriptors: (field_id ^-> (array_struct_descriptor u#a)))
  (field: field_id)
  : Tot (Type u#a) =
  struct_field_type' field_descriptors array_struct_type field

noeq type array_struct_nested_pcm : Type u#(a+1) =
  | PBase:
    a: Type u#a ->
    pcm: pcm a ->
    array_struct_nested_pcm
  | PArray:
    cell_type: Type u#a ->
    len: usize ->
    cell_nested_pcm: array_struct_nested_pcm u#a ->
    array_pcm: (pcm cell_type -> pcm (array_type cell_type len)) ->
    array_struct_nested_pcm
  | PStruct:
    field_types: (field_id ^-> Type u#a) ->
    field_nested_pcms: (field:field_id -> array_struct_nested_pcm u#a) ->
    struct_pcm: ((field:field_id -> pcm (field_types field)) -> pcm (struct_type field_types)) ->
    array_struct_nested_pcm

let rec nested_pcm_sync
  (descriptor: array_struct_descriptor)
  (nested_pcm: array_struct_nested_pcm) : GTot prop (decreases descriptor) =
  match descriptor, nested_pcm with
  | DBase da, PBase va _ ->
    da == va
  | DArray cell_descriptor dlen, PArray cell_type plen cell_nested_pcm _  ->
    dlen = plen /\ cell_type == array_struct_type cell_descriptor /\
    cell_descriptor `nested_pcm_sync` cell_nested_pcm
  | DStruct field_descriptors, PStruct field_types field_nested_pcms struct_pcm ->
    field_types == struct_field_type field_descriptors /\
    (forall (field: field_id). begin
      FStar.WellFounded.axiom1 field_descriptors field;
      field_descriptors field `nested_pcm_sync` field_nested_pcms field
    end)
  | _ -> False

noeq type array_struct : Type u#(a+1) =
  | ArrayStruct:
    descriptor: array_struct_descriptor u#a ->
    nested_pcm: array_struct_nested_pcm u#a{descriptor `nested_pcm_sync` nested_pcm} ->
    value: array_struct_type descriptor ->
    array_struct

let struct_field_type_unroll_lemma
  (field_descriptors : (field_id ^-> array_struct_descriptor u#a))
    : Lemma (
      DependentMap.t u#a field_id (struct_field_type u#a field_descriptors) ==
      array_struct_type u#a (DStruct u#a field_descriptors)
     )
  =
  let open FStar.Tactics in
  assert (
    DependentMap.t field_id (struct_field_type field_descriptors) ==
    array_struct_type (DStruct field_descriptors)
  ) by begin
    compute ()
  end

let rec nested_pcm_to_pcm
  (descriptor: array_struct_descriptor u#a)
  (nested_pcm: array_struct_nested_pcm u#a{descriptor `nested_pcm_sync` nested_pcm})
    : Tot (pcm (array_struct_type descriptor)) (decreases descriptor) =
  match descriptor, nested_pcm with
  | _, PBase _ pcm -> pcm
  | DArray cell_descriptor _, PArray cell_type _ cell_nested_pcm array_pcm ->
    array_pcm (nested_pcm_to_pcm cell_descriptor cell_nested_pcm)
  | DStruct field_descriptors, PStruct field_types field_nested_pcms struct_pcm ->
    assert(descriptor `nested_pcm_sync` nested_pcm);
    assume(field_types == struct_field_type field_descriptors); // Why can't F* find this???
    struct_field_type_unroll_lemma field_descriptors;
    struct_pcm (fun field ->
      FStar.WellFounded.axiom1 field_descriptors field;
      nested_pcm_to_pcm (field_descriptors field) (field_nested_pcms field)
    )

let composable_array_struct : symrel u#(a+1) (array_struct u#a) = fun (s0 s1: array_struct u#a) ->
  s0.descriptor == s1.descriptor /\ s0.nested_pcm == s1.nested_pcm /\
  composable (nested_pcm_to_pcm s0.descriptor s0.nested_pcm) s0.value s1.value

let compose_array_struct
  (s0: array_struct u#a)
  (s1: array_struct u#a{s0 `composable_array_struct` s1})
    : array_struct u#a
  =
  let new_val = op (nested_pcm_to_pcm s0.descriptor s0.nested_pcm) s0.value s1.value in
  ArrayStruct s0.descriptor s0.nested_pcm new_val

let unit_pcm' : pcm' u#a (Univ.raise_t u#0 u#a unit) = {
    composable = (fun _ _ -> True);
    op = (fun _ _ -> Univ.raise_val u#0 u#a () );
    one =  Univ.raise_val u#0 u#a ()
  }

let higher_unit (x: Univ.raise_t u#0 u#a unit) : Lemma (x == Univ.raise_val u#0 u#a ()) =
  let aux (_ : squash (x =!= Univ.raise_val u#0 u#a ())) : Lemma (False) =
      let x0 = Univ.downgrade_val u#0 u#a x in
      assert(x0 == ())
  in
  Classical.excluded_middle (x == Univ.raise_val u#0 u#a ());
  Classical.or_elim
    #(x == Univ.raise_val u#0 u#a ())
    #(x =!= Univ.raise_val u#0 u#a ())
    #(fun _ -> unit_pcm'.composable x unit_pcm'.one /\ unit_pcm'.op x unit_pcm'.one == x)
    (fun _ -> ())
    (fun _ -> aux ())

let unit_pcm : pcm u#a (Univ.raise_t u#0 u#a unit)  = {
  p = unit_pcm' u#a;
  comm = (fun _ _  -> ());
  assoc = (fun _ _ _ -> ());
  assoc_r = (fun _ _ _ -> ());
  is_unit = (fun x -> higher_unit x)
}

let array_struct_unit : array_struct u#a =
  ArrayStruct
    (DBase (Univ.raise_t u#0 u#a unit))
    (PBase (Univ.raise_t u#0 u#a unit) unit_pcm)
    (Univ.raise_val u#0 u#a ())

#set-options "--print_universes --print_implicits"

let array_struct_pcm' : pcm' u#(a+1) (array_struct u#a) = {
  composable = composable_array_struct u#a;
  op = compose_array_struct u#a;
  one = array_struct_unit u#a;
}

let array_struct_pcm : pcm u#(a+1) (array_struct u#a) = {
  p = array_struct_pcm' u#a;
  comm = (fun _ _  -> admit());
  assoc = (fun _ _ _ -> admit());
  assoc_r = (fun _ _ _ -> admit());
  is_unit = (fun x -> admit());
}
