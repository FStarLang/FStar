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

type usize = U32.t
let v_usize = U32.v

//TODO: use Steel.SizeT

#set-options "--fuel 1 --ifuel 1"

type field_id = string

/// The descriptor contains all the information necessary to derive the type of the values
/// corresponding to an arraystruct.
noeq
type array_struct_descriptor : Type u#(a + 1) =
  | DBase : a: Type u#a -> array_struct_descriptor
  | DArray : cell_descriptor: array_struct_descriptor u#a -> len: usize -> array_struct_descriptor
  | DStruct : field_descriptors: (field_id ^-> array_struct_descriptor u#a)
    -> array_struct_descriptor

// Missing: untagged unions (not must have)
unfold
let struct_field_type'
      (field_descriptors: (field_id ^-> array_struct_descriptor u#a))
      (array_struct_type:
          (descriptor: array_struct_descriptor u#a {descriptor << field_descriptors}
              -> Tot (Type u#a)))
      (field: field_id)
    : Tot (Type u#a) =
  let descr = field_descriptors field in
  FStar.WellFounded.axiom1 field_descriptors field;
  array_struct_type descr

let array_type (cell_type: Type u#a) (len: usize) : Type u#a = Seq.lseq cell_type (v_usize len)

let struct_type (field_typs: (field_id -> Type u#a)) : Type u#a = DepMap.t field_id field_typs

/// This functions achives the descriptor -> Type correspondence
let rec array_struct_type (descriptor: array_struct_descriptor u#a)
    : Tot (Type u#a) (decreases descriptor) =
  match descriptor with
  | DBase a -> a
  | DArray descriptor' len ->
    let typ' = array_struct_type descriptor' in
    array_type typ' len
  | DStruct field_descriptors ->
    let typs' = struct_field_type' field_descriptors array_struct_type in
    struct_type typs'
unfold
let struct_field_type
      (field_descriptors: (field_id ^-> (array_struct_descriptor u#a)))
      (field: field_id)
    : Tot (Type u#a) = struct_field_type' field_descriptors array_struct_type field
noeq
type array_struct : Type u#(a + 1) =
  | ArrayStruct : 
      descriptor: array_struct_descriptor u#a ->
      pcm: unitless_pcm (array_struct_type descriptor) ->
      value: array_struct_type descriptor
    -> array_struct

let struct_field_type_unroll_lemma (field_descriptors: (field_id ^-> array_struct_descriptor u#a))
    : Lemma
    (DependentMap.t u#a field_id (struct_field_type u#a field_descriptors) ==
      array_struct_type u#a (DStruct u#a field_descriptors)) =
  let open FStar.Tactics in
  FStar.Tactics.Effect.assert_by_tactic (DependentMap.t field_id
        (struct_field_type field_descriptors) ==
      array_struct_type (DStruct field_descriptors))
    (fun _ ->
        ();
        compute ())

/// Composability is then based on the composability of the nested PCM.
let composable_array_struct:symrel u#(a + 1) (array_struct u#a) =
  fun (s0: array_struct u#a) (s1: array_struct u#a) ->
    s0.descriptor == s1.descriptor /\ s0.pcm == s1.pcm /\
    s0.pcm.unitless_p.unitless_composable s0.value s1.value

let compose_array_struct
      (s0: array_struct u#a)
      (s1: array_struct u#a {s0 `composable_array_struct` s1})
    : array_struct u#a =
  let new_val = s0.pcm.unitless_p.unitless_op s0.value s1.value in
  ArrayStruct s0.descriptor s0.pcm new_val

#set-options "--print_universes --print_implicits"

let array_struct_unitless_pcm':unitless_pcm' u#(a + 1) (array_struct u#a) =
  { unitless_composable = composable_array_struct u#a; unitless_op = compose_array_struct u#a }

let array_struct_unitless_pcm:unitless_pcm u#(a + 1) (array_struct u#a) =
  {
    unitless_p = array_struct_unitless_pcm' u#a;
    unitless_comm = (fun s0 s1 -> s0.pcm.unitless_comm s0.value s1.value);
    unitless_assoc = (fun s0 s1 s2 -> s0.pcm.unitless_assoc s0.value s1.value s2.value);
    unitless_assoc_r = (fun s0 s1 s2 -> s0.pcm.unitless_assoc_r s0.value s1.value s2.value)
  }

let array_struct_pcm:pcm u#(a + 1) (option u#(a + 1) (array_struct u#a)) =
  to_full_pcm_with_unit array_struct_unitless_pcm

////////////////////////////////////////////////////////////////////
// PCM builders
////////////////////////////////////////////////////////////////////

let pointwise_array_pcm (cell_type: Type u#a) (len: usize) (base_pcm: unitless_pcm cell_type)
    : unitless_pcm (array_type cell_type len) =
  let composable_cell (x y: array_type cell_type len) (i: nat{i < v_usize len}) : prop =
    let xi = Seq.index x i in
    let yi = Seq.index y i in
    base_pcm.unitless_p.unitless_composable xi yi
  in
  let composable:symrel (array_type cell_type len) =
    fun x y -> forall (i: nat{i < v_usize len}). composable_cell x y i
  in
  let compose (x: array_type cell_type len) (y: array_type cell_type len {composable x y})
      : array_type cell_type len =
    Seq.init (v_usize len)
      (fun i ->
          let xi = Seq.index x i in
          let yi = Seq.index y i in
          base_pcm.unitless_p.unitless_op xi yi)
  in
  let pcm':unitless_pcm' (array_type cell_type len) =
    { unitless_composable = composable; unitless_op = compose }
  in
  {
    unitless_p = pcm';
    unitless_comm
    =
    (fun x y ->
        let xy = pcm'.unitless_op x y in
        let yx = pcm'.unitless_op y x in
        let aux (i: nat{i < v_usize len}) : Lemma (Seq.index xy i == Seq.index yx i) =
          base_pcm.unitless_comm (Seq.index x i) (Seq.index y i)
        in
        Classical.forall_intro aux;
        assert (xy `Seq.equal` yx));
    unitless_assoc
    =
    (fun x y z ->
        let x_yz = pcm'.unitless_op x (pcm'.unitless_op y z) in
        let aux (i: nat{i < v_usize len})
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
        let aux (i: nat{i < v_usize len})
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

let pointwise_struct_pcm
      (field_types: (field_id -> Type u#a))
      (base_pcms: (field: field_id -> unitless_pcm (field_types field)))
    : unitless_pcm (struct_type field_types) =
  let composable_field (field: field_id) (x y: struct_type field_types) : prop =
    let xf = DepMap.sel x field in
    let yf = DepMap.sel y field in
    (base_pcms field).unitless_p.unitless_composable xf yf
  in
  let composable:symrel (struct_type field_types) =
    fun x y -> forall (field: field_id). composable_field field x y
  in
  let compose (x: struct_type field_types) (y: struct_type field_types {composable x y})
      : struct_type field_types =
    DepMap.create (fun field ->
          let xf = DepMap.sel x field in
          let yf = DepMap.sel y field in
          (base_pcms field).unitless_p.unitless_op xf yf)
  in
  let pcm':unitless_pcm' (struct_type field_types) =
    { unitless_composable = composable; unitless_op = compose }
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

////////////////////////////////////////////////////////////////////
// Examples
////////////////////////////////////////////////////////////////////

open Steel.PCM.FractionalPermission
open Steel.PCM.Unitless.Base

let array_with_frac_perm_on_all_indexes (t: Type u#a) (len: usize) (v: t) : array_struct u#a =
  ArrayStruct (DArray (DBase (with_perm u#a t)) len)
    (pointwise_array_pcm (with_perm t) len frac_perm_pcm)
    (Seq.init u#a (v_usize len) (fun _ -> { value = v; perm = perm_one }))

let immutable_splittable_array (t: Type u#a) (len: usize) (v: t) : array_struct u#a =
  ArrayStruct (DArray (DBase t) len)
    (pointwise_array_pcm t len immutable_unitless_pcm)
    (Seq.init u#a (v_usize len) (fun _ -> v))

let two_fields_restricted_func
      (#a: Type u#a)
      (field1: string)
      (field2: string{field2 <> field1})
      (value1 value2 by_default: a)
    : (field_id ^-> a) =
  on _
    (fun field -> if field = field1 then value1 else if field = field2 then value2 else by_default)

#push-options "--fuel 2 --ifuel 2"
let two_fields_dep_map
      (a: (field_id -> Type u#a))
      (field1: string)
      (field2: string{field2 <> field1})
      (value1: a field1)
      (value2: a field2)
      (by_default: (field: field_id{field <> field1 /\ field <> field2} -> a field))
    : (DepMap.t field_id a) =
  DepMap.create #field_id
    #a
    (fun field ->
        if field = field1 then value1 else if field = field2 then value2 else by_default field)


let point_2d:array_struct =
  let field_descriptors = two_fields_restricted_func "x" "y" (DBase int) (DBase int) (DBase unit) in
  let field_types:(field_id -> Type0) = struct_field_type field_descriptors in
  let field_pcms:(field: field_id -> unitless_pcm (field_types field)) =
    fun field ->
      if field = "x"
      then exclusive_unitless_pcm
      else if field = "y" then immutable_unitless_pcm else exclusive_unitless_pcm
  in
  struct_field_type_unroll_lemma field_descriptors;
  ArrayStruct (DStruct field_descriptors)
    (pointwise_struct_pcm field_types field_pcms)
    (two_fields_dep_map field_types "x" "y" 0 1 (fun _ -> ()))

