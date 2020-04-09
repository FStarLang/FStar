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

#set-options "--fuel 1 --ifuel 1"

type field_id = string

noeq type array_struct_descriptor : Type u#(a+1) =
  // You can store your own funky PCM in the Base case
  | Base: a: Type u#a -> pcm: pcm a -> array_struct_descriptor
  | Array: cell_descriptor:array_struct_descriptor u#a -> len:usize -> array_struct_descriptor
  | Struct: field_descriptors: (field_id ^-> option (array_struct_descriptor u#a)) ->
    array_struct_descriptor
  // Missing: untagged unions (not must have)

unfold let struct_field_type'
  (field_descriptors: (field_id ^-> option (array_struct_descriptor u#a)))
  (array_struct_type: (descriptor: array_struct_descriptor u#a{
    descriptor << field_descriptors
  }) -> Tot (Type u#a))
  (field: field_id)
  : Tot (Type u#a) =
  match field_descriptors field with
      | Some descr ->
        FStar.WellFounded.axiom1 field_descriptors field;
        array_struct_type descr
      | None -> Univ.raise_t u#0 u#a False

let rec array_struct_type (descriptor: array_struct_descriptor u#a) : Tot (Type u#a) (decreases descriptor) =
  match descriptor with
  | Base a pcm -> a
  | Array descriptor' len ->
    let typ' = array_struct_type descriptor' in
    Seq.lseq u#a typ' (v_usize len)
  | Struct field_descriptors ->
    DepMap.t field_id (struct_field_type' field_descriptors array_struct_type)

unfold let struct_field_type
  (field_descriptors: (field_id ^-> option (array_struct_descriptor u#a)))
  (field: field_id)
  : Tot (Type u#a) =
  struct_field_type' field_descriptors array_struct_type field

noeq type array_struct : Type u#(a+1) =
  | ArrayStruct:
    descriptor: array_struct_descriptor u#a ->
    value:(array_struct_type  descriptor) -> array_struct

let struct_field_type_unroll_lemma_aux
  (field_descriptors : (field_id ^-> option (array_struct_descriptor u#a)))
    : Lemma (
      DependentMap.t u#a field_id (struct_field_type u#a field_descriptors) ==
      array_struct_type u#a (Struct u#a field_descriptors)
     )
  =
  let open FStar.Tactics in
  assert (
    DependentMap.t field_id (struct_field_type field_descriptors) ==
    array_struct_type (Struct field_descriptors)
  ) by begin
    compute ()
  end

let struct_field_type_unroll_lemma
  (s: array_struct u#a{Struct? s.descriptor})
  : Lemma (
    DependentMap.t u#a field_id (struct_field_type u#a (Struct?.field_descriptors s.descriptor))
    ==
    array_struct_type u#a s.descriptor
  )
  =
  struct_field_type_unroll_lemma_aux (Struct?.field_descriptors s.descriptor)

let array_cell_type_unroll_lemma_aux
  (cell_descriptor : array_struct_descriptor u#a)
  (len: usize)
    : Lemma (
      Seq.lseq (array_struct_type cell_descriptor) (v_usize len) ==
      array_struct_type u#a (Array u#a cell_descriptor len)
     )
  =
  let open FStar.Tactics in
  assert (
     Seq.lseq (array_struct_type cell_descriptor) (v_usize len) ==
      array_struct_type u#a (Array u#a cell_descriptor len)
  ) by begin
    compute ()
  end

let array_cell_type_unroll_lemma
  (s: array_struct u#a{Array? s.descriptor})
    : Lemma (
      Seq.lseq
        (array_struct_type (Array?.cell_descriptor s.descriptor))
        (v_usize (Array?.len s.descriptor)) ==
      array_struct_type u#a s.descriptor
     )
  =
  array_cell_type_unroll_lemma_aux
    (Array?.cell_descriptor s.descriptor)
    (Array?.len s.descriptor)


let array_cell_sub_array_struct
  (s: array_struct u#a{Array? s.descriptor})
  (i:nat{i < v_usize (Array?.len s.descriptor)})
  : Tot (s':array_struct u#a{s'.descriptor << s.descriptor})
  =
  let cell_descriptor = Array?.cell_descriptor s.descriptor in
  let len = Array?.len s.descriptor in
  array_cell_type_unroll_lemma s;
  let v: Seq.lseq u#a (array_struct_type u#a cell_descriptor) (v_usize len) = s.value in
  let sub_v = Seq.index u#a v i in
  ArrayStruct u#a cell_descriptor sub_v

let struct_field_sub_array_struct
  (s: array_struct u#a{Struct? s.descriptor})
  (field: field_id{Some? ((Struct?.field_descriptors s.descriptor) field)})
  : Tot (s':array_struct u#a{s'.descriptor << s.descriptor})
  =
  let field_descriptors = Struct?.field_descriptors s.descriptor in
  let Some sub_descriptor = field_descriptors field in
  struct_field_type_unroll_lemma u#a s;
  let sub_v = DepMap.sel u#a #_ #(struct_field_type field_descriptors) s.value field in
  FStar.WellFounded.axiom1 field_descriptors field;
  ArrayStruct sub_descriptor sub_v

let rec composable_array_struct' (s0 s1: array_struct u#a) : Tot prop (decreases s0.descriptor) =
  match s0.descriptor, s1.descriptor with
  | Base a0 pcm0, Base a1 pcm1 ->
    a0 == a1 /\ pcm0 == pcm1 /\
    composable pcm0 s0.value s1.value
  | Array descriptor0 len0, Array descriptor1 len1 ->
    descriptor0 == descriptor1 /\ len0 == len1 /\
    begin forall (i:nat{i < v_usize len0}).
       composable_array_struct'
         (array_cell_sub_array_struct s0 i)
         (array_cell_sub_array_struct s1 i)
    end
  | Struct field_descriptors0, Struct field_descriptors1 ->
    field_descriptors0 == field_descriptors1 /\
    begin forall (field: field_id{Some? (field_descriptors0 field)}).
      composable_array_struct'
        (struct_field_sub_array_struct s0 field)
        (struct_field_sub_array_struct s1 field)
    end
  | _ -> False


let composable_array_struct_struct_case_intro
  (s0: array_struct u#a{Struct? s0.descriptor})
  (s1: array_struct u#a {Struct? s1.descriptor /\
    Struct?.field_descriptors s0.descriptor == Struct?.field_descriptors s1.descriptor
  })
  (lemma: (field: field_id{Some? ((Struct?.field_descriptors s0.descriptor) field)}) -> Lemma (
      composable_array_struct'
        (struct_field_sub_array_struct s0 field)
        (struct_field_sub_array_struct s1 field)
  ))
    : Lemma (composable_array_struct' s0 s1)
  =
  struct_field_type_unroll_lemma u#a s0;
  struct_field_type_unroll_lemma u#a s1;
  Classical.forall_intro lemma

let composable_array_struct_struct_case_elim
  (s0: array_struct{Struct? s0.descriptor})
  (s1: array_struct{Struct? s1.descriptor /\ composable_array_struct' s0 s1})
  (field: field_id{Some? ((Struct?.field_descriptors s0.descriptor) field)})
    : Lemma (
      Struct?.field_descriptors s0.descriptor == Struct?.field_descriptors s1.descriptor /\
      composable_array_struct'
        (struct_field_sub_array_struct s0 field)
        (struct_field_sub_array_struct s1 field)
    )
  =
  ()

let rec composable_sym (s0 s1: array_struct u#a)
    : Lemma
      (requires composable_array_struct' s0 s1)
      (ensures composable_array_struct' s1 s0)
      (decreases s0.descriptor)
  =
  match s0.descriptor, s1.descriptor with
  | Base a0 pcm0, Base a1 pcm1 ->
    ()
  | Array descriptor0 len0, Array descriptor1 len1 ->
    let aux (i:nat{i < v_usize len0}) : Lemma (
       composable_array_struct'
         (array_cell_sub_array_struct s1 i)
         (array_cell_sub_array_struct s0 i)
    ) =
      composable_sym
        (array_cell_sub_array_struct s0 i)
        (array_cell_sub_array_struct s1 i)
    in
    Classical.forall_intro aux
  | Struct field_descriptors0, Struct field_descriptors1 ->
    let aux (field: field_id{Some? (field_descriptors0 field)}) : Lemma (
       composable_array_struct'
         (struct_field_sub_array_struct s1 field)
         (struct_field_sub_array_struct s0 field)
    ) =
       composable_sym
         (struct_field_sub_array_struct s0 field)
         (struct_field_sub_array_struct s1 field)
    in
    Classical.forall_intro aux
  | _ -> ()


unfold let composable_array_struct : symrel array_struct =
  let aux (s0 s1: array_struct) : Lemma (
    composable_array_struct' s0 s1 <==> composable_array_struct' s1 s0
  ) =
    let aux (_: squash (composable_array_struct' s0 s1)) : Lemma (composable_array_struct' s1 s0) =
      composable_sym s0 s1
    in
    Classical.impl_intro aux;
    let aux (_: squash (composable_array_struct' s1 s0)) : Lemma (composable_array_struct' s0 s1) =
      composable_sym s1 s0
    in
    Classical.impl_intro aux
  in
  Classical.forall_intro_2 aux;
  composable_array_struct'
#set-options "--print_universes"

let rec compose_array_struct
  (s0 : array_struct u#a)
  (s1: array_struct u#a{s0 `composable_array_struct` s1})
    : Tot (s':array_struct u#a{s'.descriptor == s0.descriptor})
      (decreases s0.descriptor)
  =

  match s0.descriptor, s1.descriptor with
  | Base a0 pcm0, Base a1 pcm1 ->
    ArrayStruct s0.descriptor (op pcm0 s0.value s1.value)
  | Array descriptor0 len0, Array descriptor1 len1 ->
    let new_val : Seq.lseq u#a (array_struct_type u#a descriptor0) (v_usize len0) =
      Seq.init (v_usize len0) (fun i ->
        let new_sub_array_struct : array_struct u#a =
          compose_array_struct
            (array_cell_sub_array_struct s0 i)
            (array_cell_sub_array_struct s1 i)
        in
        let cell_val : array_struct_type u#a descriptor0 = new_sub_array_struct.value in
        cell_val
      )
    in
    ArrayStruct s0.descriptor new_val
  | Struct field_descriptors0, Struct field_descriptors1 ->
    let aux (field: field_id) : Tot (struct_field_type field_descriptors0 field) =
      match field_descriptors0 field, field_descriptors1 field with
      | None, None ->
        assert(struct_field_type field_descriptors0 field == Univ.raise_t u#0 u#a False);
        // Here I chose the type to be False, but how to provide a value ?
        magic()
      | Some sub_descriptor0, Some sub_descriptor1 ->
        let new_sub_array_struct : array_struct u#a =
          compose_array_struct
            (struct_field_sub_array_struct s0 field)
            (struct_field_sub_array_struct s1 field)
        in
        let cell_val : struct_field_type u#a field_descriptors0 field =
          new_sub_array_struct.value
        in
        cell_val
    in
    struct_field_type_unroll_lemma_aux u#a field_descriptors0;
    let new_val : array_struct_type u#a s0.descriptor =
      DepMap.create #_ #(struct_field_type field_descriptors0) aux
    in
    ArrayStruct s0.descriptor new_val

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
