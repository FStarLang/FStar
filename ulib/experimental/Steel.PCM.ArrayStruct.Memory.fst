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

let struct_field_type'
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

let struct_field_type
  (field_descriptors: (field_id ^-> option (array_struct_descriptor u#a)))
  (field: field_id)
  : Tot (Type u#a) =
  struct_field_type' field_descriptors array_struct_type field

noeq type array_struct : Type u#(a+1) =
  | ArrayStruct:
    descriptor: array_struct_descriptor u#a ->
    value:(array_struct_type  descriptor) -> array_struct

let struct_field_type_unroll_lemma
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

let composable_array_cell'
  (cell_descriptor: array_struct_descriptor u#a)
  (len : usize)
  (i:nat{i < v_usize len})
  (v0 v1: array_struct_type u#a (Array u#a cell_descriptor len))
  (composable_array_struct':
    (s0: array_struct{s0.descriptor << Array cell_descriptor len}) ->
    (s1: array_struct) -> Tot prop
  )
  : Tot prop
  =
  let v0: Seq.lseq u#a (array_struct_type u#a cell_descriptor) (v_usize len) = v0 in
  let sub_v0 = Seq.index u#a v0 i in
  let v1: Seq.lseq u#a (array_struct_type u#a cell_descriptor) (v_usize len) = v1 in
  let sub_v1 = Seq.index u#a v1 i in
  let sub_s0 = ArrayStruct u#a cell_descriptor sub_v0 in
  let sub_s1 = ArrayStruct u#a cell_descriptor sub_v1 in
  composable_array_struct' sub_s0 sub_s1

let composable_struct_field''
  (s: array_struct u#a{Struct? s.descriptor})
  (field: field_id)
  (v0 v1: array_struct_type u#a s.descriptor)
  (composable_array_struct':
    (s0: array_struct u#a{s0.descriptor << s.descriptor}) ->
    (s1: array_struct u#a) -> Tot prop
  )
  : Tot prop
  =
  let Struct field_descriptors = s.descriptor in
  match field_descriptors field with
  | Some sub_descriptor ->
    struct_field_type_unroll_lemma field_descriptors;
    let v0 : DependentMap.t field_id (struct_field_type field_descriptors) = v0 in
    let sub_v0 = DepMap.sel #_ #(struct_field_type field_descriptors) v0 field in
    let v1 : DependentMap.t field_id (struct_field_type field_descriptors) = v1 in
    let sub_v1 = DepMap.sel #_ #(struct_field_type field_descriptors) v1 field in
    let sub_s0 = ArrayStruct sub_descriptor sub_v0 in
    let sub_s1 = ArrayStruct sub_descriptor sub_v1 in
    FStar.WellFounded.axiom1 field_descriptors field;
    composable_array_struct' sub_s0 sub_s1
  | None -> True

// The last function needed the whole array struct to be fed in for some reason, but
// we prefer the later signature
let composable_struct_field'
  (field_descriptors: field_id ^-> option (array_struct_descriptor u#a))
  (field: field_id)
  (v0 v1: array_struct_type u#a (Struct field_descriptors))
  (composable_array_struct':
    (s0: array_struct u#a{s0.descriptor << Struct field_descriptors}) ->
    (s1: array_struct u#a) -> Tot prop
  )
  : Tot prop
  =
  composable_struct_field''
    (ArrayStruct (Struct field_descriptors) v0)
    field
    v0
    v1
    composable_array_struct'

let rec composable_array_struct' (s0 s1: array_struct u#a) : Tot prop (decreases s0.descriptor) =
  match s0.descriptor, s1.descriptor with
  | Base a0 pcm0, Base a1 pcm1 ->
    a0 == a1 /\ pcm0 == pcm1 /\
    composable pcm0 s0.value s1.value
  | Array descriptor0 len0, Array descriptor1 len1 ->
    descriptor0 == descriptor1 /\ len0 == len1 /\
    begin forall (i:nat{i < v_usize len0}).
      composable_array_cell' descriptor0 len0 i s0.value s1.value
        (fun s0 s1 -> composable_array_struct' s0 s1)
        // We need the eta-expansion here to convince F* of recursive termination
    end
  | Struct field_descriptors0, Struct field_descriptors1 ->
    field_descriptors0 == field_descriptors1 /\
    begin forall (field: field_id).
      composable_struct_field' field_descriptors0 field s0.value s1.value
       (fun s0 s1 -> composable_array_struct' s0 s1)
    end
  | _ -> False

let composable_array_cell
  (cell_descriptor: array_struct_descriptor u#a)
  (len : usize)
  (i:nat{i < v_usize len})
  (v0 v1: array_struct_type u#a (Array cell_descriptor len))
  : Tot prop
  =
  composable_array_cell' cell_descriptor len i v0 v1
    (fun s0 s1 -> composable_array_struct' u#a s0 s1)

let composable_struct_field
  (field_descriptors: field_id ^-> option (array_struct_descriptor u#a))
  (field: field_id)
  (v0 v1: array_struct_type u#a (Struct field_descriptors))
  : Tot prop
  =
  composable_struct_field' field_descriptors field v0 v1
    (fun s0 s1 -> composable_array_struct' u#a s0 s1)

#push-options "--warn_error -271"
let rec composable_sym (s0 s1: array_struct u#a)
    : Lemma
      (requires True)
      (ensures (composable_array_struct' s0 s1 ==> composable_array_struct' s1 s0))
      (decreases s0.descriptor)
  =
  match s0.descriptor, s1.descriptor with
  | Base a0 pcm0, Base a1 pcm1 ->
    ()
  | Array descriptor0 len0, Array descriptor1 len1 ->
    let aux
      (_ : squash (composable_array_struct' s0 s1))
        : Lemma (composable_array_struct' s1 s0)
      =
      let aux (i:nat{i < v_usize len0}) : Lemma (
        composable_array_cell descriptor1 len1 i s1.value s0.value
      ) =
        assert(descriptor0 == descriptor1 /\ len0 == len1);
        // This should be implied by (composable_array_struct' s0 s1)
        assume(composable_array_cell descriptor0 len0 i s0.value s1.value);
        let v0: Seq.lseq u#a (array_struct_type u#a descriptor0) (v_usize len0) = s0.value in
        let sub_v0 = Seq.index u#a v0 i in
        let v1: Seq.lseq u#a (array_struct_type u#a descriptor1) (v_usize len1) = s1.value in
        let sub_v1 = Seq.index u#a v1 i in
        let sub_s0 = ArrayStruct u#a descriptor0 sub_v0 in
        let sub_s1 = ArrayStruct u#a descriptor1 sub_v1 in
        composable_sym sub_s0 sub_s1
      in
      Classical.forall_intro aux;
      assert(descriptor1 == descriptor0 /\ len1 == len0 /\ (forall (i:nat{i < v_usize len1}).
         composable_array_cell descriptor1 len1 i s1.value s0.value
      ));
      // This should also go through but problem because of the recursive function
      admit()
    in
    Classical.impl_intro aux
  | Struct field_descriptors0, Struct field_descriptors1 ->
    assume(composable_array_struct' s0 s1 ==> composable_array_struct' s1 s0)
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
        admit();
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
