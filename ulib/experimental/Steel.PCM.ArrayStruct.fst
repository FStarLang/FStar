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
      | None -> Univ.raise_t u#0 u#a unit

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
      {:pattern (array_cell_sub_array_struct s0 i) \/ (array_cell_sub_array_struct s1 i)}
       composable_array_struct'
         (array_cell_sub_array_struct s0 i)
         (array_cell_sub_array_struct s1 i)
    end
  | Struct field_descriptors0, Struct field_descriptors1 ->
    field_descriptors0 == field_descriptors1 /\
    begin forall (field: field_id{Some? (field_descriptors0 field)}).
      {:pattern (struct_field_sub_array_struct s0 field) \/ (struct_field_sub_array_struct s1 field)}
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

let rec composable_symmetric (s0 s1: array_struct u#a)
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
      composable_symmetric
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
       composable_symmetric
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
      composable_symmetric s0 s1
    in
    Classical.impl_intro aux;
    let aux (_: squash (composable_array_struct' s1 s0)) : Lemma (composable_array_struct' s0 s1) =
      composable_symmetric s1 s0
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
        // Here I chose the type to be False, but how to provide a value ?
        Univ.raise_val u#0 u#a ()
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

let one_array_struct : array_struct u#a  =
  ArrayStruct u#a (Base (Univ.raise_t unit) unit_pcm) (Univ.raise_val ())

let array_struct_pcm' : pcm' u#(a+1) (array_struct u#a) = {
  composable = composable_array_struct;
  op = compose_array_struct;
  one = one_array_struct
}

open FStar.Tactics

let compose_opaque (x: array_struct u#a) (y :array_struct u#a{x `composable_array_struct` y}) =
  x `compose_array_struct` y

let struct_field_sub_array_struct_opaque
  (s: array_struct u#a{Struct? s.descriptor})
  (field: field_id{Some? ((Struct?.field_descriptors s.descriptor) field)})
  = struct_field_sub_array_struct s field


let compose_struct_field_sub_array_struct_lemma (x y : array_struct u#a) (field: field_id)
    : Lemma
      (requires (
        Struct? x.descriptor /\ x `composable_array_struct` y /\
        Some? ((Struct?.field_descriptors x.descriptor) field)
      ))
      (ensures (
         let xf = struct_field_sub_array_struct x field in
         let yf = struct_field_sub_array_struct y field in
         let xyf = struct_field_sub_array_struct (x `compose_array_struct` y) field in
         xyf == xf `compose_array_struct` yf
      ))
  =
  let xf = struct_field_sub_array_struct_opaque x field in
  let yf = struct_field_sub_array_struct_opaque y field in
  let xyf = struct_field_sub_array_struct (x `compose_array_struct` y) field in
  match x.descriptor, y.descriptor, (x `compose_array_struct` y).descriptor with
  | Struct fields, Struct fields', Struct fields'' ->
    assert(fields == fields');
    assert(fields == fields'');
    assert(xf.descriptor == Some?.v (fields field));
    assert(yf.descriptor == Some?.v (fields field));
    assert(xyf.descriptor == Some?.v (fields field));
    let xfyf = xf `compose_opaque` yf in
    assert(xyf == xfyf) by begin
      norm [delta_only ["Steel.PCM.ArrayStruct.Memory.compose_array_struct"]; zeta];
      norm [nbe; simplify; weak; hnf];
      // Here we just want the tactics engine to figure out that it can reduce the match...
      tadmit ()
    end;
    admit()
  | _ -> ()

#push-options "--z3rlimit 20"
let array_struct_assoc_l_helper
  (x: array_struct u#a{Struct? x.descriptor})
  (y: array_struct u#a)
  (z: array_struct u#a{
    y `composable_array_struct` z /\
    x `composable_array_struct` (y `compose_array_struct` z)
  })
  (field: field_id{Some? (( Struct?.field_descriptors x.descriptor) field)})
    : Lemma (requires (
      let fields = Struct?.field_descriptors x.descriptor in
      let xi = struct_field_sub_array_struct x field in
      let yi = struct_field_sub_array_struct y field in
      let zi = struct_field_sub_array_struct z field in
      composable_array_struct yi zi /\ composable_array_struct xi (yi `compose_array_struct` zi)
    ))
    (ensures (
      let fields = Struct?.field_descriptors x.descriptor in
      struct_field_type_unroll_lemma_aux u#a fields;
      let xi = struct_field_sub_array_struct x field in
      let yi = struct_field_sub_array_struct y field in
      let zi = struct_field_sub_array_struct z field in
      (xi `compose_array_struct` (yi `compose_array_struct` zi)).value ==
      FStar.DependentMap.sel
        #field_id
        #(struct_field_type (Struct?.field_descriptors x.descriptor))
        (x `compose_array_struct` (y `compose_array_struct` z)).value field
    ))
  =
  admit()


#push-options "--z3rlimit 50 --warn_error -271"
let rec arraystruct_assoc_l
  (x:array_struct u#a)
  (y:array_struct u#a)
  (z:array_struct u#a)
    : Lemma (requires (
      composable_array_struct y z /\ composable_array_struct x (y `compose_array_struct` z)
    )) (ensures (
      composable_array_struct x y /\ composable_array_struct (x `compose_array_struct` y) z /\
      x `compose_array_struct` (y `compose_array_struct` z) ==
        (x `compose_array_struct` y) `compose_array_struct` z
    )) (decreases x.descriptor)
  =
  match x.descriptor, y.descriptor, z.descriptor with
  | Base _ pcm, Base _ _, Base _ _ ->
    pcm.assoc x.value y.value z.value
  | Array a len, Array _ _, Array _ _ ->
    let aux (i:nat{i < v_usize len}) : Lemma (
      let xi = array_cell_sub_array_struct x i in
      let yi = array_cell_sub_array_struct y i in
      let zi = array_cell_sub_array_struct z i in
      composable_array_struct xi yi /\ composable_array_struct (xi `compose_array_struct` yi) zi /\
      xi `compose_array_struct` (yi `compose_array_struct` zi) ==
        (xi `compose_array_struct` yi) `compose_array_struct` zi
    ) =
      let xi = array_cell_sub_array_struct x i in
      let yi = array_cell_sub_array_struct y i in
      let zi = array_cell_sub_array_struct z i in
      arraystruct_assoc_l xi yi zi
    in
    Classical.forall_intro aux;
    let yz = y `compose_array_struct` z in
    let xy = x `compose_array_struct` y in
    assert(
      (x `compose_array_struct` yz).value `Seq.equal #(array_struct_type a)`
      (xy `compose_array_struct` z).value
    )
  | Struct fields, Struct _, Struct _ ->
      let aux_helper (x y: array_struct u#a) (field: field_id)
        : Lemma
          (requires (
            Struct? x.descriptor /\ x `composable_array_struct` y /\
            Some? ((Struct?.field_descriptors x.descriptor) field)
          ))
          (ensures (
             let xf = struct_field_sub_array_struct x field in
             let yf = struct_field_sub_array_struct y field in
             let xyf = struct_field_sub_array_struct (x `compose_array_struct` y) field in
             xyf == xf `compose_array_struct` yf
          )) [SMTPat ()]
      =
      compose_struct_field_sub_array_struct_lemma x y field
    in
    let aux1 (field: field_id{Some? (fields field)}) : Lemma (
      let xi = struct_field_sub_array_struct x field in
      let yi = struct_field_sub_array_struct y field in
      let zi = struct_field_sub_array_struct z field in
      composable_array_struct xi yi /\ composable_array_struct (xi `compose_array_struct` yi) zi /\
      xi `compose_array_struct` (yi `compose_array_struct` zi) ==
        (xi `compose_array_struct` yi) `compose_array_struct` zi
    ) [SMTPat ()] =
      let xi = struct_field_sub_array_struct x field in
      let yi = struct_field_sub_array_struct y field in
      let zi = struct_field_sub_array_struct z field in
      let yzi = struct_field_sub_array_struct (y `compose_array_struct` z) field in
      arraystruct_assoc_l xi yi zi
    in
    assert(composable_array_struct x y);
    assert(composable_array_struct (x `compose_array_struct` y) z);
    struct_field_type_unroll_lemma_aux u#a fields;
    let aux2 (field: field_id) : Lemma (
      FStar.DependentMap.sel #field_id #(struct_field_type fields)
        (x `compose_array_struct` (y `compose_array_struct` z)).value field ==
      FStar.DependentMap.sel #field_id #(struct_field_type fields)
        ((x `compose_array_struct` y) `compose_array_struct` z).value field
    ) =
      let v1 =
        FStar.DependentMap.sel #field_id #(struct_field_type fields)
          (x `compose_array_struct` (y `compose_array_struct` z)).value field
      in
      let v2 =
        FStar.DependentMap.sel #field_id #(struct_field_type fields)
          ((x `compose_array_struct` y) `compose_array_struct` z).value field
      in
      match
        fields field
      with
      | None ->
        assert((struct_field_type fields) field == Univ.raise_t u#0 u#a unit);
        higher_unit u#a v1; higher_unit u#a v2
      | Some descr ->
        assert((struct_field_type fields) field == array_struct_type descr);
        aux1 field;
        let xi = struct_field_sub_array_struct x field in
        let yi = struct_field_sub_array_struct y field in
        let zi = struct_field_sub_array_struct z field in
        array_struct_assoc_l_helper x y z field;
        // DM 04/21/2020: Why are these assumes still needed?
        assume((xi `compose_array_struct` (yi `compose_array_struct` zi)).value == v1);
        assume(((xi `compose_array_struct` yi) `compose_array_struct` zi).value == v2)
    in
    Classical.forall_intro aux2;
    assert(
      (x `compose_array_struct` (y `compose_array_struct` z)).value
        `FStar.DependentMap.equal #field_id #(struct_field_type fields)`
          ((x `compose_array_struct` y) `compose_array_struct` z).value
    )
