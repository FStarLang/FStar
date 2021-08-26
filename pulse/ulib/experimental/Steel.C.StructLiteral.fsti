module Steel.C.StructLiteral

#set-options "--z3rlimit 50"

open Steel.Memory
open Steel.Effect
open Steel.Effect.Common
open Steel.Effect.Atomic

open Steel.C.PCM
open Steel.C.Struct
open Steel.C.Typedef
open Steel.C.Ref
open Steel.C.Connection
open Steel.C.Opt
open Steel.C.Fields

open FStar.List.Tot
open FStar.FunctionalExtensionality
open FStar.FSet

module TS = Steel.C.Typestring

val mk_struct_def (tag: Type0) (field_descriptions: Type0): Type0

(** To declare a struct definition, one needs to write
      let _ = norm norm_c_typedef (mk_c_struct <struct_tag> <struct_fields>).
    This normalizes to a type (mk_struct_def t fs), where
      t is an embedding of the struct tag name as a Type0 (see Steel.C.Typestring), and
      fs is an embedding of the struct fields as a Type0
    Kremlin then parses this embedding and emits a C struct definition. *)
let mk_c_struct (tag: Type0) (fields: c_fields) =
  mk_struct_def tag (c_fields_t fields)

(** When we take a pointer &p->foo, p loses access to field foo.
    To record this fact, we explcitly track the set of excluded fields. *)
let excluded_fields = s:set string{s "" == false}

(** A [struct' tag fields excluded] is a view type for C structs with
    tag [tag], fields [fields], and excluded fields [excluded]. *)
val struct' (tag: Type0) (fields: c_fields) (excluded: excluded_fields): Type0

(** A [struct tag fields] is a view type for C structs with tag [tag] and fields [fields]. *)
inline_for_extraction
let struct (tag: Type0) (fields: c_fields) = struct' tag fields emptyset

(** Combinators for constructing struct literals *)

val mk_nil (tag: Type0): struct tag fields_nil

val mk_cons (tag: Type0) (fields: c_fields)
  (field: field_t) (td: typedef) (x: td.view_type) (v: struct tag fields)
: Pure (struct tag (fields_cons field td fields))
    (requires fields.has_field field == false)
    (ensures fun _ -> True)

(** [struct_pcm_carrier tag fields] is the carrier of the PCM which
    models structs with tag [tag] and fields [fields]. *)
val struct_pcm_carrier (tag: Type0) (fields: c_fields): Type0

(** [struct_pcm] is the PCM that models structs with tag [tag] and fields [fields]. *)
val struct_pcm (tag: Type0) (fields: c_fields): pcm (struct_pcm_carrier tag fields)

/// Reading a struct field
val struct_get
  (#tag: Type0) (#fields: c_fields) (#excluded: excluded_fields)
  (x: struct' tag fields excluded) (field: field_of fields)
: Pure (fields.get_field field).view_type
    (requires excluded field == false)
    (ensures fun _ -> True)

/// Writing a struct field
val struct_put
  (#tag: Type0) (#fields: c_fields) (#excluded: excluded_fields)
  (x: struct' tag fields excluded)
  (field: field_of fields)
  (v: (fields.get_field field).view_type)
: Pure (struct' tag fields excluded)
    (requires excluded field == false)
    (ensures fun _ -> True)

/// For a fixed field name, struct_get and struct_put form a lens

val struct_get_put 
  (#tag: Type0) (#fields: c_fields) (#excluded: excluded_fields)
  (x: struct' tag fields excluded)
  (field: field_of fields)
  (v: (fields.get_field field).view_type)
: Lemma
    (requires excluded field == false)
    (ensures struct_put x field v `struct_get` field == v)
  [SMTPat (struct_put x field v `struct_get` field)]

val struct_put_get
  (#tag: Type0) (#fields: c_fields) (#excluded: excluded_fields)
  (x: struct' tag fields excluded)
  (field: field_of fields)
: Lemma
    (requires excluded field == false)
    (ensures struct_put x field (x `struct_get` field) == x)
  [SMTPat (struct_put x field (x `struct_get` field))]

val struct_put_put
  (#tag: Type0) (#fields: c_fields)
  (x: struct tag fields)
  (field: field_of fields)
  (v w: (fields.get_field field).view_type)
: Lemma (struct_put (struct_put x field v) field w == struct_put x field w)
  [SMTPat (struct_put (struct_put x field v) field w)]

/// struct_get/struct_put pairs for different fields don't interfere with each other

val struct_get_put_ne
  (#tag: Type0) (#fields: c_fields) (#excluded: excluded_fields)
  (x: struct' tag fields excluded)
  (field1: field_of fields)
  (field2: field_of fields)
  (v: (fields.get_field field1).view_type)
: Lemma
    (requires field1 =!= field2 /\ excluded field1 == false /\ excluded field2 == false)
    (ensures struct_put x field1 v `struct_get` field2 == x `struct_get` field2)
  [SMTPat (struct_put x field1 v `struct_get` field2)]
  
val struct_put_put_ne
  (#tag: Type0) (#fields: c_fields) (#excluded: excluded_fields)
  (x: struct' tag fields excluded)
  (field1: field_of fields)
  (v: (fields.get_field field1).view_type)
  (field2: field_of fields)
  (w: (fields.get_field field2).view_type)
: Lemma
    (requires field1 =!= field2 /\ excluded field1 == false /\ excluded field2 == false)
    (ensures
      struct_put (struct_put x field1 v) field2 w ==
      struct_put (struct_put x field2 w) field1 v)

let struct_pcm_one (tag: Type0) (fields: c_fields)
: struct_pcm_carrier tag fields
= one (struct_pcm tag fields)

/// Reading a pcm_struct_carrier field
val struct_pcm_get
  (#tag: Type0) (#fields: c_fields)
  (x: struct_pcm_carrier tag fields) (field: field_of fields)
: (fields.get_field field).carrier

/// Writing a struct_pcm_carrier field
val struct_pcm_put
  (#tag: Type0) (#fields: c_fields)
  (x: struct_pcm_carrier tag fields)
  (field: field_of fields)
  (v: (fields.get_field field).carrier)
: struct_pcm_carrier tag fields

/// For a fixed field name, struct_pcm_get and struct_pcm_put form a lens

val struct_pcm_get_put 
  (#tag: Type0) (#fields: c_fields)
  (x: struct_pcm_carrier tag fields)
  (field: field_of fields)
  (v: (fields.get_field field).carrier)
: Lemma (struct_pcm_put x field v `struct_pcm_get` field == v)
  [SMTPat (struct_pcm_put x field v `struct_pcm_get` field)]

val struct_pcm_put_get
  (#tag: Type0) (#fields: c_fields)
  (x: struct_pcm_carrier tag fields)
  (field: field_of fields)
: Lemma (struct_pcm_put x field (x `struct_pcm_get` field) == x)
  [SMTPat (struct_pcm_put x field (x `struct_pcm_get` field))]

val struct_pcm_put_put
  (#tag: Type0) (#fields: c_fields)
  (x: struct_pcm_carrier tag fields)
  (field: field_of fields)
  (v w: (fields.get_field field).carrier)
: Lemma (struct_pcm_put (struct_pcm_put x field v) field w == struct_pcm_put x field w)
  [SMTPat (struct_pcm_put (struct_pcm_put x field v) field w)]
  
/// struct_pcm_get/struct_pcm_put pairs for different fields don't interfere with each other

val struct_pcm_get_put_ne
  (#tag: Type0) (#fields: c_fields)
  (x: struct_pcm_carrier tag fields)
  (field1: field_of fields)
  (field2: field_of fields)
  (v: (fields.get_field field1).carrier)
: Lemma
    (requires field1 =!= field2)
    (ensures struct_pcm_put x field1 v `struct_pcm_get` field2 == x `struct_pcm_get` field2)
  [SMTPat (struct_pcm_put x field1 v `struct_pcm_get` field2)]
  
val struct_pcm_put_put_ne
  (#tag: Type0) (#fields: c_fields)
  (x: struct_pcm_carrier tag fields)
  (field1: field_of fields)
  (v: (fields.get_field field1).carrier)
  (field2: field_of fields)
  (w: (fields.get_field field2).carrier)
: Lemma
    (requires field1 =!= field2)
    (ensures
      struct_pcm_put (struct_pcm_put x field1 v) field2 w ==
      struct_pcm_put (struct_pcm_put x field2 w) field1 v)

val struct_view (tag: Type0) (fields: c_fields) (excluded: excluded_fields)
: sel_view (struct_pcm tag fields) (struct' tag fields excluded) false

val struct_is_unit (tag: Type0) (fields: c_fields)
  (v: struct_pcm_carrier tag fields)
: b:bool{b <==> v == one (struct_pcm tag fields)}

[@@c_typedef]
let typedef_struct (tag: Type0) (fields: c_fields): typedef = {
  carrier = struct_pcm_carrier tag fields;
  pcm = struct_pcm tag fields;
  view_type = struct tag fields;
  view = struct_view tag fields emptyset;
  is_unit = struct_is_unit tag fields;
}

(** A connection from a struct to any of its fields *)
val struct_field
  (tag: Type0) (fields: c_fields) (field: field_of fields)
: connection (struct_pcm tag fields) (fields.get_field field).pcm

(** extract_field tag fields excluded field v = (v without field field, v.field) *)
val extract_field
  (tag: Type0) (fields: c_fields) (excluded: excluded_fields)
  (field: field_of fields)
  (v: struct' tag fields excluded)
: Pure (struct' tag fields (insert field excluded) & (fields.get_field field).view_type)
    (requires not (excluded field))
    (ensures fun _ -> True)
    
val extract_field_extracted
  (tag: Type0) (fields: c_fields) (excluded: excluded_fields)
  (field: field_of fields)
  (v: struct' tag fields excluded)
: Lemma
    (requires not (excluded field))
    (ensures snd (extract_field tag fields excluded field v) == v `struct_get` field)
    [SMTPat (extract_field tag fields excluded field v)]

val extract_field_unextracted
  (tag: Type0) (fields: c_fields) (excluded: excluded_fields)
  (field: field_of fields)
  (field': field_of fields)
  (v: struct' tag fields excluded)
: Lemma
    (requires not (excluded field) /\ not (excluded field') /\ (field =!= field'))
    (ensures 
      not (excluded field) /\ not (excluded field') /\ (field =!= field') /\
      fst (extract_field tag fields excluded field v) `struct_get` field'
      == v `struct_get` field')
//    [SMTPat (extract_field tag fields excluded field v);
//     SMTPat (has_type field' string)]
     
val extract_field_unextracted'
  (tag: Type0) (fields: c_fields) (excluded: excluded_fields)
  (field: field_of fields)
  (v: struct' tag fields excluded)
:  Lemma (forall (field': field_of fields).
    (not (excluded field) /\ not (excluded field') /\ (field =!= field')) ==>
    (fst (extract_field tag fields excluded field v) `struct_get` field' == v `struct_get` field'))
    [SMTPat (extract_field tag fields excluded field v)]

val addr_of_struct_field_ref
  (#tag: Type0) (#fields: c_fields) (#excluded: excluded_fields)
  (field: field_of fields)
  (p: ref 'a (struct_pcm tag fields))
: Steel (ref 'a (fields.get_field field).pcm)
    (p `pts_to_view` struct_view tag fields excluded)
    (fun q ->
      (p `pts_to_view` struct_view tag fields (insert field excluded)) `star`
      (pts_to_view u#0
                  #'a
                  #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).carrier))
                  #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).pcm))
                  q
                  #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).view_type))
                  #false
                  (norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).view))))
    (requires fun _ -> not (excluded field))
    (ensures fun h q h' -> 
      not (excluded field) /\
      q == ref_focus p (struct_field tag fields field) /\
      fst (extract_field tag fields excluded field
        (h (p `pts_to_view` struct_view tag fields excluded)))
        == h' (p `pts_to_view` struct_view tag fields (insert field excluded)) /\
      snd (extract_field tag fields excluded field
        (h (p `pts_to_view` struct_view tag fields excluded)))
        == h' (q `pts_to_view` (fields.get_field field).view))

val unaddr_of_struct_field_ref'
  (#tag: Type0) (#fields: c_fields) (#excluded: excluded_fields)
  (field: field_of fields)
  (p: ref 'a (struct_pcm tag fields))
  (q: ref 'a (fields.get_field field).pcm)
: Steel unit
    ((p `pts_to_view` struct_view tag fields excluded) `star`
     (q `pts_to_view` (fields.get_field field).view))
    (fun _ -> p `pts_to_view` struct_view tag fields (remove field excluded))
    (requires fun _ ->
      excluded field == true /\
      q == ref_focus p (struct_field tag fields field))
    (ensures fun h _ h' -> 
      excluded field == true /\
      fst (extract_field tag fields (remove field excluded) field
        (h' (p `pts_to_view` struct_view tag fields (remove field excluded))))
       ==
        h (p `pts_to_view` struct_view tag fields excluded) /\
      snd (extract_field tag fields (remove field excluded) field
        (h' (p `pts_to_view` struct_view tag fields (remove field excluded))))
       ==
         h (q `pts_to_view` (fields.get_field field).view))

#restart-solver

val dummy_def : unit

val unaddr_of_struct_field_ref
  (#tag: Type0) (#fields: c_fields) (#excluded: excluded_fields)
  (field: field_of fields)
  (p: ref 'a (struct_pcm tag fields))
  (q: ref 'a (fields.get_field field).pcm)
: Steel unit
    ((p `pts_to_view` struct_view tag fields excluded) `star`
     (pts_to_view u#0
                  #'a
                  #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).carrier))
                  #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).pcm))
                  q
                  #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).view_type))
                  #false
                  (norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).view))))
    (fun _ -> p `pts_to_view` struct_view tag fields (remove field excluded))
    (requires fun _ ->
      excluded field == true /\
      q == ref_focus p (struct_field tag fields field))
    (ensures fun h _ h' -> 
      excluded field == true /\
      fst 
        (extract_field tag fields (remove field excluded) field
          (h' (p `pts_to_view` struct_view tag fields (remove field excluded))))
       == h (p `pts_to_view` struct_view tag fields excluded) /\
      snd 
        (extract_field tag fields (remove field excluded) field
          (h' (p `pts_to_view` struct_view tag fields (remove field excluded))))
      == h (q `pts_to_view` (fields.get_field field).view))

open Steel.C.Reference

(* TODO make abstract *)
let addr_of_struct_field''
  (return_view_type: Type0)
  (return_carrier: Type0)
  (tag: Type0) (fields: c_fields) (excluded: excluded_fields)
  (field: field_of fields{
    return_view_type == (fields.get_field field).view_type /\
    return_carrier == (fields.get_field field).carrier})
  (p: ref 'a (struct tag fields) (struct_pcm tag fields))
: Steel (ref 'a return_view_type #return_carrier (fields.get_field field).pcm)
    (p `pts_to_view` struct_view tag fields excluded)
    (fun q ->
      (p `pts_to_view` struct_view tag fields (insert field excluded)) `star`
      (pts_to_view u#0
                  #'a
                  #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).view_type))
                  #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).view_type))
                  #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).carrier))
                  #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).pcm))
                  q
                  (norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).view))))
    (requires fun _ -> not (excluded field))
    (ensures fun h q h' -> 
      not (excluded field) /\
      q == Steel.C.Ref.ref_focus p (struct_field tag fields field) /\
      fst (extract_field tag fields excluded field
        (h (p `pts_to_view` struct_view tag fields excluded)))
       ==
        h' (p `pts_to_view` struct_view tag fields (insert field excluded))
        /\
        snd (extract_field tag fields excluded field
        (h (p `pts_to_view` struct_view tag fields excluded))) ==
         h' (q `pts_to_view` (fields.get_field field).view))
= addr_of_struct_field_ref #'a #tag #fields #excluded field p

(** Take the address of a field of a struct.
    The above definitions are set up so that calls to addr_of_struct_field are erased to calls to addr_of_struct_field'' with
      (fields.get_field field).view_type
    and
      (fields.get_field field).carrier
    fully normalized. This allows the extracted OCaml code to be
    ML-typable, avoiding Obj.magic and the insertion of spurious casts
    in the extracted C.

    Calls to [norm] are used to compute the type of values pointed to
    by the returned reference, and to ensure that the Steel tactic
    will be able to unify vprops properly. *)
inline_for_extraction noextract
let addr_of_struct_field
  (#tag: Type0) (#fields: c_fields) (#excluded: excluded_fields)
  (field: field_of fields)
  (p: ref 'a (struct tag fields) (struct_pcm tag fields))
: Steel (ref 'a
          (norm simplify_typedefs (fields.get_field field).view_type)
          #(norm simplify_typedefs (fields.get_field field).carrier)
          (fields.get_field field).pcm)
    (p `pts_to_view` struct_view tag fields excluded)
    (fun q ->
      (p `pts_to_view` struct_view tag fields (insert field excluded)) `star`
      (pts_to_view u#0
                  #'a
                  #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).view_type))
                  #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).view_type))
                  #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).carrier))
                  #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).pcm))
                  q
                  (norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).view))))
    (requires fun _ -> not (excluded field))
    (ensures fun h q h' -> 
      not (excluded field) /\
      q == Steel.C.Ref.ref_focus p (struct_field tag fields field) /\
      fst (extract_field tag fields excluded field
        (h (p `pts_to_view` struct_view tag fields excluded)))
       == h' (p `pts_to_view` struct_view tag fields (insert field excluded))
        /\ 
        snd (extract_field tag fields excluded field
        (h (p `pts_to_view` struct_view tag fields excluded)))
        == h' (q `pts_to_view` (fields.get_field field).view))
= addr_of_struct_field''
    (normalize (fields.get_field field).view_type)
    (normalize (fields.get_field field).carrier)
    tag fields excluded field p

(** Inverse of unaddr_of_struct_field. *)
let unaddr_of_struct_field
  (#tag: Type0) (#fields: c_fields) (#excluded: excluded_fields)
  (field: field_of fields)
  (p: ref 'a (struct tag fields) (struct_pcm tag fields))
  (q: ref 'a
    (norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).view_type))
    (fields.get_field field).pcm)
: Steel unit
    ((p `pts_to_view` struct_view tag fields excluded) `star`
     (pts_to_view u#0
                  #'a
                  #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).view_type))
                  #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).view_type))
                  #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).carrier))
                  #(norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).pcm))
                  q
                  (norm simplify_typedefs (norm unfold_typedefs (fields.get_field field).view))))
    (fun _ -> p `pts_to_view` struct_view tag fields (remove field excluded))
    (requires fun _ ->
      excluded field == true /\
      q == ref_focus p (struct_field tag fields field))
    (ensures fun h _ h' -> 
      excluded field == true /\
      fst (extract_field tag fields (remove field excluded) field
        (h' (p `pts_to_view` struct_view tag fields (remove field excluded))))
       == h (p `pts_to_view` struct_view tag fields excluded)
        /\
        snd (extract_field tag fields (remove field excluded) field
        (h' (p `pts_to_view` struct_view tag fields (remove field excluded)))) ==
         h (q `pts_to_view` (fields.get_field field).view))
=
//let unaddr_of_struct_field #a #tag #fields #excluded field p q =
  unaddr_of_struct_field_ref' field p q
