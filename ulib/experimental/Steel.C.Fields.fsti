module Steel.C.Fields

open FStar.FSet
open FStar.FunctionalExtensionality

open Steel.C.Typedef
open Steel.C.Opt

module TS = Steel.C.Typestring

(** Used to control normalization *)
irreducible let c_struct = ()
irreducible let c_union = ()
irreducible let c_typedef = ()

[@@c_typedef]
let trivial_typedef: typedef = {
  carrier = option unit;
  pcm = opt_pcm #unit;
  view_type = unit;
  view = opt_view unit;
  is_unit = (fun o -> None? o);
}

(** While possible to encode struct fields as a list of (field name,
    typedef) pairs, such a representation does not play well with F*'s
    normalizer due to the fact that many kinds of queries we would like to
    perform on such lists of struct fields require recursion over that
    list. This interacts poorly with Steel's normalization tactic, and
    requires the user to increase fuel, which can be costly. To sidestep
    this, we essentially encode a list of fields by all of the various
    types at which we would like to eliminate that list, and build up each
    elimination at "list"-construction time by exposing combinators
    {c_fields_nil, c_fields_cons} which, rather than constructing a
    list, just precompute all of the facts that we could ever need to
    know in the future about it. All such facts are represented in
    the following c_fields struct. *)
//[@@__reduce__]
noeq type c_fields = {
  //cfields: clist string;
  cfields: list string;
  has_field: set string;
  has_field_mt: squash (has_field "" == true);
  has_field_prf: squash (forall field. has_field field == field `List.Tot.mem` cfields);
  get_field: string ^-> typedef;
  // get_field_prf: forall field. has_field field == false ==> get_field field == trivial_typedef;
  get_field_mt: squash (get_field "" == trivial_typedef);
  nonempty_witness:
    o:option string
     {(None? o ==> cfields == [""]) /\
      (Some? o ==> Some?.v o `List.Tot.mem` cfields /\ Some?.v o =!= "")};
}

(* Begin for extraction *)

(** The following combinators encode c_fields as a F* type, which
    allows struct field information to stick around after erasure for
    Kremlin. For more details about why we need this, see
    Steel.C.Typestring.fsti and Steel.C.Typenat.fsti *)

val c_fields_t_nil: Type0
val c_fields_t_cons
  (field: Type0) (t: Type0) (fields: Type0)
: Type0

let c_fields_t (fields: c_fields) =
  List.Tot.fold_right
    (fun field fields' ->
      c_fields_t_cons
        (TS.mk_string_t field)
        (fields.get_field field).view_type
        fields')
    fields.cfields
    c_fields_t_nil

(* End for extraction *)

//[@@__reduce__]
let fields_nil: c_fields = {
  cfields = [""];
  has_field = insert "" emptyset;
  has_field_mt = ();
  has_field_prf = ();
  //has_field_prf = ();
  get_field = on_dom _ (fun _ -> trivial_typedef);
  get_field_mt = ();
  nonempty_witness = None;
}

let field_t = field:string{field =!= ""}

//[@@__reduce__]
let fields_cons (field: field_t) (td: typedef) (fields: c_fields): c_fields = {
  cfields = field :: fields.cfields;
  has_field = insert field fields.has_field;
  has_field_mt = fields.has_field_mt;
  has_field_prf = fields.has_field_prf;
  get_field = on_dom _ (fun field' -> if field = field' then td else fields.get_field field');
  get_field_mt = ();
  nonempty_witness = Some field;
}

let field_of (fields: c_fields) = field:string{fields.has_field field == true /\ field =!= ""}

(** We divide normalization into two stages:
      1) First, all typedefs (which ought to have been defined with attribute c_typedef) are unfolded.
      2) Then, struct/union fields (which ought to have been defined
         with attributes c_struct and c_union respectively) are unfolded
         along with a number of helper definitions.
    This two-step normalization process is used by
    addr_of_struct_field and addr_of_union_field, and was developed to
    ensure that, in the case where a struct has structs inside of it,
    only the outermost typedef representing the outermost struct is
    unfolded.
    
    In retrospect, it's unclear whether this is needed, or even
    whether [norm] actually carries out such a 2-stage process.
    TODO see if this can be simplified *)

unfold let unfold_typedefs = [delta_attr [`%c_typedef]]

unfold let simplify_typedefs =
  [delta_attr [`%c_struct; `%c_union];
   delta_only
    [`%fields_cons;
     `%fields_nil;
     `%Mkc_fields?.get_field;
     `%Mktypedef?.carrier;
     `%Mktypedef?.pcm;
     `%Mktypedef?.view_type;
     `%Mktypedef?.view];
   iota; zeta; primops]

(* Operations on views *)

[@@c_typedef]
noextract inline_for_extraction
let opt_typedef (t: Type0): typedef = {
  carrier = option t;
  pcm = opt_pcm #t;
  view_type = t;
  view = opt_view t;
  is_unit = (fun x -> None? x);
}

open Steel.C.Reference

[@@c_typedef]
inline_for_extraction noextract
let refine_typedef
  (t: typedef)
  (p: (t.view_type -> Tot prop))
: Tot typedef
= {
  carrier = t.carrier;
  pcm = t.pcm;
  view_type = Steel.C.Ref.refine t.view_type p;
  view = refine_view t.view p;
  is_unit = t.is_unit;
}

[@@c_typedef]
inline_for_extraction noextract
let rewrite_typedef
  (t: typedef)
  (#view': Type)
  (f: t.view_type -> Tot view')
  (g: view' -> Tot t.view_type)
  (prf: squash (f `Steel.C.Connection.is_inverse_of` g))
: Tot typedef
= {
  carrier = t.carrier;
  pcm = t.pcm;
  view_type = view';
  view = rewrite_view t.view f g prf;
  is_unit = t.is_unit;
}
