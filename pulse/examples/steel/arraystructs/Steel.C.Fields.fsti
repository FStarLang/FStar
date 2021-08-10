module Steel.C.Fields

open FStar.FSet
open FStar.FunctionalExtensionality

open Steel.C.Typedef
open Steel.C.Opt

module TS = Typestring

//[@@__reduce__]
noeq type c_fields = {
  //cfields: clist string;
  cfields: list string;
  has_field: set string;
  //has_field_prf: squash (forall field. has_field field == field `mem` cfields);
  get_field: string ^-> typedef;
  // get_field_prf: forall field. has_field field == false ==> get_field field == trivial_typedef;
}

(* Begin for extraction *)

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

let trivial_typedef: typedef = {
  carrier = option unit;
  pcm = opt_pcm #unit;
  view_type = unit;
  view = opt_view unit;
}

//[@@__reduce__]
let fields_nil: c_fields = {
  cfields = [];
  has_field = emptyset;
  //has_field_prf = ();
  get_field = on_dom _ (fun _ -> trivial_typedef);
}

//[@@__reduce__]
let fields_cons (field: string) (td: typedef) (fields: c_fields): c_fields = {
  cfields = field :: fields.cfields;
  has_field = insert field fields.has_field;
  //has_field_prf = ();
  get_field = on_dom _ (fun field' -> if field = field' then td else fields.get_field field');
}

let field_of (fields: c_fields) = field:string{fields.has_field field == true}

irreducible let c_struct = ()
irreducible let c_union = ()
irreducible let c_typedef = ()

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
