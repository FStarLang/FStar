module Steel.C.TypedefNorm

open Steel.C.StructLiteral
open Steel.C.UnionLiteral
open Steel.C.Fields
open Steel.C.Typedef
open Steel.C.Typenat
open Steel.C.Typestring

unfold let norm_c_typedef =
  [delta_only
    [`%mk_c_union;
     `%mk_c_struct;
     `%c_fields_t;
     `%List.Tot.fold_right;
     `%Steel.C.Typestring.mk_string_t;
     `%Steel.C.Typestring.string_t_of_chars;
     `%Steel.C.Typestring.char_t_of_char;
     `%Mkc_fields?.get_field;
     `%Mkc_fields?.cfields;
     `%Mktypedef?.view_type;
     `%fields_cons;
     `%fields_nil;
     `%Steel.C.Typenat.nat_t_of_nat;
     ];
   delta_attr [`%c_struct; `%c_typedef];
   iota; zeta; primops]
