open Prims
open FStar_Pervasives
open FStar_Syntax_Syntax
open FStar_Ident
open Yojson.Safe
let decl_as_json : (lident * univ_names * typ) -> string =
  fun (lid, univs, t) ->
    let pair =
      `Assoc [ "lid", `String (string_of_lid lid);
               "univs", univ_names_to_yojson univs;
               "typ", term_to_yojson t ]
    in
    Yojson.Safe.to_string pair

