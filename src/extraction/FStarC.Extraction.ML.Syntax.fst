(*
   Copyright 2008-2016 Abhishek Anand, Nikhil Swamy,
                           Antoine Delignat-Lavaud, Pierre-Yves Strub
                               and Microsoft Research

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
(* -------------------------------------------------------------------- *)
module FStarC.Extraction.ML.Syntax
open FStarC.Effect
open FStarC.List
open FStarC
open FStarC.Ident
open FStarC.Const
open FStarC.BaseTypes

open FStarC.Class.Show
open FStarC.Class.PP
open FStarC.Pprint

(* -------------------------------------------------------------------- *)
let krml_keywords = []

let ocamlkeywords = [
  "and"; "as"; "assert"; "asr"; "begin"; "class";
  "constraint"; "do"; "done"; "downto"; "else"; "end";
  "exception"; "external"; "false"; "for"; "fun"; "function";
  "functor"; "if"; "in"; "include"; "inherit"; "initializer";
  "land"; "lazy"; "let"; "lor"; "lsl"; "lsr";
  "lxor"; "match"; "method"; "mod"; "module"; "mutable";
  "new"; "object"; "of"; "open"; "or"; "private";
  "rec"; "sig"; "struct"; "then"; "to"; "true";
  "try"; "type"; "val"; "virtual"; "when"; "while";
  "with"; "nonrec"
]

let fsharpkeywords = [
  "abstract"; "and"; "as"; "assert"; "base"; "begin"; "class";
  "default"; "delegate"; "do"; "done"; "downcast"; "downto";
  "elif"; "else"; "end"; "exception"; "extern"; "false";
  "finally"; "fixed"; "for"; "fun"; "function"; "global"; "if";
  "in"; "inherit"; "inline"; "interface"; "internal"; "lazy";
  "let"; "let!"; "match"; "member"; "module"; "mutable";
  "namespace"; "new"; "not"; "null"; "of"; "open"; "or";
  "override"; "private"; "public"; "rec"; "return"; "return!";
  "select"; "static"; "struct"; "then"; "to"; "true"; "try";
  "type"; "upcast"; "use"; "use!"; "val"; "void"; "when";
  "while"; "with"; "yield"; "yield!";
  // --mlcompatibility keywords
  "asr"; "land"; "lor";
  "lsl"; "lsr"; "lxor"; "mod"; "sig";
  // reserved keywords
  "atomic"; "break"; "checked"; "component"; "const";
  "constraint"; "constructor"; "continue"; "eager"; "event";
  "external"; "fixed"; "functor"; "include"; "method"; "mixin";
  "object"; "parallel"; "process"; "protected"; "pure";
  "sealed"; "tailcall"; "trait"; "virtual"; "volatile"
]

let string_of_mlpath ((p, s) : mlpath) : mlsymbol =
    String.concat "." (p @ [s])

let dummy_loc: mlloc = 0, ""

let mk_mlmodule1 m = { mlmodule1_m = m; mlmodule1_attrs = [] }
let mk_mlmodule1_with_attrs m attrs = { mlmodule1_m = m; mlmodule1_attrs = attrs }

let with_ty_loc t e l = {expr=e; mlty=t; loc = l }
let with_ty t e = with_ty_loc t e dummy_loc

// do NOT remove Prims, because all mentions of unit/bool in F* are actually Prims.unit/bool.
let ml_unit_ty    = MLTY_Erased
let ml_bool_ty    = MLTY_Named ([], (["Prims"], "bool"))
let ml_int_ty     = MLTY_Named ([], (["Prims"], "int"))
let ml_string_ty  = MLTY_Named ([], (["Prims"], "string"))

let ml_unit       = with_ty ml_unit_ty (MLE_Const MLC_Unit)

let apply_obj_repr :  mlexpr -> mlty -> mlexpr = fun x t ->
    let repr_name = if Options.codegen() = Some Options.FSharp
                    then MLE_Name([], "box")
                    else MLE_Name(["Obj"], "repr") in
    let obj_repr = with_ty (MLTY_Fun(t, E_PURE, MLTY_Top)) repr_name in
    with_ty_loc MLTY_Top (MLE_App(obj_repr, [x])) x.loc

let ty_param_names (tys:list ty_param) : list string =
  tys |> List.map (fun {ty_param_name} -> ty_param_name)

let push_unit eff (ts : mltyscheme) : mltyscheme =
    let vs, ty = ts in
    vs, MLTY_Fun(ml_unit_ty, eff, ty)

let pop_unit (ts : mltyscheme) : e_tag & mltyscheme =
    let vs, ty = ts in
    match ty with
    | MLTY_Fun (l, eff, t) ->
        if l = ml_unit_ty
        then eff, (vs, t)
        else failwith "unexpected: pop_unit: domain was not unit"
    | _ ->
        failwith "unexpected: pop_unit: not a function type"

let ctor' (n: string) (args: list document) =
  nest 2 (group (parens (flow (break_ 1) (doc_of_string n :: args))))
let ctor (n: string) (arg: document) =
  nest 2 (group (parens (doc_of_string n ^/^ arg)))

let rec mlty_to_doc (t:mlty) =
  match t with
  | MLTY_Var v -> doc_of_string v
  | MLTY_Fun (t1, _, t2) ->
    ctor' "<MLTY_Fun>" [mlty_to_doc t1; doc_of_string "->"; mlty_to_doc t2]
  | MLTY_Named (ts, p) ->
    ctor' "<MLTY_Named>" (List.map mlty_to_doc ts @ [doc_of_string (string_of_mlpath p)])
  | MLTY_Tuple ts ->
    ctor "<MLTY_Tuple>" <| flow_map (doc_of_string " *" ^^ break_ 1) mlty_to_doc ts
  | MLTY_Top -> doc_of_string "MLTY_Top"
  | MLTY_Erased -> doc_of_string "MLTY_Erased"
let mlty_to_string (t:mlty) = render (mlty_to_doc t)

let mltyscheme_to_doc (tsc:mltyscheme) =
  ctor "<MLTY_Scheme>"
    (brackets (flow_map (comma ^^ break_ 1) doc_of_string (ty_param_names (fst tsc)))
      ^^ doc_of_string "," ^/^ mlty_to_doc (snd tsc))
let mltyscheme_to_string (tsc:mltyscheme) = render (mltyscheme_to_doc tsc)

let pair a b = group (parens (a ^^ comma ^/^ b))
let triple a b c = group (parens (a ^^ comma ^/^ b ^^ comma ^/^ c))
let ctor2 n a b = ctor n (pair a b)
let list_to_doc #t (xs: list t) (f: t -> document) : document =
  nest 2 (group (brackets (flow_map (semi ^^ break_ 1) f xs)))
let option_to_doc #t (x: option t) (f: t -> document) : document =
  match x with
  | Some x -> group (doc_of_string "Some" ^/^ f x)
  | None -> doc_of_string "None"
let spaced a = break_ 1 ^^ a ^^ break_ 1
let record fs =
  group <| nest 2 <| braces <| spaced <| separate (semi ^^ break_ 1) fs
let fld n v = group <| nest 2 <| doc_of_string (n ^ " =") ^/^ v

let rec mlexpr_to_doc (e:mlexpr) =
  match e.expr with
  | MLE_Const c ->
    ctor "MLE_Const" (mlconstant_to_doc c)
  | MLE_Var x ->
    ctor "MLE_Var" (doc_of_string x)
  | MLE_Name (p, x) ->
    ctor2 "MLE_Name" (doc_of_string (String.concat "." p)) (doc_of_string x)
  | MLE_Let (lbs, e) ->
    ctor2 "MLE_Let" (mlletbinding_to_doc lbs) (mlexpr_to_doc e)
  | MLE_App (e, es) ->
    ctor2 "MLE_App" (mlexpr_to_doc e) (list_to_doc es mlexpr_to_doc)
  | MLE_TApp (e, ts) ->
    ctor2 "MLE_TApp" (mlexpr_to_doc e) (list_to_doc ts mlty_to_doc)
  | MLE_Fun (bs, e) ->
    ctor2 "MLE_Fun"
      (list_to_doc bs (fun b -> pair (doc_of_string b.mlbinder_name) (mlty_to_doc b.mlbinder_ty)))
      (mlexpr_to_doc e)
  | MLE_Match (e, bs) ->
    ctor2 "MLE_Match" (mlexpr_to_doc e) (list_to_doc bs mlbranch_to_doc)
  | MLE_Coerce (e, t1, t2) ->
    ctor "MLE_Coerce" <| triple (mlexpr_to_doc e) (mlty_to_doc t1) (mlty_to_doc t2)
  | MLE_CTor (p, es) ->
    ctor2 "MLE_CTor" (doc_of_string (string_of_mlpath p)) (list_to_doc es mlexpr_to_doc)
  | MLE_Seq es ->
    ctor "MLE_Seq" (list_to_doc es mlexpr_to_doc)
  | MLE_Tuple es ->
    ctor "MLE_Tuple" (list_to_doc es mlexpr_to_doc)
  | MLE_Record (p, n, es) ->
    ctor2 "MLE_Record" (list_to_doc (p@[n]) doc_of_string)
      (list_to_doc es (fun (x, e) -> pair (doc_of_string x) (mlexpr_to_doc e)))
  | MLE_Proj (e, p) ->
    ctor2 "MLE_Proj" (mlexpr_to_doc e) (doc_of_string (string_of_mlpath p))
  | MLE_If (e1, e2, e3) ->
    ctor "MLE_If" <| triple (mlexpr_to_doc e1) (mlexpr_to_doc e2) (option_to_doc e3 mlexpr_to_doc)
  | MLE_Raise (p, es) ->
    ctor2 "MLE_Raise" (doc_of_string (string_of_mlpath p)) (list_to_doc es mlexpr_to_doc)
  | MLE_Try (e, bs) ->
    ctor2 "MLE_Try" (mlexpr_to_doc e) (list_to_doc bs mlbranch_to_doc)

and mlbranch_to_doc (p, e1, e2) =
  triple (mlpattern_to_doc p) (option_to_doc e1 mlexpr_to_doc) (mlexpr_to_doc e2)

and mlletbinding_to_doc (lbs) =
  parens <|
    doc_of_string (match lbs._1 with | Rec -> "Rec" | NonRec -> "NonRec")
    ^^ doc_of_string ", " ^^
    list_to_doc lbs._2 mllb_to_doc

and mllb_to_doc (lb) =
  record [
    fld "mllb_name" (doc_of_string lb.mllb_name);
    fld "mllb_attrs" (list_to_doc lb.mllb_attrs mlexpr_to_doc);
    fld "mllb_tysc" (option_to_doc lb.mllb_tysc (fun (_, t) -> mlty_to_doc t));
    fld "mllb_add_unit" (pp lb.mllb_add_unit);
    fld "mllb_def" (mlexpr_to_doc lb.mllb_def);
  ]

and mlconstant_to_doc mlc =
  match mlc with
  | MLC_Unit -> doc_of_string "MLC_Unit"
  | MLC_Bool b -> ctor "MLC_Bool" (pp b)
  | MLC_Int (s, None) -> ctor "MLC_Int" (doc_of_string s)
  | MLC_Int (s, Some (s1, s2)) ->
    ctor "MLC_Int" <| triple (doc_of_string s) underscore underscore
  | MLC_Float f -> ctor "MLC_Float" underscore
  | MLC_Char c -> ctor "MLC_Char" underscore
  | MLC_String s -> ctor "MLC_String" (doc_of_string s)

and mlpattern_to_doc mlp =
  match mlp with
  | MLP_Wild -> doc_of_string "MLP_Wild"
  | MLP_Const c -> ctor "MLP_Const" (mlconstant_to_doc c)
  | MLP_Var x -> ctor "MLP_Var" (doc_of_string x)
  | MLP_CTor (p, ps) -> ctor2 "MLP_CTor" (doc_of_string (string_of_mlpath p)) (list_to_doc ps mlpattern_to_doc)
  | MLP_Branch ps -> ctor "MLP_Branch" (list_to_doc ps mlpattern_to_doc)

  | MLP_Record (path, fields) ->
    ctor2 "MLP_Record"
      (doc_of_string (String.concat "." path))
      (list_to_doc fields (fun (x, p) ->
        pair (doc_of_string x) (mlpattern_to_doc p)))
  | MLP_Tuple ps ->
    ctor "MLP_Tuple" (list_to_doc ps mlpattern_to_doc)

let mlbranch_to_string b = render (mlbranch_to_doc b)
let mlletbinding_to_string lb = render (mlletbinding_to_doc lb)
let mllb_to_string lb = render (mllb_to_doc lb)
let mlpattern_to_string p = render (mlpattern_to_doc p)
let mlconstant_to_string c = render (mlconstant_to_doc c)
let mlexpr_to_string e = render (mlexpr_to_doc e)

let mltybody_to_doc (d:mltybody) : document =
  match d with
  | MLTD_Abbrev mlty -> ctor "MLTD_Abbrev" (mlty_to_doc mlty)
  | MLTD_Record l ->
    ctor "MLTD_Record" <| group <| nest 2 <| braces <| spaced <|
      flow_map (semi ^^ break_ 1) (fun (x, t) -> pair (doc_of_string x) (mlty_to_doc t)) l
  | MLTD_DType l ->
    ctor "MLTD_DType" <| group <| nest 2 <| brackets <| spaced <|
      flow_map (semi ^^ break_ 1) (fun (x, l) -> pair (doc_of_string x)
        (list_to_doc l fun (x, t) -> pair (doc_of_string x) (mlty_to_doc t))) l
let mltybody_to_string (d:mltybody) : string = render (mltybody_to_doc d)

let one_mltydecl_to_doc (d:one_mltydecl) : document =
  record [
    fld "tydecl_name" (doc_of_string d.tydecl_name);
    fld "tydecl_parameters" (doc_of_string (String.concat "," (d.tydecl_parameters |> ty_param_names)));
    fld "tydecl_defn" (option_to_doc d.tydecl_defn mltybody_to_doc);
  ]
let one_mltydecl_to_string (d:one_mltydecl) : string = render (one_mltydecl_to_doc d)

let mlmodule1_to_doc (m:mlmodule1) : document =
  group (match m.mlmodule1_m with
  | MLM_Ty d -> doc_of_string "MLM_Ty " ^^ list_to_doc d one_mltydecl_to_doc
  | MLM_Let l -> doc_of_string "MLM_Let " ^^ mlletbinding_to_doc l
  | MLM_Exn (s, l) ->
    doc_of_string "MLM_Exn" ^/^
      pair (doc_of_string s)
      (list_to_doc l (fun (x, t) -> pair (doc_of_string x) (mlty_to_doc t)))
  | MLM_Top e -> doc_of_string "MLM_Top" ^/^ mlexpr_to_doc e
  | MLM_Loc _mlloc -> doc_of_string "MLM_Loc")
let mlmodule1_to_string (m:mlmodule1) : string = render (mlmodule1_to_doc m)

let mlmodulebody_to_doc (m:mlmodulebody) : document =
  group <| brackets <| spaced <| separate_map (semi ^^ break_ 1) mlmodule1_to_doc m
let mlmodulebody_to_string (m:mlmodulebody) : string = render (mlmodulebody_to_doc m)

instance showable_mlty         : showable mlty         = { show = mlty_to_string }
instance showable_mlconstant   : showable mlconstant   = { show = mlconstant_to_string }
instance showable_mlexpr       : showable mlexpr       = { show = mlexpr_to_string }
instance showable_mlmodule1    : showable mlmodule1    = { show = mlmodule1_to_string }
instance showable_mlmodulebody : showable mlmodulebody = { show = mlmodulebody_to_string }

instance pp_mlty               : pretty mlty           = { pp   = mlty_to_doc }
instance pp_mlconstant         : pretty mlconstant     = { pp   = mlconstant_to_doc }
instance pp_mlexpr             : pretty mlexpr         = { pp   = mlexpr_to_doc }
instance pp_mlmodule1          : pretty mlmodule1      = { pp   = mlmodule1_to_doc }
instance pp_mlmodulebody       : pretty mlmodulebody   = { pp   = mlmodulebody_to_doc }
