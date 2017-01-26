open Lexing
open Parsetree
open Location
open Pprintast
open Ast_helper
open Asttypes
open Longident

open FStar_Extraction_ML_Syntax


let flatmap f l = List.map f l |> List.flatten
let opt_to_list = function Some x -> [x] | None -> []

(* these might not be needed if only using Ast_helpers *)
let no_position : Lexing.position =
  {pos_fname = ""; pos_lnum = 0; pos_bol = 0; pos_cnum = 0}

let no_location : Location.t = 
  {loc_start = no_position; loc_end = no_position; loc_ghost = false}

let mk_sym s: 'a Location.loc = {txt=s; loc=no_location}

let build_symbol (s: string): Longident.t = Longident.parse s

let build_pattern ((idents, ty): mltyscheme) : pattern =
  let desc = match ty with
    | MLTY_Var ident -> failwith "not defined9"
    | MLTY_Fun (ty1, e_tag, ty2) -> failwith "not defined10"
    | MLTY_Named (tys, path) -> failwith "not defined11"
    | MLTY_Tuple tys -> failwith "not defined12"
    | MLTY_Top -> Ppat_any in
  Pat.mk desc

let rec build_expr (e: mlexpr): expression = 
  match e.expr with
  | MLE_Let ((flavour, c_flags, lbs), expr) -> 
     let recf = match flavour with | Rec -> Recursive | NonRec -> Nonrecursive in
     let val_bindings = List.map build_binding lbs in
     Exp.let_ recf val_bindings (build_expr expr)
  | _ -> failwith "not defined8"

and build_binding (lb: mllb): value_binding =
  let e = build_expr lb.mllb_def in
  let p = match lb.mllb_tysc with 
    | Some tysc -> build_pattern tysc 
    | None -> (Pat.mk Ppat_any) in
  (Vb.mk p e)

let path_to_ident ((l, sym): mlpath): Longident.t Asttypes.loc =
  match l with
  | [] -> Lident sym |> mk_sym
  | (hd::tl) -> 
     let q = List.fold_left (fun x y -> Ldot (x,y)) (Lident hd) tl in
     Ldot(q, sym) |> mk_sym

let rec build_core_type (ty: mlty): core_type =
  match ty with
  | MLTY_Var (sym, _) -> Typ.mk (Ptyp_var sym) 
  | MLTY_Fun (ty1, tag, ty2) -> 
     let c_ty1 = build_core_type ty1 in
     let c_ty2 = build_core_type ty2 in
     let label = Labelled (match tag with
                  | E_PURE -> "Pure"
                  | E_GHOST -> "Ghost"
                  | E_IMPURE -> "Impure"
                 ) in
     Typ.mk (Ptyp_arrow (label,c_ty1,c_ty2))
  | MLTY_Named (tys, path) -> 
     let c_tys = List.map build_core_type tys in
     let p = path_to_ident path in
     Typ.mk (Ptyp_constr (p, c_tys))
  | MLTY_Tuple tys -> Typ.mk (Ptyp_tuple (List.map build_core_type tys))
  | MLTY_Top -> Typ.mk Ptyp_any

let build_tybody (b: mltybody option): core_type option = 
  match b with
  | Some body -> (match body with
     | MLTD_Abbrev ty -> Some (build_core_type ty)
     | MLTD_Record l -> None
     | MLTD_DType l -> None)
  | None -> None

let build_one_tydecl ((_, x, mangle_opt, tparams, body): one_mltydecl): type_declaration = 
  let ptype_name = match mangle_opt with
    | Some y -> mk_sym y
    | None -> mk_sym x in
  let ptype_params = Some (List.map (fun (sym, _) -> Typ.mk (Ptyp_var sym), Covariant) tparams) in
  let ptype_manifest = build_tybody body in
  (Type.mk ?params:ptype_params ptype_name ?manifest:ptype_manifest)

let build_tydecl (td: mltydecl): structure_item_desc =
  let recf = Nonrecursive in
  let type_declarations = List.map build_one_tydecl td in 
  Pstr_type(recf, type_declarations)

let build_mlsig1 = function
    MLS_Mod (sym, s) -> failwith "not defined0"
  | MLS_Ty  tydecl -> failwith "not defined1"
  | MLS_Val (sym, tyscheme) -> failwith "not defined2"
  | MLS_Exn (sym, mltys) -> failwith "not defined3"

let build_module1 (m1: mlmodule1): structure_item option = match m1 with
  | MLM_Ty tydecl -> Some (Str.mk (build_tydecl tydecl))  (* failwith "not defined4" *)
  | MLM_Let letbinding -> None (* failwith "not defined5" *)
  | MLM_Exn (sym, tys) -> None (* failwith "not defined6" *)
  | MLM_Top expr -> Some (Str.eval (build_expr expr))
  | MLM_Loc loc -> None

let build_m (md: (mlsig * mlmodule) option) : structure = match md with
  | Some(s, m) -> List.map build_module1 m |> flatmap opt_to_list
  | None -> failwith "not defined7"

let build_ast = function
  MLLib l -> List.map (fun (path, md, _) -> build_m md) l |> List.flatten

let print ml = structure Format.std_formatter (build_ast ml)


