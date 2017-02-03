open List
open Lexing
open Parsetree
open Location
open Pprintast
open Ast_helper
open Asttypes
open Longident

open FStar_Extraction_ML_Syntax


let flatmap f l = map f l |> List.flatten
let opt_to_list = function Some x -> [x] | None -> []

(* these might not be needed if only using Ast_helpers *)
let no_position : Lexing.position =
  {pos_fname = ""; pos_lnum = 0; pos_bol = 0; pos_cnum = 0}

let no_location : Location.t = 
  {loc_start = no_position; loc_end = no_position; loc_ghost = false}

let no_attrs: attributes = []

let mk_sym s: 'a Location.loc = {txt=s; loc=no_location}

let build_symbol (s: string): Longident.t = Longident.parse s

let path_to_ident ((l, sym): mlpath): Longident.t Asttypes.loc =
  match l with
  | [] -> Lident sym |> mk_sym
  | (hd::tl) -> 
     let q = fold_left (fun x y -> Ldot (x,y)) (Lident hd) tl in
     Ldot(q, sym) |> mk_sym

let build_constant (c: mlconstant): Parsetree.constant =
  match c with
  | MLC_Int (v, _) -> Const.integer v
  | MLC_Float v -> Const.float (string_of_float v)
  | MLC_Char v -> Const.char v
  | MLC_String v -> Const.string v
  | _ -> failwith "not defined10"

let build_constant_expr (c: mlconstant): expression =
  match c with
  | MLC_Unit -> Exp.construct (mk_sym (Lident "()")) None
  | MLC_Bool b -> 
     let id = if b then "true" else "false" in
     Exp.construct (mk_sym (Lident id)) None
  | _ -> Exp.constant (build_constant c)

let build_constant_pat (c: mlconstant): pattern_desc =
  match c with
  | MLC_Unit -> Ppat_construct (mk_sym (Lident "()"), None)
  | MLC_Bool b -> 
     let id = if b then "true" else "false" in
     Ppat_construct (mk_sym (Lident id), None)
  | _ -> Ppat_constant (build_constant c)

let rec build_pattern (p: mlpattern): pattern =
  let desc = (match p with
  | MLP_Wild -> Ppat_any
  | MLP_Const c -> build_constant_pat c
  | MLP_Var (sym, _) -> Ppat_var (mk_sym sym)
  | MLP_CTor (path, [pat]) ->
     let name = match path with (_, sym) -> sym in
     Ppat_construct (mk_sym (Lident name), Some (build_pattern pat))
  | MLP_CTor (path, pats) ->
     let name = match path with (_, sym) -> sym in
     let inner = Pat.tuple (map build_pattern pats) in
     Ppat_construct (mk_sym (Lident name), Some inner) 
  | MLP_Branch l -> Ppat_tuple (map build_pattern l)
  | MLP_Record (syms, l) -> 
     let fs = map (fun (x,y) -> (mk_sym (Lident x), build_pattern y)) l in
     Ppat_record (fs, Open) (* does the closed flag matter? *)
  | MLP_Tuple l -> Ppat_tuple (map build_pattern l)
             ) in
  Pat.mk desc

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
     let c_tys = map build_core_type tys in
     let p = path_to_ident path in
     Typ.mk (Ptyp_constr (p, c_tys))
  | MLTY_Tuple tys -> Typ.mk (Ptyp_tuple (map build_core_type tys))
  | MLTY_Top -> Typ.mk Ptyp_any

let rec build_binding_pattern ?ty ((sym, _): mlident) : pattern =
  let p = Pat.mk (Ppat_var (mk_sym sym)) in
  match ty with
  | Some t -> 
     Pat.mk (Ppat_constraint (p, build_core_type t))
  | None -> p

let rec build_expr (e: mlexpr): expression = 
  match e.expr with
  | MLE_Const c -> build_constant_expr c
  | MLE_Var (sym, _) -> Exp.ident (mk_sym (Lident sym))
  | MLE_Name path -> Exp.ident (path_to_ident path)
  | MLE_Let ((flavour, c_flags, lbs), expr) -> 
     let recf = match flavour with | Rec -> Recursive | NonRec -> Nonrecursive in
     let val_bindings = map build_binding lbs in
     Exp.let_ recf val_bindings (build_expr expr)

   | MLE_App (e, es) -> 
      let args = map (fun x -> (Nolabel, build_expr x)) es in
      Exp.apply (build_expr e) args
   | MLE_Fun (l, e) -> (* apply each argument of the function *)
      (match l with
      | ((id, ty)::tl) -> 
         let p = build_binding_pattern ~ty:ty id in
         Exp.fun_ Nolabel None p (build_expr e)
      | [] -> build_expr e)
   | MLE_Match (e, branches) ->
      let ep = build_expr e in
      let cases = map build_case branches in
      Exp.match_ ep cases
   | MLE_Coerce (e, ty1, ty2) -> 
      let ep = build_expr e in
      let ty1p = build_core_type ty1 in
      let ty2p = build_core_type ty2 in
      Exp.coerce ep (Some ty1p) ty2p
   | MLE_CTor (path, [e]) ->
      let name = match path with (_, sym) -> sym in
      Exp.construct (mk_sym (Lident name)) (Some (build_expr e))
   | MLE_CTor (path, es) ->
      let name = match path with (_, sym) -> sym in
      let inner = Exp.tuple (map build_expr es) in
      Exp.construct (mk_sym (Lident name)) (Some inner) 
   | MLE_Seq _ -> failwith "not defined26"    
   | MLE_Tuple l -> Exp.tuple (map build_expr l)
   | MLE_Record (path, l) ->
      let fields = map (fun (x,y) -> (mk_sym (Lident x), build_expr y)) l in
      Exp.record fields None
   | MLE_Proj (e, path) -> 
      let field = match path with (_, f) -> f in
      Exp.field (build_expr e) (mk_sym (Lident field))
   | MLE_If _ -> failwith "not defined30" (* always desugared to match? *)    
   | MLE_Raise _ -> failwith "not defined31"  
   | MLE_Try _ -> failwith "not defined32"

and build_case ((lhs, guard, rhs): mlbranch): case =
  {pc_lhs = (build_pattern lhs); 
   pc_guard = BatOption.map build_expr guard; 
   pc_rhs = (build_expr rhs)}

and build_value (mllbs: mllb list): value_binding list =
  map build_binding mllbs

and build_binding (lb: mllb): value_binding =
  match lb.mllb_tysc with
  | None -> 
     let e = build_expr lb.mllb_def in
     let p = build_binding_pattern lb.mllb_name in
     (Vb.mk p e)
  | Some _ ->  (* wrong *)
     let e = build_expr lb.mllb_def in
     let p = build_binding_pattern lb.mllb_name in
     (Vb.mk p e) 

let build_row_field (sym, tys): row_field = 
  Rtag (sym, no_attrs, false, map build_core_type tys)

let build_ty_manifest (b: mltybody): core_type option= 
  match b with
  | MLTD_Abbrev ty -> Some (build_core_type ty)
  | MLTD_Record l -> None
  | MLTD_DType l -> None

let build_label_decl (sym, ty): label_declaration =
  Type.field (mk_sym sym) (build_core_type ty)

let build_constructor_decl (sym, tys): constructor_declaration =
  let args = if BatList.is_empty tys then None else
    Some (Pcstr_tuple (map build_core_type tys)) in
  Type.constructor ?args:args (mk_sym sym)

let build_ty_kind (b: mltybody): type_kind = 
  match b with
  | MLTD_Abbrev ty -> Ptype_abstract
  | MLTD_Record l -> Ptype_record (map build_label_decl l)
  | MLTD_DType l -> Ptype_variant (map build_constructor_decl l)

let build_one_tydecl ((_, x, mangle_opt, tparams, body): one_mltydecl): type_declaration = 
 let ptype_name = match mangle_opt with
    | Some y -> mk_sym y
    | None -> mk_sym x in
  let ptype_params = Some (map (fun (sym, _) -> Typ.mk (Ptyp_var sym), Invariant) tparams) in
  let (ptype_manifest: core_type option) = BatOption.map_default build_ty_manifest None body in
  let ptype_kind =  Some (BatOption.map_default build_ty_kind Ptype_abstract body) in
  (Type.mk ?params:ptype_params ?kind:ptype_kind ?manifest:ptype_manifest ptype_name)

let build_tydecl (td: mltydecl): structure_item_desc =
  (* list length > 1 for mutually recursive type declarations *)
  let recf = Recursive in
  let type_declarations = map build_one_tydecl td in 
  Pstr_type(recf, type_declarations)

let build_mlsig1 = function
    MLS_Mod (sym, s) -> failwith "not defined0"
  | MLS_Ty  tydecl -> failwith "not defined1"
  | MLS_Val (sym, tyscheme) -> failwith "not defined2"
  | MLS_Exn (sym, mltys) -> failwith "not defined3"

let build_module1 (m1: mlmodule1): structure_item option = match m1 with
  | MLM_Ty tydecl -> Some (Str.mk (build_tydecl tydecl))
  | MLM_Let (flav, flags, mllbs) -> 
     let recf = match flav with | Rec -> Recursive | NonRec -> Nonrecursive in
     let bindings = map build_binding mllbs in
     Some (Str.value recf bindings)
  | MLM_Exn (sym, tys) ->  failwith "not defined6"
  | MLM_Top expr -> failwith "not defined45" (* Some (Str.eval (build_expr expr)) *)
  | MLM_Loc loc -> None (* do we need this? *)

let build_m (md: (mlsig * mlmodule) option) : structure = match md with
  | Some(s, m) -> 
     let a = map build_mlsig1 s in (* is this necessary? *)
     (map build_module1 m |> flatmap opt_to_list)
  | None -> []

let build_ast = function
  MLLib l -> map (fun (path, md, _) -> build_m md) l |> List.flatten

let print ml = structure Format.std_formatter (build_ast ml)


