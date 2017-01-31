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

let build_constant (c: mlconstant): Parsetree.constant =
  match c with
  | MLC_Unit -> Const.string ">>>>> ()"
  | MLC_Bool _ -> Const.string ">>>>> bool"
  | MLC_Int (sym, _) -> Const.integer sym
  (* | MLC_Float _ -> Const.float "bogus" *)
  | MLC_Char c -> Const.char c
  | MLC_String s -> Const.string s 
  (* | MLC_Bytes b -> Const.string ">>>>> bytes" *)
  | _ -> Const.string "<<<<<< bad"

let rec build_pattern (p: mlpattern): pattern =
  let desc = (match p with
  | MLP_Wild -> Ppat_any
  | MLP_Const c -> Ppat_constant (build_constant c)
  | MLP_Var (sym, _) -> Ppat_var (mk_sym sym)
  | MLP_CTor (path, l) -> Ppat_tuple (map build_pattern l) (* wrong *)
  | MLP_Branch l -> Ppat_tuple (map build_pattern l)
  | MLP_Record (syms, l) -> Ppat_tuple (map (fun (_, x) -> build_pattern x) l) (* wrong *)
  | MLP_Tuple l -> Ppat_tuple (map build_pattern l)
             ) in
  Pat.mk desc

let path_to_ident ((l, sym): mlpath): Longident.t Asttypes.loc =
  match l with
  | [] -> Lident sym |> mk_sym
  | (hd::tl) -> 
     let q = fold_left (fun x y -> Ldot (x,y)) (Lident hd) tl in
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
  | MLE_Const c -> Exp.constant (build_constant c)
  | MLE_Var (sym, _) -> Exp.ident (mk_sym (Lident sym))
  | MLE_Name path -> Exp.ident (path_to_ident path)
  | MLE_Let ((flavour, c_flags, lbs), expr) -> failwith "not defined 15" 
     (* let recf = match flavour with | Rec -> Recursive | NonRec -> Nonrecursive in
     let val_bindings = map build_binding lbs in
     Exp.let_ recf val_bindings (build_expr expr) *)

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
   | MLE_CTor _ -> Exp.unreachable () (* wrong *)
   | MLE_Seq _ -> failwith "not defined26"    
   | MLE_Tuple _ -> failwith "not defined27"  
   | MLE_Record _ -> failwith "not defined28" 
   | MLE_Proj _ -> failwith "not defined29"   
   | MLE_If _ -> failwith "not defined30"     
   | MLE_Raise _ -> failwith "not defined31"  
   | MLE_Try _ -> failwith "not defined32"

and build_case ((lhs, guard, rhs): mlbranch): case =
  {pc_lhs = (build_pattern lhs); 
   pc_guard = BatOption.map build_expr guard; 
   pc_rhs = (build_expr rhs)}

and build_value (mllbs: mllb list): value_binding list =
  map build_binding mllbs

and build_binding (lb: mllb): value_binding =
  (* let e = build_expr lb.mllb_def in
  let p = match lb.mllb_tysc with 
    | Some (ids, ty) -> build_binding_pattern ty 
    | None -> (Pat.mk Ppat_any) in
  (Vb.mk p e) *)
  match lb.mllb_tysc with
  | None -> 
     let e = build_expr lb.mllb_def in
     let p = build_binding_pattern lb.mllb_name in
     (Vb.mk p e)
  | Some _ -> failwith "not defined57"

let build_row_field (sym, tys): row_field = 
  Rtag (sym, no_attrs, false, map build_core_type tys)

let build_tybody (b: mltybody option): core_type option = 
  match b with
  | Some body -> (match body with
     | MLTD_Abbrev ty -> Some (build_core_type ty)
     | MLTD_Record l -> 
        let rows: row_field list = map (fun (sym, ty) -> Rtag (sym, no_attrs, false, [build_core_type ty])) l in
        Some (Typ.variant rows Closed None) (* maybe don't map records to variants *)
     | MLTD_DType l -> 
        let rows = map build_row_field l in
        Some (Typ.variant rows Closed None)
     )
  | None -> None

let build_one_tydecl ((_, x, mangle_opt, tparams, body): one_mltydecl): type_declaration = 
  let ptype_name = match mangle_opt with
    | Some y -> mk_sym y
    | None -> mk_sym x in
  let ptype_params = Some (map (fun (sym, _) -> Typ.mk (Ptyp_var sym), Invariant) tparams) in
  let ptype_manifest = build_tybody body in
  (Type.mk ?params:ptype_params ptype_name ?manifest:ptype_manifest)

let build_tydecl (td: mltydecl): structure_item_desc =
  let recf = Nonrecursive in
  let type_declarations = map build_one_tydecl td in 
  Pstr_type(recf, type_declarations)

let build_mlsig1 = function
    MLS_Mod (sym, s) -> failwith "not defined0"
  | MLS_Ty  tydecl -> failwith "not defined1"
  | MLS_Val (sym, tyscheme) -> failwith "not defined2"
  | MLS_Exn (sym, mltys) -> failwith "not defined3"

let build_module1 (m1: mlmodule1): structure_item option = match m1 with
  | MLM_Ty tydecl -> Some (Str.mk (build_tydecl tydecl))  (* failwith "not defined4" *)
  | MLM_Let (flav, flags, mllbs) -> 
     let recf = match flav with | Rec -> Recursive | NonRec -> Nonrecursive in
     let bindings = map build_binding mllbs in
     let toplevel_e = Exp.construct (mk_sym (Lident "()")) None in
     let e = (Exp.let_ recf bindings toplevel_e) in 
     Some (Str.eval e)
  (* Some (Str.value Nonrecursive (build_value mllbs)) *)
  | MLM_Exn (sym, tys) -> None (* failwith "not defined6" *)
  | MLM_Top expr -> Some (Str.eval (build_expr expr))
  | MLM_Loc loc -> None

let build_m (md: (mlsig * mlmodule) option) : structure = match md with
  | Some(s, m) -> map build_module1 m |> flatmap opt_to_list
  | None -> failwith "not defined7"

let build_ast = function
  MLLib l -> map (fun (path, md, _) -> build_m md) l |> List.flatten

let print ml = structure Format.std_formatter (build_ast ml)


