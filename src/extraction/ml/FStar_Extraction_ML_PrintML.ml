open List
open Lexing
open Parsetree
open Location
open Pprintast
open Ast_helper
open Asttypes
open Longident

open FStar_Extraction_ML_Syntax

let m_ref = ref ""

let flatmap f l = map f l |> List.flatten
let opt_to_list = function Some x -> [x] | None -> []

let no_position : Lexing.position =
  {pos_fname = ""; pos_lnum = 0; pos_bol = 0; pos_cnum = 0}

let no_location : Location.t = 
  {loc_start = no_position; loc_end = no_position; loc_ghost = false}

let no_attrs: attributes = []

let mk_sym s: string Location.loc = {txt=s; loc=no_location}
let mk_sym_lident s: Longident.t Location.loc = {txt=s; loc=no_location}

let mk_lident name = Lident name |> mk_sym_lident

(* remove an apostrophe from beginning of type name *)
let mk_typ_name s = 
  match (BatString.sub s 0 1) with
  | "'" -> BatString.tail s 1
  | _ -> s

let rec path_to_string ((l, sym): mlpath): string =
  match l with
  | [] -> sym
  | (hd::tl) -> BatString.concat "_" [hd; path_to_string (tl, sym)]

let rec path_to_ident ((l, sym): mlpath): Longident.t Asttypes.loc =
  (* let _ = (match sym with
  | "lbname" -> (BatString.concat "/" l) |> print_string; print_string "\n"
  | _ -> ()) in *)
  match l with
  | [] -> mk_lident sym
  | ("FStar"::tl) ->
     let (l1, tl) = BatList.span (fun x -> x.[0] |> BatChar.is_uppercase) l in
     let hd = BatString.concat "_" l1 in
     path_to_ident ((hd::tl), sym)
  | ["Prims"] -> 
     let remove_qual = ["Some"; "None"] in
     if (BatList.mem sym remove_qual) then
       path_to_ident ([], sym)
     else 
       mk_lident (BatString.concat "." ["Prims"; sym])
  | (hd::tl) -> 
     let m_name = !m_ref in
     if (BatString.equal m_name hd) then path_to_ident (tl, sym) else 
      (let q = fold_left (fun x y -> Ldot (x,y)) (Lident hd) tl in
      Ldot(q, sym) |> mk_sym_lident)

let build_constant (c: mlconstant): Parsetree.constant =
  match c with
  | MLC_Int (v, _) -> 
     let i = BatString.concat "" ["(Prims.parse_int \""; v; "\")"] in
     Const.integer i
  | MLC_Float v -> Const.float (string_of_float v)
  | MLC_Char v -> Const.char v
  | MLC_String v -> Const.string v
  | MLC_Bytes _ -> failwith "not defined10" (* do we need this? *)

let build_constant_expr (c: mlconstant): expression =
  match c with
  | MLC_Unit -> Exp.construct (mk_lident "()") None
  | MLC_Bool b -> 
     let id = if b then "true" else "false" in
     Exp.construct (mk_lident id) None
  | _ -> Exp.constant (build_constant c)

let build_constant_pat (c: mlconstant): pattern_desc =
  match c with
  | MLC_Unit -> Ppat_construct (mk_lident "()", None)
  | MLC_Bool b -> 
     let id = if b then "true" else "false" in
     Ppat_construct (mk_lident id, None)
  | _ -> Ppat_constant (build_constant c)

let rec build_pattern (p: mlpattern): pattern =
  match p with
  | MLP_Wild -> Pat.any ()
  | MLP_Const c -> build_constant_pat c |> Pat.mk
  | MLP_Var (sym, _) -> Pat.var (mk_sym sym)
  | MLP_CTor args -> build_constructor_pat args |> Pat.mk
  | MLP_Branch l -> 
     (match l with
      | [pat] -> build_pattern pat
      | (pat1::tl) -> Pat.or_ (build_pattern pat1) (build_pattern (MLP_Branch tl))
      | [] -> failwith "can this happen?")
  | MLP_Record (path, l) -> 
     let fs = map (fun (x,y) -> (path_to_ident (path, x), build_pattern y)) l in
     Pat.record fs Open (* does the closed flag matter? *)
  | MLP_Tuple l -> Pat.tuple (map build_pattern l)

and build_constructor_pat ((path, sym), p) =
  let (path', name) = 
    (match sym with
    | "Cons" -> ([], "::")
    | "Nil" -> ([], "[]")
    | x -> (path, x)) in
  match p with
  | [] ->
     Ppat_construct (path_to_ident (path', name), None)
  | [pat] -> 
     Ppat_construct (path_to_ident (path', name), Some (build_pattern pat))
  | pats ->
     let inner = Pat.tuple (map build_pattern pats) in
     Ppat_construct (path_to_ident(path', name), Some inner) 

let rec build_core_type (ty: mlty): core_type =
  match ty with
  | MLTY_Var (sym, _) -> Typ.mk (Ptyp_var (mk_typ_name sym)) 
  | MLTY_Fun (ty1, tag, ty2) -> 
     let c_ty1 = build_core_type ty1 in
     let c_ty2 = build_core_type ty2 in
     let label = Nolabel (* do we need to preserve these labels? *)
                 (* Labelled (match tag with
                  | E_PURE -> "Pure"
                  | E_GHOST -> "Ghost"
                  | E_IMPURE -> "Impure"
                 ) *) in
     Typ.mk (Ptyp_arrow (label,c_ty1,c_ty2))
  | MLTY_Named (tys, path) -> 
     let c_tys = map build_core_type tys in
     let p = path_to_ident path in
     (match path with
      | (["Prims"], c) ->
        if ((BatString.length c == 6) && 
            (BatString.equal (BatString.sub c 0 5) "tuple")) then
          (* resugar tuples (Prims.tupleX) *) 
          Typ.mk (Ptyp_tuple (map build_core_type tys))
        else
          Typ.mk (Ptyp_constr (p, c_tys))
      | _ -> Typ.mk (Ptyp_constr (p, c_tys)))
  | MLTY_Tuple tys -> Typ.mk (Ptyp_tuple (map build_core_type tys))
  | MLTY_Top -> Typ.mk Ptyp_any

let build_binding_pattern ?print_ty ?ty ?scheme ((sym, _): mlident) : pattern =
  let pid = Pat.mk (Ppat_var (mk_sym sym)) in
  let p = pid (* (match scheme with
    | Some (ids, ty) -> 
       let binders = map (fun (x,_) -> (mk_typ_name x)) ids in
       Pat.mk (Ppat_constraint (pid, Typ.poly binders (build_core_type ty)))
    | None -> pid) *) in
  match ty with
  | Some t -> 
     (match print_ty with
      | Some true -> Pat.mk (Ppat_constraint (p, build_core_type t))
      | _ -> p)
  | None -> p

let resugar_prims_ops path: expression = 
  (match path with
  | (["Prims"], "op_Addition") -> mk_lident "+" 
  | (["Prims"], "op_Subtraction") -> mk_lident "-" 
  | (["Prims"], "op_Multiply") -> mk_lident "*" 
  | (["Prims"], "op_Division") -> mk_lident "/" 
  | (["Prims"], "op_Equality") -> mk_lident "=" 
  | (["Prims"], "op_Colon_Equals") -> mk_lident ":="
  | (["Prims"], "op_disEquality") -> mk_lident "<>"
  | (["Prims"], "op_AmpAmp") -> mk_lident "&&"
  | (["Prims"], "op_BarBar") -> mk_lident "||"
  | (["Prims"], "op_LessThanOrEqual") -> mk_lident "<="
  | (["Prims"], "op_GreaterThanOrEqual") -> mk_lident ">="
  | (["Prims"], "op_LessThan") -> mk_lident "<" 
  | (["Prims"], "op_GreaterThan") -> mk_lident ">" 
  | (["Prims"], "op_Modulus") -> mk_lident "mod"
  | (["Prims"], "op_Minus") -> mk_lident "~-"
  | path -> path_to_ident path)
  |> Exp.ident 

let rec build_expr ?print_ty (e: mlexpr): expression = 
  let e' = (match e.expr with
  | MLE_Const c -> build_constant_expr c
  | MLE_Var (sym, _) -> Exp.ident (mk_lident sym)
  | MLE_Name path -> 
     (match path with 
      | (["Prims"], op) -> resugar_prims_ops path
      | _ -> Exp.ident (path_to_ident path))
  | MLE_Let ((flavour, c_flags, lbs), expr) -> 
     let recf = match flavour with 
       | Rec -> Recursive 
       | NonRec -> Nonrecursive in
     let val_bindings = map (build_binding false) lbs in
     Exp.let_ recf val_bindings (build_expr expr)
   | MLE_App (e, es) -> 
      let args = map (fun x -> (Nolabel, build_expr x)) es in
      Exp.apply (build_expr e) args
   | MLE_Fun (l, e) -> build_fun l e
   | MLE_Match (e, branches) ->
      let ep = build_expr e in
      let cases = map build_case branches in
      Exp.match_ ep cases
   | MLE_Coerce (e, _, ty) -> 
      Exp.constraint_ (build_expr e) (build_core_type ty)
   | MLE_CTor args -> build_constructor_expr args
   | MLE_Seq args -> build_seq args
   | MLE_Tuple l -> Exp.tuple (map build_expr l)
   | MLE_Record (path, l) ->
      let fields = map (fun (x,y) -> (path_to_ident(path, x), build_expr y)) l in
      Exp.record fields None
   | MLE_Proj (e, path) -> 
      let field = match path with (_, f) -> f in
      Exp.field (build_expr e) (path_to_ident (path))
   (* MLE_If always desugared to match? *)
   | MLE_If (e, e1, e2) -> 
      Exp.ifthenelse (build_expr e) (build_expr e1) (BatOption.map build_expr e2)
   | MLE_Raise (path, es) -> 
      let r = Exp.ident (mk_lident "raise") in
      let args = map (fun x -> (Nolabel, build_expr x)) es in
      Exp.apply r args
   | MLE_Try (e, cs) ->
      Exp.try_ (build_expr e) (map build_case cs)) in
  match e.mlty with
  | MLTY_Top -> e'
  | t -> 
     (match print_ty with
     | Some true -> Exp.constraint_ e' (build_core_type t)
     | Some false -> e'
     | _ -> e' (* Exp.constraint_ e' (build_core_type t) *)) (* not sure *)

and build_seq args =
  match args with
  | [hd] -> build_expr hd
  | (hd::tl) -> Exp.sequence (build_expr hd) (build_seq tl)
  | [] -> failwith "Empty sequence should never happen"

and build_constructor_expr ((path, sym), exp): expression =
  let (path', name) = 
    (match sym with
    | "Cons" -> ([], "::")
    | "Nil" -> ([], "[]")
    | x -> (path, x)) in
  match exp with
  | [] -> Exp.construct (path_to_ident(path', name)) None
  | [e] -> 
     Exp.construct (path_to_ident(path', name)) (Some (build_expr e))
  | es ->
      let inner = Exp.tuple (map build_expr es) in
      Exp.construct (path_to_ident(path', name)) (Some inner) 

and build_fun l e = 
   match l with
   | ((id, ty)::tl) -> 
      let p = build_binding_pattern ~ty:ty id in 
      Exp.fun_ Nolabel None p (build_fun tl e)
   | [] -> build_expr e

and build_case ((lhs, guard, rhs): mlbranch): case =
  {pc_lhs = (build_pattern lhs); 
   pc_guard = BatOption.map build_expr guard; 
   pc_rhs = (build_expr rhs)}

(* and build_value (mllbs: mllb list): value_binding list =
  map build_binding mllbs *)

and build_binding (toplevel: bool) (lb: mllb): value_binding =
  let print_ty = if (lb.print_typ && toplevel) then
    (match lb.mllb_tysc with
     | Some ([], ty) -> true
     | _ -> false)
                 else false in 
  let e = build_expr ?print_ty:(Some print_ty) lb.mllb_def in
  let p = build_binding_pattern ?print_ty:(Some lb.print_typ) 
                                ?scheme:lb.mllb_tysc lb.mllb_name in
  (Vb.mk p e)

let build_row_field (sym, tys): row_field = 
  Rtag (sym, no_attrs, false, map build_core_type tys)

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

let build_ty_manifest (b: mltybody): core_type option= 
  match b with
  | MLTD_Abbrev ty -> Some (build_core_type ty)
  | MLTD_Record l -> None
  | MLTD_DType l -> None

let build_one_tydecl ((_, x, mangle_opt, tparams, body): one_mltydecl): type_declaration = 
 let ptype_name = match mangle_opt with
    | Some y -> mk_sym y
    | None -> mk_sym x in
  let ptype_params = Some (map (fun (sym, _) -> Typ.mk (Ptyp_var (mk_typ_name sym)), Invariant) tparams) in
  let (ptype_manifest: core_type option) = BatOption.map_default build_ty_manifest None body in
  let ptype_kind =  Some (BatOption.map_default build_ty_kind Ptype_abstract body) in
  (Type.mk ?params:ptype_params ?kind:ptype_kind ?manifest:ptype_manifest ptype_name)

let build_tydecl (td: mltydecl): structure_item_desc =
  (* list length > 1 for mutually recursive type declarations *)
  let recf = Recursive in
  let type_declarations = map build_one_tydecl td in 
  Pstr_type(recf, type_declarations)

let build_exn (sym, tys): extension_constructor =
  let name = mk_sym sym in
  let args = Some (Pcstr_tuple (map build_core_type tys)) in
  Te.decl ?args:args name

let build_mlsig1 = function
    MLS_Mod (sym, s) -> failwith "not defined0"
  | MLS_Ty  tydecl -> failwith "not defined1"
  | MLS_Val (sym, tyscheme) -> failwith "not defined2"
  | MLS_Exn (sym, mltys) -> failwith "not defined3"

let build_module1 path (m1: mlmodule1): structure_item option = 
  match m1 with
  | MLM_Ty tydecl -> Some (Str.mk (build_tydecl tydecl))
  | MLM_Let (flav, flags, mllbs) -> 
     let recf = match flav with | Rec -> Recursive | NonRec -> Nonrecursive in
     let bindings = map (build_binding true) mllbs in
     Some (Str.value recf bindings)
  | MLM_Exn exn -> Some (Str.exception_ (build_exn exn))
  | MLM_Top expr -> None
  | MLM_Loc (p, f) -> None

let build_m path (md: (mlsig * mlmodule) option) : structure = 
  match md with
  | Some(s, m) -> 
     let open_prims = 
       Str.open_ (Opn.mk ?override:(Some Fresh) (mk_lident "Prims")) in 
     let a = map build_mlsig1 s in (* is this necessary? *)
     open_prims::(map (build_module1 path) m |> flatmap opt_to_list)
  | None -> []

let build_ast = function
  | MLLib l -> 
     map (fun (p, md, _) -> 
         let m = path_to_string p in
         m_ref := m;
         let name = BatString.concat "." [m; "ml"] in
         let path = BatString.concat "/" ["pretty-output"; name] in
         (path, build_m path md)) l

let print_module ((path, m): string * structure) = 
  print_string path; print_string "\n"; 
  Format.set_formatter_out_channel (open_out path);
  structure Format.std_formatter m;
  Format.pp_print_flush Format.std_formatter ()

let print ml = 
  let ast = build_ast ml in
  iter print_module ast

