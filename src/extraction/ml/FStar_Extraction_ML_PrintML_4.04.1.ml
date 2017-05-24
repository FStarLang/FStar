open List
open Lexing
open Parsetree
open Location
open Pprintast
open Ast_helper
open Asttypes
open Longident

open FStar_Extraction_ML_Syntax

(* Global state used for the name of the ML module being pprinted.
   current_module is only set once in build_ast and read once in
   path_to_ident. This is done in order to avoid clutter. *)
let current_module = ref ""


let flatmap f l = map f l |> List.flatten
let opt_to_list = function Some x -> [x] | None -> []


let no_position : Lexing.position =
  {pos_fname = ""; pos_lnum = 0; pos_bol = 0; pos_cnum = 0}

let no_location : Location.t =
  {loc_start = no_position; loc_end = no_position; loc_ghost = false}

let no_attrs: attributes = []


(* functions for generating names and paths *)
let mk_sym s: string Location.loc = {txt=s; loc=no_location}

let mk_sym_lident s: Longident.t Location.loc = {txt=s; loc=no_location}

let mk_lident name = Lident name |> mk_sym_lident

let mk_typ_name s =
  (* remove an apostrophe from beginning of type name *)
  match (BatString.sub s 0 1) with
  | "'" -> BatString.tail s 1
  | _ -> s

let rec path_to_string ((l, sym): mlpath): string =
  match l with
  | [] -> sym
  | (hd::tl) -> BatString.concat "_" [hd; path_to_string (tl, sym)]

let split_path (l1: string list) (l2: string list): (string list * string list) option =
  let rec split_aux l1 l2 =
    match l2 with
     | [] -> Some l1
     | hd2::tl2 when BatString.equal hd2 (hd l1) -> split_aux (tl l1) tl2
     | _ -> None
  in
  if (length l1 >= length l2) then
    match split_aux l1 l2 with
    | None -> None
    | Some l1' -> Some (l1', l2)
  else None

let path_to_ident ((l, sym): mlpath): Longident.t Asttypes.loc =
  let codegen_libs = FStar_Options.codegen_libs() in
  match l with
  | [] -> mk_lident sym
  | ["FStar"; "Pervasives"] when BatList.mem sym ["Some"; "None"] ->
     (* as in the original printer, stripping module from some constructors *)
     mk_lident sym
  | hd::tl ->
     let m_name = !current_module in
     let suffix, prefix =
       try BatList.find_map (split_path l) codegen_libs with
       | Not_found -> l, []
     in
       let path_abbrev = BatString.concat "_" suffix in
       if (prefix = [] && BatString.equal m_name path_abbrev) then
         (* remove circular references *)
          mk_lident sym
       else
         match prefix with
         | [] ->  Ldot(Lident path_abbrev, sym) |> mk_sym_lident
         | p_hd::p_tl ->
            let q = fold_left (fun x y -> Ldot (x,y)) (Lident p_hd) p_tl in
            (match path_abbrev with
             | "" -> Ldot(q, sym) |> mk_sym_lident
             | _ -> Ldot(Ldot(q, path_abbrev), sym) |> mk_sym_lident)


(* names of F* functions which need to be handled differently *)
let fst_ident = path_to_ident (["FStar"; "Pervasives"], "fst")
let snd_ident = path_to_ident (["FStar"; "Pervasives"], "snd")
let raise_ident = path_to_ident (["FStar"; "Pervasives"], "raise")
let try_with_ident = path_to_ident (["FStar"; "All"], "try_with")


(* mapping functions from F* ML AST to Parsetree *)
let build_constant (c: mlconstant): Parsetree.constant =
  match c with
  | MLC_Int (v, _) ->
     let i = BatString.concat "" ["(Prims.parse_int \""; v; "\")"] in
     Const.integer i
  | MLC_Float v -> failwith "Case not handled"
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
      | [] -> failwith "Empty branch shouldn't happen")
  | MLP_Record (path, l) ->
     let fs = map (fun (x,y) -> (path_to_ident (path, x), build_pattern y)) l in
     Pat.record fs Open (* does the closed flag matter? *)
  | MLP_Tuple l -> Pat.tuple (map build_pattern l)

and build_constructor_pat ((path, sym), p) =
  let (path', name) =
    (* resugaring the Cons and Nil from Prims *)
    (match path with
     | ["Prims"] ->
       (match sym with
        | "Cons" -> ([], "::")
        | "Nil" -> ([], "[]")
        | x -> (path, x))
     | _ -> (path, sym)) in
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
     let label = Nolabel in
     Typ.mk (Ptyp_arrow (label,c_ty1,c_ty2))
  | MLTY_Named (tys, path) ->
     let c_tys = map build_core_type tys in
     let p = path_to_ident path in
     (match path with
      | (["FStar"; "Pervasives"], c) ->
        if ((BatString.length c == 6) &&
            (BatString.equal (BatString.sub c 0 5) "tuple")) then
          (* resugar tuples (Prims.tupleX) *)
          Typ.mk (Ptyp_tuple (map build_core_type tys))
        else if BatString.equal c "option" then
          Typ.mk (Ptyp_constr (path_to_ident ([], "option"), (map build_core_type tys)))
        else
          Typ.mk (Ptyp_constr (p, c_tys))
      | _ -> Typ.mk (Ptyp_constr (p, c_tys)))
  | MLTY_Tuple tys -> Typ.mk (Ptyp_tuple (map build_core_type tys))
  | MLTY_Top -> Typ.mk (Ptyp_constr (mk_lident "Obj.t", []))

let build_binding_pattern ((sym, _): mlident) : pattern =
  Pat.mk (Ppat_var (mk_sym sym))

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

let resugar_if_stmts ep cases =
  if List.length cases = 2 then
    let case1 = List.hd cases in
    let case2 = BatList.last cases in
    (match case1.pc_lhs.ppat_desc with
     | Ppat_construct({txt=Lident "true"}, None) ->
         Exp.ifthenelse ep case1.pc_rhs (Some case2.pc_rhs)
     | _ -> Exp.match_ ep cases)
  else
    Exp.match_ ep cases

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
      let f = build_expr e in
      resugar_app f args es
   | MLE_Fun (l, e) -> build_fun l e
   | MLE_Match (e, branches) ->
      let ep = build_expr e in
      let cases = map build_case branches in
      resugar_if_stmts ep cases
   | MLE_Coerce (e, _, _) ->
      let r = Exp.ident (mk_lident "Obj.magic") in
      Exp.apply r [(Nolabel, build_expr e)]
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
     | _ -> e')

and resugar_app f args es: expression =
  match f.pexp_desc with
  | Pexp_ident x when (x = try_with_ident) ->
    (* resugar FStar_All.try_with to a try...with
       try_with : (unit -> ML 'a) -> (exn -> ML 'a) -> ML 'a *)
    assert (length es == 2);
    let s, cs = BatList.first es, BatList.last es in
    let body = match s.expr with
      | MLE_Fun (_, e) ->
         (match e.expr with
          | MLE_Match (_, branches) ->
             assert (length branches == 1);
             (match (hd branches) with
              | (_, _, x) -> build_expr x
              | _ -> failwith "Cannot resugar FStar.All.try_with")
          | _ -> failwith "Cannot resugar FStar.All.try_with"
         )
      | _ -> failwith "Cannot resugar FStar.All.try_with" in
    let variants = match cs.expr with
      | MLE_Fun (_, e) ->
         (match e.expr with
          | MLE_Match (_, branches) ->
             map build_case branches
          | _ -> [build_case (MLP_Wild, None, e)]
         )
      | _ -> failwith "Cannot resugar FStar.All.try_with" in
    Exp.try_ body variants
  | Pexp_ident x when (x = fst_ident) ->
    Exp.apply (Exp.ident (mk_lident "fst")) args
  | Pexp_ident x when (x = snd_ident) ->
    Exp.apply (Exp.ident (mk_lident "snd")) args
  | Pexp_ident x when (x = raise_ident) ->
    Exp.apply (Exp.ident (mk_lident "raise")) args
  | _ -> Exp.apply f args

and build_seq args =
  match args with
  | [hd] -> build_expr hd
  | hd::tl -> Exp.sequence (build_expr hd) (build_seq tl)
  | [] -> failwith "Empty sequence should never happen"

and build_constructor_expr ((path, sym), exp): expression =
  let path', name =
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
      let p = build_binding_pattern id in
      Exp.fun_ Nolabel None p (build_fun tl e)
   | [] -> build_expr e

and build_case ((lhs, guard, rhs): mlbranch): case =
  {pc_lhs = (build_pattern lhs);
   pc_guard = BatOption.map build_expr guard;
   pc_rhs = (build_expr rhs)}

and build_binding (toplevel: bool) (lb: mllb): value_binding =
  (* replicating the rules for whether to print type ascriptions
     from the old printer *)
  let print_ty = if (lb.print_typ && toplevel) then
    (match lb.mllb_tysc with
     | Some ([], ty) -> true
     | _ -> false)
                 else false in
  let e = build_expr ?print_ty:(Some print_ty) lb.mllb_def in
  let p = build_binding_pattern lb.mllb_name in
  (Vb.mk p e)

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


let skip_type_defn (current_module:string) (type_name:string) :bool =
  current_module = "FStar_Pervasives" && type_name = "option"

let build_one_tydecl ((_, x, mangle_opt, tparams, body): one_mltydecl): type_declaration option =
  if skip_type_defn !current_module x then None
  else
    let ptype_name = match mangle_opt with
      | Some y -> mk_sym y
      | None -> mk_sym x in
    let ptype_params = Some (map (fun (sym, _) -> Typ.mk (Ptyp_var (mk_typ_name sym)), Invariant) tparams) in
    let (ptype_manifest: core_type option) = BatOption.map_default build_ty_manifest None body in
    let ptype_kind =  Some (BatOption.map_default build_ty_kind Ptype_abstract body) in
    Some (Type.mk ?params:ptype_params ?kind:ptype_kind ?manifest:ptype_manifest ptype_name)

let build_tydecl (td: mltydecl): structure_item_desc option =
  let recf = Recursive in
  let type_declarations = map build_one_tydecl td |> flatmap opt_to_list in
  if type_declarations = [] then None else Some (Pstr_type (recf, type_declarations))

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
  | MLM_Ty tydecl ->
     (match build_tydecl tydecl with
      | Some t -> Some (Str.mk t)
      | None   -> None)
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
     let a = map build_mlsig1 s in (* module signatures not yet implemented *)
     open_prims::(map (build_module1 path) m |> flatmap opt_to_list)
  | None -> []

let build_ast (out_dir: string option) (ext: string) (ml: mllib) =
  match ml with
  | MLLib l ->
     map (fun (p, md, _) ->
         let m = path_to_string p in
         current_module := m;
         let name = BatString.concat "" [m; ext] in
         let path = (match out_dir with
           | Some out -> BatString.concat "/" [out; name]
           | None -> name) in
         (path, build_m path md)) l


(* printing the AST to the correct path *)
let print_module ((path, m): string * structure) =
  Format.set_formatter_out_channel (open_out_bin path);
  structure Format.std_formatter m;
  Format.pp_print_flush Format.std_formatter ()

let print (out_dir: string option) (ext: string) (ml: mllib) =
  match ext with
  | ".ml" ->
     (* Use this printer for OCaml extraction *)
     let ast = build_ast out_dir ext ml in
     iter print_module ast
  | ".fs" ->
     (* Use the old printer for F# extraction *)
     let new_doc = FStar_Extraction_ML_Code.doc_of_mllib ml in
     iter (fun (n,d) ->
         FStar_Util.write_file
           (FStar_Options.prepend_output_dir (BatString.concat "" [n;ext]))
           (FStar_Format.pretty (Prims.parse_int "120") d)) new_doc
  | _ -> failwith "Unrecognized extension"
