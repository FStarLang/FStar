open List
open Lexing
open Ppxlib_ast
open Astlib.Ast_500.Parsetree
open Location
open Pprintast
open Ast_helper
open Astlib.Ast_500.Asttypes
open Longident

open FStarC_Extraction_ML_Syntax

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
  let codegen_libs = FStarC_Options.codegen_libs() in
  match l with
  | [] -> mk_lident sym
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

let mk_top_mllb (e: mlexpr): mllb =
  {mllb_name="_";
   mllb_tysc=None;
   mllb_add_unit=false;
   mllb_def=e;
   mllb_meta=[];
   mllb_attrs=[];
   print_typ=false }

(* Find the try_with in the default effect module. For instance this can be
FStar.All.try_with (for most users) or FStarC.Compiler.Effect.try_with (during
bootstrapping with "--MLish --MLish_effect FStarC.Compiler.Effect"). *)
let try_with_ident () =
  let lid = FStarC_Parser_Const.try_with_lid () in
  let ns = FStarC_Ident.ns_of_lid lid in
  let id = FStarC_Ident.ident_of_lid lid in
  path_to_ident (List.map FStarC_Ident.string_of_id ns, FStarC_Ident.string_of_id id)

(* For integer constants (not 0/1) in this range we will use Prims.of_int
 * Outside this range we will use string parsing to allow arbitrary sized
 * integers.
 * Using int_zero/int_one removes int processing to create the Z.t
 * Using of_int removes string processing to create the Z.t
 *)
let max_of_int_const = Z.of_int   65535
let min_of_int_const = Z.of_int (-65536)

(* mapping functions from F* ML AST to Parsetree *)
let build_constant (c: mlconstant): Parsetree.constant =
  let stdint_module (s:FStarC_Const.signedness) (w:FStarC_Const.width) : string =
    let sign = match s with
      | FStarC_Const.Signed -> "Int"
      | FStarC_Const.Unsigned -> "Uint" in
    let with_w ws = BatString.concat "" ["Stdint."; sign; ws] in
    match w with
    | FStarC_Const.Int8 -> with_w "8"
    | FStarC_Const.Int16 -> with_w "16"
    | FStarC_Const.Int32 -> with_w "32"
    | FStarC_Const.Int64 -> with_w "64"
    | FStarC_Const.Sizet -> with_w "64" in
  match c with
  | MLC_Int (v, None) ->
      let s = match Z.of_string v with
        | x when x = Z.zero -> "Prims.int_zero"
        | x when x = Z.one -> "Prims.int_one"
        | x when (min_of_int_const < x) && (x < max_of_int_const) ->
            BatString.concat v ["(Prims.of_int ("; "))"]
        | x ->
            BatString.concat v ["(Prims.parse_int \""; "\")"] in
      Const.integer s
  (* Special case for UInt8, as it's realized as OCaml built-in int type *)
  | MLC_Int (v, Some (FStarC_Const.Unsigned, FStarC_Const.Int8)) ->
      Const.integer v
  | MLC_Int (v, Some (s, w)) ->
      let s = match Z.of_string v with
        | x when x = Z.zero ->
            BatString.concat "" [stdint_module s w; ".zero"]
        | x when x = Z.one ->
            BatString.concat "" [stdint_module s w; ".one"]
        | x when (min_of_int_const < x) && (x < max_of_int_const) ->
            BatString.concat "" ["("; stdint_module s w; ".of_int ("; v; "))"]
        | x ->
            BatString.concat "" ["("; stdint_module s w; ".of_string \""; v; "\")"] in
      Const.integer s
  | MLC_Float v -> Const.float (string_of_float v)
  | MLC_Char v -> Const.int v
  | MLC_String v -> Const.string v
  | MLC_Bytes _ -> failwith "Case not handled" (* do we need this? *)
  | _ -> failwith "Case not handled"

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
  | MLP_Var sym -> Pat.var (mk_sym sym)
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
     Ppat_construct (path_to_ident (path', name), Some ([], build_pattern pat))
  | pats ->
     let inner = Pat.tuple (map build_pattern pats) in
     Ppat_construct (path_to_ident(path', name), Some ([], inner))

let rec build_core_type ?(annots = []) (ty: mlty): core_type =
  let t =
  match ty with
  | MLTY_Var sym -> Typ.mk (Ptyp_var (mk_typ_name sym))
  | MLTY_Fun (ty1, tag, ty2) ->
     let c_ty1 = build_core_type ty1 in
     let c_ty2 = build_core_type ty2 in
     let label = Nolabel in
     Typ.mk (Ptyp_arrow (label,c_ty1,c_ty2))
  | MLTY_Named (tys, (path, sym)) ->
     let c_tys = map build_core_type tys in
     let p = path_to_ident (path, sym) in
     let ty = Typ.mk (Ptyp_constr (p, c_tys)) in
     (match path with
      | ["FStar"; "Pervasives"; "Native"] ->
        (* A special case for tuples, so they are displayed as
         * ('a * 'b) instead of ('a,'b) FStarC_Pervasives_Native.tuple2
         * VD: Should other types named "tupleXX" where XX does not represent
         * the arity of the tuple be added to FStar.Pervasives.Native,
         * the condition below might need to be more specific. *)
        if BatString.starts_with sym "tuple" then
          Typ.mk (Ptyp_tuple (map build_core_type tys))
        else
          ty
      | _ -> ty)
  | MLTY_Tuple tys -> Typ.mk (Ptyp_tuple (map build_core_type tys))
  | MLTY_Top -> Typ.mk (Ptyp_constr (mk_lident "Obj.t", []))
  | MLTY_Erased -> Typ.mk (Ptyp_constr (mk_lident "unit", []))
  in
  if annots = []
  then t
  else Typ.mk (Ptyp_poly (annots, t))

let build_binding_pattern ?ty (sym : mlident) : pattern =
    let p = Pat.mk (Ppat_var (mk_sym sym)) in
    match ty with
    | None -> p
    | Some ty -> Pat.mk (Ppat_constraint (p, ty))

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

let rec build_expr (e: mlexpr): expression =
  match e.expr with
  | MLE_Const c -> build_constant_expr c
  | MLE_Var sym -> Exp.ident (mk_lident sym)
  | MLE_Name path ->
     (match path with
      | (["Prims"], op) -> resugar_prims_ops path
      | _ -> Exp.ident (path_to_ident path))
  | MLE_Let ((flavour, lbs), expr) ->
     let recf = match flavour with
       | Rec -> Recursive
       | NonRec -> Nonrecursive in
     let val_bindings = map (build_binding false) lbs in
     Exp.let_ recf val_bindings (build_expr expr)
   | MLE_App (e, es) ->
      let args = map (fun x -> (Nolabel, build_expr x)) es in
      let f = build_expr e in
      resugar_app f args es
   | MLE_TApp (e, ts) ->
      build_expr e
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
   | MLE_Record (path, _, l) ->
      let fields = map (fun (x,y) -> (path_to_ident(path, x), build_expr y)) l in
      Exp.record fields None
   | MLE_Proj (e, path) ->
      Exp.field (build_expr e) (path_to_ident (path))
   (* MLE_If always desugared to match? *)
   | MLE_If (e, e1, e2) ->
      Exp.ifthenelse (build_expr e) (build_expr e1) (BatOption.map build_expr e2)
   | MLE_Raise (path, es) ->
      let r = Exp.ident (mk_lident "raise") in
      let args = map (fun x -> (Nolabel, build_expr x)) es in
      Exp.apply r args
   | MLE_Try (e, cs) ->
      Exp.try_ (build_expr e) (map build_case cs)

and resugar_app f args es: expression =
  match f.pexp_desc with
  | Pexp_ident x when x = try_with_ident () ->
    (* resugar try_with to a try...with
       try_with : (unit -> ML 'a) -> (exn -> ML 'a) -> ML 'a *)
    assert (length es == 2);
    let s, cs = BatList.first es, BatList.last es in
    (* We have FStar.All.try_with s cs, with s : unit -> ML 'a
     *                                  and  cs : exn -> ML 'a
     *
     * We need to create an OCaml try..with, with a body and a
     * set of cases for catching the exception.
     *
     * For the body, we simply translate `s ()` and we're done.
     *
     * For the cases, we can't a similar trick, so we try to reverse-engineer
     * the shape of the term in order to obtain a proper set. See get_variants. *)

    let body = Exp.apply (build_expr s) [(Nolabel, build_expr ml_unit)] in
    let variants = get_variants cs in
    Exp.try_ body variants

  | _ -> Exp.apply f args

and get_variants (e : mlexpr) : Parsetree.case list =
    match e.expr with
    | MLE_Fun ([{mlbinder_name=id}], e) ->
       (match e.expr with
        | MLE_Match ({expr = MLE_Var id'}, branches) when id = id' ->
           map build_case branches
        | _ ->
           [build_case (MLP_Var id, None, e)]
       )
    | _ -> failwith "Cannot resugar FStar.All.try_with (3)"

and build_seq args =
  match args with
  | [hd] -> build_expr hd
  | hd::tl -> Exp.sequence (build_expr hd) (build_seq tl)
  | [] -> failwith "Empty sequence should never happen"

and build_constructor_expr ((path, sym), exp): expression =
  let path', name =
    (match path, sym with
    | ["Prims"], "Cons" -> ([], "::")
    | ["Prims"], "Nil" -> ([], "[]")
    | path, x -> (path, x)) in
  match exp with
  | [] -> Exp.construct (path_to_ident(path', name)) None
  | [e] ->
     Exp.construct (path_to_ident(path', name)) (Some (build_expr e))
  | es ->
      let inner = Exp.tuple (map build_expr es) in
      Exp.construct (path_to_ident(path', name)) (Some inner)

and build_fun l e =
   match l with
   | ({mlbinder_name=id; mlbinder_ty=ty}::tl) ->
      let p = build_binding_pattern id in
      Exp.fun_ Nolabel None p (build_fun tl e)
   | [] -> build_expr e

and build_case ((lhs, guard, rhs): mlbranch): case =
  {pc_lhs = (build_pattern lhs);
   pc_guard = BatOption.map build_expr guard;
   pc_rhs = (build_expr rhs)}

and build_binding (toplevel: bool) (lb: mllb): value_binding =
  (* Add a constraint on the binding (ie. an annotation) for top-level lets *)
  let mk1 s = mkloc (String.sub s 1 (String.length s - 1)) none in
  let ty =
      match lb.mllb_tysc with
      | None -> None
      | Some ts ->
           if lb.print_typ && toplevel
           then let vars = List.map mk1 (ty_param_names (fst ts)) in
                let ty = snd ts in
                Some (build_core_type ~annots:vars ty)
           else None
  in
  let e = build_expr lb.mllb_def in
  let p = build_binding_pattern ?ty:ty lb.mllb_name in
  (Vb.mk p e)

let build_label_decl (sym, ty): label_declaration =
  Type.field (mk_sym sym) (build_core_type ty)

let build_constructor_decl (sym, tys): constructor_declaration =
  let tys = List.map snd tys in
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

let type_metadata (md : metadata): attributes option =
  let deriving = BatList.filter_map (function
    | PpxDerivingShow | PpxDerivingShowConstant _ -> Some "show"
    | PpxDerivingYoJson -> Some "yojson"
    | _ -> None
  ) md in
  if List.length deriving > 0 then
    let str = String.concat "," deriving in
    Some [ {
      attr_name = mk_sym "deriving";
      attr_payload = PStr [Str.eval (Exp.ident (mk_lident str))];
      attr_loc = no_location }
    ]
  else
    None

let add_deriving_const (md: metadata) (ptype_manifest: core_type option): core_type option =
  match List.filter (function PpxDerivingShowConstant _ -> true | _ -> false) md with
  | [PpxDerivingShowConstant s] ->
      let e = Exp.apply (Exp.ident (path_to_ident (["Format"], "pp_print_string"))) [(Nolabel, Exp.ident (mk_lident "fmt")); (Nolabel, Exp.constant (Const.string s))] in
      let deriving_const = {
        attr_name = mk_sym "printer";
        attr_payload = PStr [Str.eval (Exp.fun_ Nolabel None (build_binding_pattern "fmt") (Exp.fun_ Nolabel None (Pat.any ()) e))];
        attr_loc = no_location } in
      BatOption.map (fun x -> {x with ptyp_attributes=[deriving_const]}) ptype_manifest
  | _ -> ptype_manifest

let build_one_tydecl ({tydecl_name=x;
                       tydecl_ignored=mangle_opt;
                       tydecl_parameters=tparams;
                       tydecl_meta=attrs;
                       tydecl_defn=body}: one_mltydecl): type_declaration =
  let ptype_name = match mangle_opt with
    | Some y -> mk_sym y
    | None -> mk_sym x in
  let ptype_params = Some (map (fun sym -> Typ.mk (Ptyp_var (mk_typ_name sym)), (NoVariance, NoInjectivity)) (ty_param_names tparams)) in
  let (ptype_manifest: core_type option) =
    BatOption.map_default build_ty_manifest None body |> add_deriving_const attrs in
  let ptype_kind =  Some (BatOption.map_default build_ty_kind Ptype_abstract body) in
  let ptype_attrs = type_metadata attrs in
  Type.mk ?params:ptype_params ?kind:ptype_kind ?manifest:ptype_manifest ?attrs:ptype_attrs ptype_name

let build_tydecl (td: mltydecl): structure_item_desc option =
  let recf = Recursive in
  let type_declarations = map build_one_tydecl td in
  if type_declarations = [] then None else Some (Pstr_type (recf, type_declarations))

let build_exn (sym, tys): type_exception =
  let tys = List.map snd tys in
  let name = mk_sym sym in
  let args = Some (Pcstr_tuple (map build_core_type tys)) in
  let ctor = Te.decl ?args:args name in
  Te.mk_exception ctor

let build_module1 path (m1: mlmodule1): structure_item option =
  match m1.mlmodule1_m with
  | MLM_Ty tydecl ->
     (match build_tydecl tydecl with
      | Some t -> Some (Str.mk t)
      | None   -> None)
  | MLM_Let (flav, mllbs) ->
     let recf = match flav with | Rec -> Recursive | NonRec -> Nonrecursive in
     let bindings = map (build_binding true) mllbs in
     Some (Str.value recf bindings)
  | MLM_Exn exn -> Some (Str.exception_ (build_exn exn))
  | MLM_Top expr ->
      let lb = mk_top_mllb expr in
      let binding = build_binding true lb in
      Some (Str.value Nonrecursive [binding])
  | MLM_Loc (p, f) -> None

let build_m path (md: (mlsig * mlmodule) option) : structure =
  match md with
  | Some(s, m) ->
     let open_prims =
       Str.open_ (Opn.mk ?override:(Some Fresh) (Mod.ident (mk_lident "Prims"))) in
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
     let new_doc = FStarC_Extraction_ML_Code.doc_of_mllib ml in
     iter (fun (n, d) ->
         FStarC_Compiler_Util.write_file
           (FStarC_Find.prepend_output_dir (BatString.concat "" [n;ext]))
           (FStarC_Extraction_ML_Code.pretty (Prims.parse_int "120") d)
           ) new_doc
  | _ -> failwith "Unrecognized extension"
