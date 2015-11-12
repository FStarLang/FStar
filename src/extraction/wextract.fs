module FStar.Extraction.Wysteria.Extract

open FStar
open FStar.Util
open FStar.Absyn
open FStar.Absyn.Syntax
open FStar.Absyn.Print

open FStar.Extraction.ML.Env
open FStar.Extraction.ML.Syntax

type name = string

type wexp = string

type wtyp = string

type tlet =
    | Mk_tlet of (name * wtyp * wexp)

let fn_map: smap<(wexp * wexp * wexp)> = smap_create 10

type wys_lib_fn = {
    fn_name:string;
    rem_args:int;
    arity:int;
    extracted_fn_name:string
}

let to_wys_lib_fn s1 n1 n2 s2 = { fn_name=s1; rem_args=n1; arity=n2; extracted_fn_name=s2 }

let wys_lib_args_map :smap<wys_lib_fn> = smap_create 10

let prims_trans_map :smap<string> = smap_create 10

let slice_id = "slice_id"
let compose_ids = "compose_ids"
let slice_id_sps = "slice_id_sps"

let initialize (_:unit) :unit =
    Util.smap_add fn_map "Prims.int" (slice_id, compose_ids, slice_id_sps);
    Util.smap_add fn_map "Prims.nat" (slice_id, compose_ids, slice_id_sps);
    Util.smap_add fn_map "Prims.list" ("slice_list", "compose_lists", "slice_list_sps");
    Util.smap_add fn_map "Prims.option" ("slice_option", "compose_options", "slice_option_sps");
    Util.smap_add fn_map "Prims.Tuple2" ("slice_tuple", "compose_tuples", "slice_tuple_sps");

    Util.smap_add wys_lib_args_map "as_par" (to_wys_lib_fn "as_par" 0 2 "mk_aspar");
    Util.smap_add wys_lib_args_map "as_sec" (to_wys_lib_fn "as_sec" 0 2 "mk_assec");
    Util.smap_add wys_lib_args_map "unbox_p" (to_wys_lib_fn "unbox_p" 1 1 "mk_unbox");
    Util.smap_add wys_lib_args_map "unbox_s" (to_wys_lib_fn "unbox_s" 1 1 "mk_unbox");
    Util.smap_add wys_lib_args_map "box" (to_wys_lib_fn "box" 0 2 "mk_box");
    Util.smap_add wys_lib_args_map "mkwire_p" (to_wys_lib_fn "mkwire_p" 1 2 "mk_mkwire");
    Util.smap_add wys_lib_args_map "mkwire_s" (to_wys_lib_fn "mkwire_s" 0 2 "mk_mkwire");
    Util.smap_add wys_lib_args_map "projwire_p" (to_wys_lib_fn "projwire_p" 1 2 "mk_projwire");
    Util.smap_add wys_lib_args_map "projwire_s" (to_wys_lib_fn "projwire_s" 1 2 "mk_projwire");
    Util.smap_add wys_lib_args_map "concat_wire" (to_wys_lib_fn "concat_wire" 2 2 "mk_concatwire");

    Util.smap_add prims_trans_map "Prims.op_Multiply" "Prims.( * )";
    Util.smap_add prims_trans_map "Prims.op_Subtraction" "Prims.(-)";
    Util.smap_add prims_trans_map "Prims.op_Addition" "Prims.(+)";
    Util.smap_add prims_trans_map "Prims.op_LessThanOrEqual" "Prims.(<=)";
    Util.smap_add prims_trans_map "Prims.op_GreaterThan" "Prims.(>)";
    Util.smap_add prims_trans_map "Prims.op_GreaterThanOrEqual" "Prims.(>=)";
    Util.smap_add prims_trans_map "Prims.op_LessThan" "Prims.(<)";
    Util.smap_add prims_trans_map "Prims.op_Modulus" "Prims.(%)";

    ()

let lookup_ffi_map (t:string) :(wexp * wexp * wexp) =
    let m = smap_try_find fn_map t in
    match m with
        | Some m -> m
        | _ -> failwith ("Unknown user type: " ^ t)

let lookup_wys_lib_map (s:string) :wys_lib_fn =
    match (smap_try_find wys_lib_args_map s) with
        | Some x -> x
        | _ -> failwith "Unknown wysteria library function"

let translate_ffi_name (s:string) :string =
    match (smap_try_find prims_trans_map s) with
        | Some x -> x
        | None   -> s

let rec sublist (s:string) (l:list<'a>) (n:int) =
    if n > List.length l then failwith (Util.format3 "Error removing arguments in sublist for %s, list len is %s, n is %s " s (Util.string_of_int (List.length l)) (Util.string_of_int n))
    else if n = 0 then l
    else sublist s (List.tl l) (n - 1)

let is_bool (t:mlty) =
    match t with
        | MLTY_Named (_, p) -> string_of_mlpath p = "Prims.bool"
        | _ -> false

let is_int (t:mlty) =
    match t with
        | MLTY_Named (_, p) -> string_of_mlpath p = "Prims.int"
        | _ -> false

let is_unit (t:mlty) =
    match t with
        | MLTY_Named (_, p) -> string_of_mlpath p = "Prims.unit"
        | _ -> false

let is_prin (t:mlty) =
    match t with
        | MLTY_Named (_, p) -> string_of_mlpath p = "Prins.prin"
        | _ -> false

let is_prins (t:mlty) =
    match t with
        | MLTY_Named (_, p) -> string_of_mlpath p = "Prins.prins"
        | _ -> false

let is_eprins (t:mlty) =
    match t with
        | MLTY_Named (_, p) -> string_of_mlpath p = "Prins.eprins"
        | _ -> false

let is_box (t:mlty) =
    match t with
        | MLTY_Named (_, p) -> string_of_mlpath p = "Wysteria.Box"
        | _ -> false

let is_wire (t:mlty) =
    match t with
        | MLTY_Named (_, p) -> string_of_mlpath p = "Wysteria.Wire"
        | _ -> false

let box_content_type (t:mlty) :mlty =
    match t with
        | MLTY_Named (l, p) ->
            if string_of_mlpath p = "Wysteria.Box" then List.hd l
            else failwith "Cannot get content for non box named type"
        | _ -> failwith "Cannot get content for non-named type"

let wire_content_type (t:mlty) :mlty =
    match t with
        | MLTY_Named (l, p) ->
            if string_of_mlpath p = "Wysteria.Wire" then List.hd l
            else failwith "Cannot get content for non wire named type"
        | _ -> failwith "Cannot get content for non-named type"

let is_wysteria_type (t:mlty) = is_prin t || is_prins t || is_eprins t || is_box t || is_wire t

let slice_value = "Semantics.slice_v_ffi"
let slice_value_sps = "Semantics.slice_v_sps_ffi"
let compose_values = "Semantics.compose_vals_ffi"

let rec get_opaque_fns (t:mlty) :(wexp * wexp * wexp) =
    if is_bool t || is_unit t || is_prin t || is_prins t || is_eprins t then slice_id, compose_ids, slice_id_sps
    else if is_box t || is_wire t then slice_value, compose_values, slice_value_sps
    else
        match t with
            | MLTY_Named ([], p)   -> lookup_ffi_map (string_of_mlpath p)
            | MLTY_Named (args, p) ->
                let e1, e2, e3 = get_opaque_fns (MLTY_Named ([], p)) in
                List.fold_left (fun (a1, a2, a3) arg ->
                    match arg with
                        | MLTY_Named _ ->
                            let e1_arg, e2_arg, e3_arg = get_opaque_fns arg in
                            "(" ^ a1 ^ " " ^ e1_arg ^ ")", "(" ^ a2 ^ " " ^ e2_arg ^ ")", "(" ^ a3 ^ " " ^ e3_arg ^ ")"
                        | _ -> failwith "Did not expect type argument to be something other than named type"
                ) (e1, e2, e3) args
            | _ -> failwith "Did not expect a non named type in get_opaque_fns"

let get_injection (t:mlty) :string =
    let s = "fun x -> " in
    let s' =
        if is_bool t then "D_v (const_meta, V_bool x)"
        else if is_unit t then "D_v (const_meta, V_unit)"
        else if is_prin t then "D_v (const_meta, V_prin x)"
        else if is_prins t || is_eprins t then "D_v (const_meta, V_eprins x)"
        else if is_box t || is_wire t then "x"
        else
            let s1, s2, s3 = get_opaque_fns t in
            "mk_v_opaque x " ^ s1 ^ " " ^ s2 ^ " " ^ s3
    in
    s ^ s'

let is_known_named_type (t:mlty) :bool =
    match t with
        | MLTY_Named (_, p) ->
            let s_opt = smap_try_find fn_map (string_of_mlpath p) in
            if s_opt = None then false else true
        | _ -> failwith "Is_known_named_type was not called with a named type"

let name_to_string (s:name) = "\"" ^ s ^ "\""

let rec mlty_to_typ (t:mlty) :string =
    if is_bool t then "T_bool"
    else if is_unit t then "T_unit"
    else if is_prin t then "T_prin"
    else if is_prins t then "T_eprins"
    else if is_box t then "T_box (" ^ (mlty_to_typ (box_content_type t)) ^ ")"
    else if is_wire t then "T_wire (" ^ (mlty_to_typ (wire_content_type t)) ^ ")"
    else
        match t with
            | MLTY_Named (l, p) ->
                let n = "T_cons (" ^ (name_to_string (string_of_mlpath p)) in
                let args = List.fold_left (fun s a -> s ^ " (" ^ (mlty_to_typ a) ^ ");") "" l in        
                n ^ ", [" ^ args ^ "])"
            | _ -> "T_unknown"
   
let get_constant_injection (t:mlty) (x:string) :string =
    if is_bool t then "C_bool " ^ x
    else if is_unit t then "C_unit ()"
    else if is_known_named_type t then
        "C_opaque ((), Obj.magic " ^ x ^ ", " ^ mlty_to_typ t ^ ")"
    else failwith "Constant injection does not support this type"

let is_ffi ({expr = e; ty = t}:mlexpr) :(bool * string) =
    match e with
        | MLE_Name (p, n) -> ((p = ["FFI"] || p = ["Prims"]), translate_ffi_name (string_of_mlpath (p, n)))
        | _ -> (false, "")

let tag_of_mlconst (c:mlconstant) :string =
    match c with
        | MLC_Unit -> "MLC_Unit"
        | MLC_Bool _ -> "MLC_Bool"
        | MLC_Char _ -> "MLC_Char"
        | MLC_Byte _ -> "MLC_Byte"
        | MLC_Int32 _ -> "MLC_Int32"
        | MLC_Int64 _ -> "MLC_Int64"
        | MLC_Int _ -> "MLC_Int"
        | MLC_Float _ -> "MLC_Float"
        | MLC_Bytes _ -> "MLC_Bytes"
        | MLC_String _ -> "MLC_String"

let extract_mlconst (c:mlconstant) :wexp =
    match c with
        | MLC_Unit    -> "C_unit ()"
        | MLC_Bool b  -> "C_bool " ^ (if b then "true" else "false")
        | MLC_Int32 n -> "C_opaque ((), Obj.magic " ^ (Util.string_of_int32 n) ^ ", T_cons (\"Prims.int\", []))"
        | MLC_Int64 n -> "C_opaque ((), Obj.magic " ^ (Util.string_of_int64 n) ^ ", T_cons (\"Prims.int\", []))"
        | MLC_Int x   -> "C_opaque ((), Obj.magic " ^ x ^ ", T_cons (\"Prims.int\", []))"
        | MLC_String s -> "C_opaque ((), Obj.magic (\"" ^ s ^ "\"), T_unknown)"
        | _           -> failwith ("Unsupported constant: tag: " ^ (tag_of_mlconst c))

let is_wys_lib_fn ({expr = e; ty = t}:mlexpr) :bool =
    match e with
        | MLE_Name p -> Util.starts_with (string_of_mlpath p) "Wysteria"
        | _ -> false

let check_pats_for_bool (l:list<(mlpattern * option<mlexpr> * mlexpr)>) :(bool * mlexpr * mlexpr) =
    let def = false, ml_unit, ml_unit in
    if List.length l <> 2 then def
    else
        let (p1, _, e1) = List.hd l in
        let (p2, _, e2) = List.hd (List.tl l) in
        match (p1, p2) with
            | (MLP_Const (MLC_Bool _), MLP_Const (MLC_Bool _)) -> true, e1, e2
            | _ -> def

let mk_var (s:string) (t:mlty) :wexp =
    "mk_var " ^ name_to_string s ^ " (" ^ mlty_to_typ t ^ ")"

let mk_varname (s:string) (t:mlty) :wexp =
    "mk_varname " ^ name_to_string s ^ " (" ^ mlty_to_typ t ^ ")"

let rec extract_mlexp ({expr = e; ty = t}:mlexpr) :wexp =
    match e with
        | MLE_Const c          -> "mk_const (" ^ extract_mlconst c ^ ")"
        | MLE_Var x            -> mk_var (idsym x) t
        | MLE_Name (p, s)      ->
            let ss = string_of_mlpath (p, s) in
            let _ =
                if not (Util.starts_with ss "SMC.") then
                    Util.print_string (Util.format1 "Warning: name not applied: %s\n" (string_of_mlpath (p, s)))
                else ()
            in
            mk_var s t
        | MLE_Let ((b, l), e') ->
            if b then failwith "Nested recursive lets are not supported yet"
            else
                let lb = List.hd l in
                let lbname = idsym lb.mllb_name in
                let lbbody = lb.mllb_def in
                "mk_let (" ^ (mk_varname lbname lbbody.ty) ^ ") (" ^ extract_mlexp lbbody ^ ") (" ^ extract_mlexp e' ^ ")"
        | MLE_App (f, args)    ->
            let b, ffi = is_ffi f in
            if b then
                let inj = get_injection t in
                let args_exp = List.fold_left (fun s a -> s ^ " (" ^ (extract_mlexp a) ^ ");") "" args in
                "mk_ffi " ^ (string_of_int (List.length args)) ^ " " ^ name_to_string ffi ^ " (" ^ ffi ^ ") [ " ^ args_exp ^ " ] (" ^ inj ^ ")"
            else if is_wys_lib_fn f then extract_wysteria_specific_ast f args t
            else
                let s = extract_mlexp f in
                if s = "_assert" then "mk_const (C_unit ())"  // ?
                else List.fold_left (fun s a -> "mk_app (" ^ s ^ ") (" ^ extract_mlexp a ^ ")") s args
        | MLE_Fun (bs, body) ->
            let body_str = extract_mlexp body in
            List.fold_left (fun s ((b, _), t) -> "mk_abs (" ^ mk_varname b t ^ ") (" ^ s ^ ")") body_str (List.rev bs)
        | MLE_Match (e, bs) ->
            let b, e1, e2 = check_pats_for_bool bs in
            if b then
                "mk_cond (" ^ (extract_mlexp e) ^ ") (" ^ extract_mlexp e1 ^ ") (" ^ extract_mlexp e2 ^ ")"
            else failwith "Only if-then-else patterns are supported"
        | MLE_Coerce (e, _, _) -> extract_mlexp e
        | MLE_If (e, e1, e2_opt) ->            
            (match e2_opt with
                | None    -> failwith "If Then Else should have an else branch?"
                | Some e2 ->
                    "mk_cond (" ^ (extract_mlexp e) ^ ") (" ^ extract_mlexp e1 ^ ") (" ^ extract_mlexp e2 ^ ")")
        | _ -> failwith "This expression extraction is not supported yet"

and extract_wysteria_specific_ast ({expr=f; ty=_}:mlexpr) (args:list<mlexpr>) (t:mlty) :string =  // t is the original expression type that called this function (the immediate parent app node)
    match f with
        | MLE_Name (_, s) ->
            if s = "main" then
                let f = List.hd (List.tl args) in
                let f_exp = extract_mlexp f in
                "mk_app (" ^ f_exp ^ ") (E_const (C_unit ()))"
            else if s = "w_read_int" then
                let inj_str = get_injection t in
                "mk_ffi 1 \"FFI.read_int\" FFI.read_int [ E_const (C_unit ()) ] (" ^  inj_str ^ ")"
            else if s = "w_read_int_tuple" then
                let inj_str = get_injection t in
                "mk_ffi 1 \"FFI.read_int_tuple\" FFI.read_int_tuple [ E_const (C_unit ()) ] (" ^  inj_str ^ ")"
            else if s = "w_read_int_list" then
                let inj_str = get_injection t in
                "mk_ffi 1 \"FFI.read_int_list\" FFI.read_int_list [ E_const (C_unit ()) ] (" ^  inj_str ^ ")"
            else
                let r = lookup_wys_lib_map s in
                let args = sublist s args r.rem_args in
                List.fold_left (fun acc arg -> acc ^ " (" ^ extract_mlexp arg ^ ")") r.extracted_fn_name args
        
        | _ -> failwith "Expected wysteria lib fn to be a MLE_Name"

let extract_mllb ((b, l):mlletbinding) :tlet =
    if List.length l <> 1 then failwith "Mutually recursive lets are not yet suppored"
    else
        let lb = List.hd l in
        let lbname = idsym lb.mllb_name in
        let lbbody = lb.mllb_def in

        if b then
            match lbbody.expr with
                | MLE_Fun (bs, e) ->
                    let first_b, rest_bs = List.hd bs, List.tl bs in
                    let body_exp = extract_mlexp e in
                    let tl_abs_exp = List.fold_left (fun e (bname, btyp) -> "mk_abs (" ^ mk_varname (idsym bname) btyp ^ ") (" ^ e ^ ")") body_exp (List.rev rest_bs) in
                    let fix_exp = "mk_fix (" ^ mk_varname lbname lbbody.ty ^ ") (" ^ mk_varname (idsym (fst first_b)) (snd first_b) ^ ") (" ^ tl_abs_exp ^ ")" in
                    Mk_tlet (lbname, (mlty_to_typ lbbody.ty), fix_exp)
                | _ -> failwith "Recursive let binding is not an abstraction ?"
        else
            Mk_tlet (lbname, (mlty_to_typ lbbody.ty), extract_mlexp lbbody)

let extract_mlmodule (m:mlmodule) :(list<tlet> * option<wexp>) =
    List.fold_left (fun (l, top_opt)  tld ->
        match tld with
            | MLM_Ty _   -> (l, top_opt)
            | MLM_Exn _  -> failwith "Cannot extract an exception"
            | MLM_Let lb -> (l @ [ extract_mllb lb ], top_opt)
            | MLM_Top e  ->
                match top_opt with
                    | None   ->  (l, Some (extract_mlexp e))
                    | Some _ -> failwith "Impossible: more than one top expressions"
    ) ([], None) m

let rec find_smc_module (mllibs:list<mllib>) :option<mlmodule> =
    let rec find_smc_module' (mllib:list<(mlsymbol * option<(mlsig * mlmodule)> * mllib)>) :option<mlmodule> =
        match mllib with
            | []                               -> None
            | (x, mlsig_opt, MLLib mllib')::tl ->
                if x = "SMC" then
                    (match mlsig_opt with
                        | Some (_, m) -> Some m
                        | None        -> raise (NYI "Found the SMC module name but no module"))
                else
                    let m_opt = find_smc_module' mllib' in
                    match m_opt with
                        | Some m -> Some m
                        | None   -> find_smc_module' tl
    in

    match mllibs with
        | []            -> None
        | (MLLib s)::tl ->
            let m_opt = find_smc_module' s in
            match m_opt with
                | Some m -> Some m
                | None   -> find_smc_module tl

let mltyp_to_string (t:mlty) :string =
    match t with
        | MLTY_Named (_, p) -> string_of_mlpath p
        | _ -> "Something other than named type"

let rec get_iface_arg_ret_typ (t:mlty) :(mlty * mlty) =
    match t with
        | MLTY_Fun (arg, _, ret) ->
            (match ret with
                | MLTY_Fun (_, _, _) -> get_iface_arg_ret_typ ret
                | _ -> (arg, ret))
        | _ -> failwith "Get wys arg ret type has a non-arrow type" 

let extract_smc_exports (g:env) :string =
    List.fold_left (fun s b ->
        match b with
            | Fv (fvv, _, t) ->
                if Util.starts_with fvv.v.str "Smciface" then
                    let fn_name = fvv.v.ident.idText in
                    let (arg, ret) = get_iface_arg_ret_typ (snd t) in
                    let arg_inj = get_constant_injection arg "x" in

                    let s0 = "let " ^ fn_name ^ " ps p x = \n" in
                    let s1 = "let e1 = mk_const (C_eprins ps) in\n" in
                    let s2 = "let e2 = mk_mkwire (mk_const (C_eprins (singleton p))) (mk_box (mk_const (C_eprins (singleton p))) (mk_const (" ^ arg_inj ^ "))) in\n" in
                    let s3 = "let dv = Interpreteriface.run p \"" ^ fn_name ^ "\" " ^ (mlty_to_typ (snd t)) ^ " [e1; e2] in\n"
                    let s4 = "Obj.magic (Interpreteriface.project_value_content dv)\n"
                    s ^ (s0 ^ s1 ^ s2 ^ s3 ^ s4) ^ "\n\n"
                    // let wire_arg = "mk_mkwire (mk_const (C_prin p)) (mk_box (mk_const (C_prins (singleton p))) ((" ^ arg_inj ^ ") x))" in
                    // let s' = "let " ^ fn_name ^ " ps p x = project_value_content (Interpreter.run p \"" ^ fn_name ^ "\" " ^
                    //          "[mk_const (C_eprins ps); (" ^ wire_arg ^ ")])" in
                    // s ^ s' ^ "\n\n"
                else s
            | _ -> s
    ) "" g.gamma
                    
let extract (l:list<modul>) (en:FStar.Tc.Env.env) :unit =
    initialize ();
    let c, mllibs = Util.fold_map Extraction.ML.ExtractMod.extract (Extraction.ML.Env.mkContext en) l in
    let s_exports = extract_smc_exports c in
    let mllibs = List.flatten mllibs in
    let m_opt = find_smc_module mllibs in
    let s_smc =
        (match m_opt with
            | Some m ->
                let l, m_opt = extract_mlmodule m in
                List.fold_left (fun s (Mk_tlet (n, t, b)) -> s ^ "(" ^ name_to_string n ^ ", (" ^ t ^ "), (" ^ b ^ "));\n") "" l
            | _ -> "")
    in
    let smciface = Util.open_file_for_writing (Options.prependOutputDir "smciface.ml") in
    Util.append_to_file smciface "open Ffibridge";
    Util.append_to_file smciface "open FFI";
    Util.append_to_file smciface "open AST";
    Util.append_to_file smciface "\n";
    Util.append_to_file smciface s_exports;
    Util.close_file smciface;

    let prog = Util.open_file_for_writing (Options.prependOutputDir "prog.ml") in
    Util.append_to_file prog "open AST";
    Util.append_to_file prog "open FFI";
    Util.append_to_file prog "\n";
    Util.append_to_file prog "let const_meta = Meta ([], Can_b, [], Can_w)";
    Util.append_to_file prog "\n";
    Util.append_to_file prog ("let program = [\n" ^ s_smc ^ "]");
    Util.close_file prog

    // match m_opt with
    //     | None   -> failwith "End of SMC module, no top level expression"
    //     | Some m ->
    //         let s = List.fold_left (fun acc (Mk_tlet (n, t, b)) -> "mk_let (mk_varname " ^ (name_to_string n) ^ " (" ^ t ^ ")) (" ^ b ^ ") (" ^ acc ^ ")") m (List.rev l) in
    //         Util.print_string s; Util.print_string "\n"
