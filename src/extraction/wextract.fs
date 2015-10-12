module FStar.Extraction.Wysteria.Extract

open FStar
open FStar.Util
open FStar.Absyn
open FStar.Absyn.Syntax
open FStar.Absyn.Print

exception NYI of string

type ffi_type_s = {
    module_name: string;
    type_name: string;
    slice_fn_n: string;
    compose_fn_n: string;
    slice_sps_fn_n: string;
}

let slice_id = "slice_id"
let compose_ids = "compose_ids"
let slice_id_sps = "slice_id_sps"

(* TODO: check that all these types are of kind Type or Type -> Type or Type -> Type -> Type *)

let ffi_types = [ { module_name="Prims"; type_name="int"; slice_fn_n=slice_id; compose_fn_n=compose_ids; slice_sps_fn_n=slice_id_sps; };
                  { module_name="Prims"; type_name="nat"; slice_fn_n=slice_id; compose_fn_n=compose_ids; slice_sps_fn_n=slice_id_sps; };
                  { module_name="Prims"; type_name="list"; slice_fn_n="slice_list"; compose_fn_n="compose_lists"; slice_sps_fn_n="slice_list_sps"; };
                  { module_name="Prims"; type_name="option"; slice_fn_n="slice_option"; compose_fn_n="compose_options"; slice_sps_fn_n="slice_option_sps"; }
                  { module_name="Prims"; type_name="Tuple2"; slice_fn_n="slice_tuple"; compose_fn_n="compose_tuples"; slice_sps_fn_n="slice_tuple_sps"; }
                ]

let mk_fn_exp (s:string) :exp = mk_Exp_fvar ({ v = { ns = []; ident = { idText = s; idRange = dummyRange }; nsstr = ""; str = s }; sort = mk_Typ_unknown; p = dummyRange }, None) None dummyRange

let slice_value_exp = mk_fn_exp "slice_value"
let slice_value_sps_exp = mk_fn_exp "slice_value_sps"
let compose_values_exp = mk_fn_exp "compose_vals"

type fn_mapping = {
    slice_fn: exp;
    compose_fn: exp;
    slice_sps_fn: exp;
}

let fn_map: smap<fn_mapping> = smap_create (List.length ffi_types)

let initialize (_:unit) :unit =
    List.iter (fun r ->
               let n = r.module_name ^ "." ^ r.type_name in
               let fns = { slice_fn = mk_fn_exp r.slice_fn_n; compose_fn = mk_fn_exp r.compose_fn_n; slice_sps_fn = mk_fn_exp r.slice_sps_fn_n; } in
               Util.smap_add fn_map n fns
              ) ffi_types

let rec pre_process_t (t:typ) =
    let t' = Util.compress_typ t in
    match t'.n with
        | Typ_refine (xt, _) -> pre_process_t xt.sort
        | _ -> t'
    
// before calling these is_ functions, the caller must normalize the type
let is_bool (t:typ) =
    match (pre_process_t t).n with
        | Typ_const ftv -> ftv.v.str = "Prims.bool"
        | _ -> false

let is_unit (t:typ) =
    match (pre_process_t t).n with
        | Typ_const ftv -> ftv.v.str = "Prims.unit"
        | _ -> false

let is_prin (t:typ) =
    match (pre_process_t t).n with
        | Typ_const ftv -> ftv.v.str = "Prins.prin"
        | _ -> false

let is_ordset (t:typ) =
    match (pre_process_t t).n with
        | Typ_const ftv -> ftv.v.str = "FStar.OrdSet.ordset"
        | _ -> false

let is_p_cmp (e:exp) =
    match (Util.compress_exp e).n with
        | Exp_fvar (fvv, _) -> fvv.v.str = "Prins.p_cmp"
        | _ -> false

let is_prins (t:typ) =
    match (pre_process_t t).n with
        | Typ_app (t', [ (Inl t'', _); (Inr f, _) ]) -> is_ordset t' && is_prin t'' && is_p_cmp f
        | _ -> false

let is_eprins = is_prins

let is_box' (t:typ) =
    match (pre_process_t t).n with
        | Typ_const ftv -> ftv.v.str = "Wysteria.Box"
        | _ -> false

let is_box (t:typ) =
    match (pre_process_t t).n with
        | Typ_app (t', _) -> is_box' t'
        | _ -> false

let is_wire' (t:typ) =
    match (pre_process_t t).n with
        | Typ_const ftv -> ftv.v.str = "Wysteria.Wire"
        | _ -> false

let is_wire (t:typ) =
    match (pre_process_t t).n with
        | Typ_app (t', _) -> is_wire' t'
        | _ -> false

let is_wysteria_type (t:typ) = is_prin t || is_prins t || is_eprins t || is_box t || is_wire t

let lookup_ffi_map (t:string) :(exp * exp * exp) =
    let m = smap_try_find fn_map t in
    match m with
        | Some m -> m.slice_fn, m.compose_fn, m.slice_sps_fn
        | _ -> Util.print_string ("Error in looking up ffi type: " ^ t); raise (NYI ("Error in looking up ffi type: " ^ t))

// assume type is normalized already
let rec get_opaque_fns (t:typ) :(exp * exp * exp) =
    if is_bool t || is_unit t || is_prin t || is_prins t || is_eprins t then mk_fn_exp slice_id, mk_fn_exp compose_ids, mk_fn_exp slice_id_sps
    else if is_box t || is_wire t then slice_value_exp, compose_values_exp, slice_value_sps_exp
    else
        match (pre_process_t t).n with
            | Typ_const ftv -> lookup_ffi_map (ftv.v.str)
            | Typ_app (t, args) ->
                let e1, e2, e3 = get_opaque_fns t in
                List.fold_left (fun (acc1, acc2, acc3) arg ->
                           match arg with
                            | Inl t', _ ->
                                let e1', e2', e3' = get_opaque_fns t' in
                                let e1'_arg, e2'_arg, e3'_arg = (Inr e1', None), (Inr e2', None), (Inr e3', None)  in
                                (mk_Exp_app (acc1, [e1'_arg]) None dummyRange), (mk_Exp_app (acc2, [e2'_arg]) None dummyRange), (mk_Exp_app (acc3, [e3'_arg]) None dummyRange)
                            | _ -> raise (NYI "Unexpected type argument: an expression")
                           ) (e1, e2, e3) args
            | _ -> raise (NYI "Unexpected type in get slice fn")

let get_injection (t:typ) :string =
    let s = "fun x -> " in
    let s' =
        if is_bool t then "V_bool x"
        else if is_unit t then "V_unit"
        else if is_prin t then "V_prin x"
        else if is_prins t then "V_prins x"
        else if is_eprins t then "V_eprins x"
        else if is_box t || is_wire t then "x"
        else
            let e1, e2, e3 = get_opaque_fns t in
            let s1, s2, s3 = exp_to_string e1, exp_to_string e2, exp_to_string e3 in
            "mk_v_opaque x " ^ s1 ^ " " ^ s2 ^ " " ^ s3
    in
    s ^ s'

let filter_out_type_binders = List.filter (fun a -> match a with | Inl _, _ -> false | Inr _, _ -> true)

let filter_out_type_args = List.filter (fun a -> match a with | Inl _, _ -> false | Inr _, _ -> true)

let name_to_string (s:string) :string = "\"" ^ s ^ "\""

let extract_binder (b:binder) :string =
    match b with
        | Inl _, _    -> raise (NYI ("Extract binder cannot extract type arguments"))
        | Inr bvar, _ -> name_to_string bvar.v.ppname.idText

let extract_const (c:sconst) :string =
    match c with
        | Const_unit    -> "C_unit ()"
        | Const_bool b  -> "C_bool " ^ (if b then "true" else "false")
        | Const_int32 n -> "C_opaque " ^ (Util.string_of_int32 n)
        | Const_int x   -> "C_opaque " ^ x

        | _             -> raise (NYI "Extract constant cannot extract the constant")

let typ_of_exp (e:exp) :typ =
    let t' = !(Util.compress_exp e).tk in
    match t' with
        | Some t -> t
        | _ -> raise (NYI "Type of FFI call not set!")

let is_ffi (e:exp) :(bool * string) =
    match (Util.compress_exp e).n with
        | Exp_fvar (fvv, _) ->
            if Util.starts_with fvv.v.str "FFI." || Util.starts_with fvv.v.str "Prims." then (true, fvv.v.str) else (false, "")
        | _ -> (false, "")

let check_pats_for_bool (l:list<(pat * option<exp> * exp)>) :(bool * exp * exp) =
    let c_unit = mk_Exp_constant Const_unit None dummyRange in
    let def = false, c_unit, c_unit in
    if List.length l <> 2 then def
    else
        let (p1, _, e1) = List.hd l in
        let (p2, _, e2) = List.hd (List.tl l) in
        match (p1.v, p2.v) with
            | (Pat_constant (Const_bool _), Pat_constant (Const_bool _)) -> true, e1, e2
            | _ -> def

let rec extract_exp (e:exp) en :string =
    match (Util.compress_exp e).n with
        | Exp_bvar bvar          -> "mk_var " ^ (name_to_string bvar.v.ppname.idText)
        | Exp_fvar (fvar, _)     -> "mk_var " ^ (name_to_string fvar.v.ident.idText) // TODO: check here that fvar is not an FFI or Wysteria function, they should only be applied and hence handled in Exp_app
                                                                                    // another way may be to check that fvar is from current SMC module only
        | Exp_constant c         -> "mk_const (" ^ extract_const c ^ ")"
        | Exp_abs (bs, e)        ->
            let body_str = extract_exp e en in
            let bs = filter_out_type_binders bs in
            List.fold_left (fun s b -> "mk_abs " ^ (extract_binder b) ^ " (" ^ s ^ ")") body_str (List.rev bs)
        | Exp_app (e', args)      ->
            let args = filter_out_type_args args in
            let b, ffi = is_ffi e' in
            if b then
                let t = FStar.Tc.Normalize.normalize en (typ_of_exp e) in
                let inj = get_injection t in
                let args_str = List.fold_left (fun s a -> s ^ " (" ^  (extract_arg a en) ^ ");") "" args in
                "mk_ffi " ^ (string_of_int (List.length args)) ^ " (" ^  ffi ^ ") [ " ^ args_str ^ " ] (" ^ inj ^ ")"
            else
                let s = extract_exp e' en in
                let b, s' = extract_wysteria_specific_ast s args e en in
                if b then s'
                else
                    if s = "_assert" then "mk_const (C_unit ())"  // ?
                    else
                        List.fold_left (fun s a -> "mk_app (" ^ s ^ ") (" ^ extract_arg a en ^ ")") s args
        | Exp_match (e, pats)    ->
            let b, e1, e2 = check_pats_for_bool pats in
            if b then
                "mk_cond (" ^ (extract_exp e en) ^ ") (" ^ extract_exp e1 en ^ ") (" ^ extract_exp e2 en ^ ")"
            else raise (NYI ("Only boolean patterns are supported"))
        | Exp_ascribed (e, _, _) -> extract_exp e en
        | Exp_let (lbs, e)       ->
            if fst lbs then raise (NYI "Recursive let not expected (only top level)")
            else
                let lb = List.hd (snd lbs) in
                "mk_let " ^ name_to_string (lbname_to_string lb.lbname) ^ " (" ^ extract_exp lb.lbdef en ^ ") (" ^ extract_exp e en ^ ")"
        | _ -> Util.print_string ("Expression not expected " ^ (tag_of_exp e)); raise (NYI "")

and extract_wysteria_specific_ast (s:string) (args:list<arg>) (e:exp) en :(bool * string) =  // e is the original expression that called this function
    if s = "mk_var \"main\"" then
        let f = List.hd (List.tl args) in
        let s =
            match f with
                | Inl _, _ -> raise (NYI ("Main 2nd argument not expected to be a type argument"))
                | Inr f, _ -> extract_exp (mk_Exp_app (f, [varg (mk_Exp_constant Const_unit None dummyRange)]) None dummyRange) en
        in
        true, s
    else
        match s with  // TODO: check that wysteria functions are not FFI functions (this will be checked with the check in Exp_fvar case above)
            | "mk_var \"as_par\"" ->
                let a1 = List.hd args in
                let a2 = List.hd (List.tl args) in
                true, "mk_aspar (" ^ extract_arg a1 en ^ ") (" ^ extract_arg a2 en ^ ")"
            | "mk_var \"as_sec\"" ->
                let a1 = List.hd args in
                let a2 = List.hd (List.tl args) in
                true, "mk_assec (" ^ extract_arg a1 en ^ ") (" ^ extract_arg a2 en ^ ")"
            | "mk_var \"box\"" -> 
                let a1 = List.hd args in
                let a2 = List.hd (List.tl args) in
                true, "mk_box (" ^ extract_arg a1 en ^ ") (" ^ extract_arg a2 en ^ ")"
            | "mk_var \"unbox_p\""
            | "mk_var \"unbox_s\"" ->
                let a = List.hd (List.tl args) in  // first argument is an implicit
                true, "mk_unbox (" ^ extract_arg a en ^ ")"
            | "mk_var \"mkwire_s\"" ->
                let a1 = List.hd args in
                let a2 = List.hd (List.tl args) in
                true, "mk_mkwire (" ^ extract_arg a1 en ^ ") (" ^ extract_arg a2 en ^ ")"
            | "mk_var \"mkwire_p\"" ->
                let a1 = List.hd (List.tl args) in
                let a2 = List.hd (List.tl (List.tl args)) in
                true, "mk_mkwire (" ^ extract_arg a1 en ^ ") (" ^ extract_arg a2 en ^ ")"  // first argument is implicit
            | "mk_var \"projwire_p\""
            | "mk_var \"projwire_s\"" ->
                let a1 = List.hd (List.tl args) in
                let a2 = List.hd (List.tl (List.tl args)) in
                true, "mk_projwire (" ^ extract_arg a1 en ^ ") (" ^ extract_arg a2 en ^ ")"  // first argument is implicit
            | "mk_var \"concat_wire\"" ->
                let a1 = List.hd (List.tl (List.tl args)) in
                let a2 = List.hd (List.tl (List.tl (List.tl args))) in
                true, "mk_concatwire (" ^ extract_arg a1 en ^ ") (" ^ extract_arg a2 en ^ ")"  // first two arguments are implicit
            | "mk_var \"w_read_int\"" ->
                let t = FStar.Tc.Normalize.normalize en (typ_of_exp e) in  // TODO: I am pusing this call only at FFI nodes, else gives an error in typ_of_exp
                let inj_str = get_injection t in
                true, "mk_ffi 1 FFI.read_int [ E_const (C_unit ()) ] (" ^  inj_str ^ ")"
            | "mk_var \"w_read_int_tuple\"" ->
                let t = FStar.Tc.Normalize.normalize en (typ_of_exp e) in
                let inj_str = get_injection t in
                true, "mk_ffi 1 FFI.read_int_tuple [ E_const (C_unit ()) ] (" ^  inj_str ^ ")"

            | _ -> false, ""

and extract_arg (a:arg) en :string =
    match a with
        | Inl _, _ -> raise (NYI ("Extract argument cannot extract type arguments"))
        | Inr e, _ -> extract_exp e en

and extract_sigelt (s:sigelt) en :string =
    match s with
        | Sig_let (lbs, _, _, _) ->
            if fst lbs then
                // recursive let
                if List.length (snd lbs) <> 1 then raise (NYI "Mutually recursive lets not supported")
                else
                    let lb = List.hd (snd lbs) in
                    let lbname = lbname_to_string lb.lbname in
                    let filter_ascription (e:exp) =
                        match (Util.compress_exp e).n with
                            | Exp_ascribed (e, _, _) -> e
                            | _ -> e
                    in
                    let lb_body = filter_ascription lb.lbdef in
                    match (Util.compress_exp lb_body).n with
                        | Exp_abs (bs, e) ->
                            // filter out type arguments
                            let bs = List.filter (fun a -> match a with | Inl _, _ -> false | Inr _, _ -> true) bs in
                            let first_b = List.hd bs in
                            let rest_bs = List.tl bs in
                            
                            let body_str = extract_exp e en in
                            let tl_abs_str = List.fold_left (fun s b -> "mk_abs " ^ extract_binder b ^ " (" ^ s ^ ")") body_str (List.rev rest_bs) in
                            let fix_str = "mk_fix " ^ name_to_string lbname ^ " " ^ extract_binder first_b ^ " (" ^ tl_abs_str ^ ")" in
                            let let_str = "mk_let " ^ name_to_string lbname ^ " (" ^ fix_str ^ ")" in
                            let_str
                        | _ -> raise (NYI ("Expected an abs with recursive let"))
            else
                let lb = List.hd (snd lbs) in "mk_let " ^ name_to_string (lbname_to_string lb.lbname) ^ " (" ^ (extract_exp lb.lbdef en) ^ ")"
        | Sig_main (e, _) -> extract_exp e en
        | _ -> ""

let extract_main (s:sigelt) en :string =
    match s with
        | Sig_main (e, _) -> extract_exp e en
        | _ -> raise (NYI ("Extract main got some other sigelt!"))

let extract_sigelts (l:list<sigelt>) en :string =
    let l = List.rev l in // reverse the sigelts so that main is the head
    
    let main_str = extract_main (List.hd l) en in
    List.fold_left (fun acc s ->
                        let s_str = extract_sigelt s en in
                        s_str ^ " (" ^ acc ^ ")") main_str (List.tl l)  // basically completing let body of the sigelt s

let extract (l:list<modul>) (en:FStar.Tc.Env.env) :unit =
    initialize ();
    List.iter (fun m ->
                if m.name.str = "SMC" then
                    let s = extract_sigelts m.declarations en in
                    Util.print_string s; Util.print_string "\n") l


//    let name = m.name.str in
//    Util.print_string ("Extracting module: " ^ name ^ "\n");
//List.iter (fun m -> if m.name.str = "Test" then Util.print_string (modul_to_string m) else ()) l
//    if name = "WLib" || name = "SMC" then
//        let s = List.fold_left (fun s sigelt -> s ^ "\n" ^ (extract_sigelt sigelt)) "" m.declarations in
//        Util.append_to_file fh s; Util.append_to_file fh "\n"
//        //Util.print_string (s ^ "\n")
//    else ()
