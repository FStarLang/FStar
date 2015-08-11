module Microsoft.FStar.Extraction.Wysteria.Extract

open Microsoft.FStar
open Microsoft.FStar.Util
open Microsoft.FStar.Absyn
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Absyn.Print

exception NYI of string

let prims_ffi_names = [ "op_Addition"; "op_Subtraction"; "op_Multiply"; "op_Division"; "op_Equality"; "op_disEquality"; "op_AmpAmp";
                        "op_BarBar"; "op_LessThanOrEqual"; "op_GreaterThanOrEqual"; "op_LessThan"; "op_GreaterThan"; "op_Modulus"]

let wys_ffi_names = [ "mem"; "singleton"; "subset"; "union"; "size"; "choose"; "remove"; "read"; "main" ]

let extract_const (c:sconst) :string =
    match c with
        | Const_unit    -> "()"
        | Const_bool b  -> if b then "true" else "false"
        | Const_int32 n -> Util.string_of_int32 n
        | Const_int x   -> x

        | _             -> raise (NYI "Constant not expected")

let extract_binder (b:binder) :string =
    match b with
        | Inl _, _    -> ""
        | Inr bvar, _ -> bvar.v.ppname.idText

let rec extract_exp (e:exp) :string =
    match (Util.compress_exp e).n with
        | Exp_bvar bvar          -> bvar.v.ppname.idText
        | Exp_fvar (fvar, _)     -> fvar.v.ident.idText
        | Exp_constant c         -> extract_const c
        | Exp_abs (bs, e)        ->
            let bs_str = List.fold_left (fun s b -> s ^ "fun " ^ (extract_binder b) ^ ". ") "" bs in
            bs_str ^ (extract_exp e)
        | Exp_app (e, args)      ->
            let args = List.filter (fun a -> match a with | Inl _, _ -> false | Inr _, _ -> true) args in    // filter type arguments
            let b, s = extract_prims_ffi e args in
            if b then s
            else
                let b, s = extract_wys_ffi e args in
                if b then s
                else
                    let s = extract_exp e in
                    let b, s' = extract_wysteria_specific_ast s args in
                    if b then s'
                    else
                        List.fold_left (fun s a -> "(apply " ^ s ^ " " ^ (extract_arg a) ^ ")") s args
                
        | Exp_match (e, pats)    ->
            let s = extract_exp e in
            "match " ^ s ^ " with\n" ^ (extract_pats pats) ^ "\nend"
        | Exp_ascribed (e, _, _) -> extract_exp e
        | Exp_let (lbs, e)       ->
            if fst lbs then raise (NYI "Recursive let not expected")
            else
                let lb = List.hd (snd lbs) in
                "let " ^ (lbname_to_string lb.lbname) ^ " = " ^ (extract_exp lb.lbdef) ^ " in\n" ^ (extract_exp e)
        | Exp_uvar _
        | _ -> Util.print_string ("Expression not expected " ^ (tag_of_exp e)); raise (NYI "")

and extract_prims_ffi (e:exp) (args_l:args) :(bool * string) =
    match (Util.compress_exp e).n with
        | Exp_fvar (fvar, _) ->
            let fn_name = fvar.v.ident.idText in
            let mlid = lid_of_ids fvar.v.ns in

            if List.length (mlid.ns) = 0 && mlid.ident.idText = "Prims" && Util.for_some (fun s -> s = fn_name) prims_ffi_names then
                let args_s = List.fold_left (fun s a -> s ^ (extract_arg a) ^ "; ") "" args_l in
                true, "ffi " ^ fn_name ^ " [ " ^ args_s ^ " ]"
            else
                false, ""

        | _ -> false, ""

and extract_wys_ffi (e:exp) (args_l:args) :(bool * string) =
    match (Util.compress_exp e).n with
        | Exp_fvar (fvar, _) ->
            let fn_name = fvar.v.ident.idText in
            if Util.for_some (fun s -> s = fn_name) wys_ffi_names then
                if fn_name = "main" then
                    let f = List.hd (List.tl args_l) in
                    let b, s = 
                        match f with
                            | Inl _, _ -> false, ""
                            | Inr f, _ -> true, extract_exp (mk_Exp_app (f, [varg (mk_Exp_constant Const_unit None dummyRange)]) None dummyRange)
                    in
                    b, s
                else 
                    let args_s = List.fold_left (fun s a -> s ^ (extract_arg a) ^ "; ") "" args_l in
                    true, "ffi " ^ fn_name ^ " [ " ^ args_s ^ " ]"
            else
                false, ""

        | _ -> false, ""

and extract_wysteria_specific_ast (s:string) (args:list<arg>) :(bool * string) =
    let b, args =
        match s with
            | "unbox_p"
            | "unbox_s"
            | "mkwire_p" -> true, List.tl args    // first argument is an implicit
            | "as_par"
            | "as_sec"
            | "mkwire_s"
            | "projwire_p"
            | "projwire_s"
            | "concat_wire" -> true, args

            | _ -> false, args
    in
    if b then
        b, List.fold_left (fun s a -> s ^ " " ^ (extract_arg a)) s args
    else
        b, ""

and extract_arg (a:arg) :string =
    match a with
        | Inl _, _ -> raise (NYI "Type arguments should already have been filtered")
        | Inr e, _ -> "( " ^ extract_exp e ^ " )"

and extract_pats (pats: list<(pat * option<exp> * exp)>) :string =
    List.fold_left (fun s (p, w, e) ->
               let s' = "| " ^ (extract_pat p) ^ " -> " ^ (extract_exp e) in
               s ^ "\n" ^ s') "" pats

and extract_pat (p:pat) :string =
    match p.v with
        | Pat_constant c -> extract_const c

        | _              -> raise (NYI "Pattern not expected")

let extract_sigelt (s:sigelt) :string =
    match s with
        | Sig_let (lbs, _, _, _) ->
            if fst lbs then raise (NYI "Recursive let not expected")
            else
                let lb = List.hd (snd lbs) in
                "let " ^ (lbname_to_string lb.lbname) ^ " = " ^ (extract_exp lb.lbdef) ^ " in"

        | Sig_main (e, _) -> extract_exp e

        | _ -> ""

let extract (m:modul) : unit =
    let name = m.name.str in
    Util.print_string ("Extracting module: " ^ name ^ "\n");
    if name = "SMC" then
        let s = List.fold_left (fun s sigelt -> s ^ "\n" ^ (extract_sigelt sigelt)) "" m.declarations in
        Util.write_file "SMC.wy" s
        //Util.print_string (s ^ "\n")
    else ()