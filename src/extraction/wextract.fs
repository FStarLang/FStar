module Microsoft.FStar.Extraction.Wysteria.Extract

open Microsoft.FStar
open Microsoft.FStar.Util
open Microsoft.FStar.Absyn
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Absyn.Print

exception NYI of string

let process_wysteria_lib_fun_app_args (s:string) (args:list<arg>) :list<arg> = match s with
    | "unbox_p"
    | "unbox_s"
    | "mkwire_p" -> List.tl args    // first argument is an implicit
 
    | _          -> args

let extract_const (c:sconst) :string = match c with
    | Const_unit    -> "()"
    | Const_bool b  -> if b then "true" else "false"
    | Const_int32 n -> Util.string_of_int32 n
    | Const_int x   -> x

    | _             -> raise (NYI "Constant not expected")

let extract_binder (b:binder) :string = match b with
    | Inl _, _    -> ""
    | Inr bvar, _ -> bvar.v.ppname.idText

let rec extract_exp (e:exp) :string = match (Util.compress_exp e).n with
    | Exp_bvar bvar          -> bvar.v.ppname.idText
    | Exp_fvar (fvar, _)     -> fvar.v.ident.idText
    | Exp_constant c         -> extract_const c
    | Exp_abs (bs, e)        ->
      let bs_str = List.fold (fun s b -> s ^ "fun " ^ (extract_binder b) ^ ". ") "" bs in
      let s' = extract_exp e in
      bs_str ^ s'
    | Exp_app (e, args)      ->
      let s = extract_exp e in
      let args = List.filter (fun a -> match a with | Inl _, _ -> false | Inr _, _ -> true) args in
      let args = process_wysteria_lib_fun_app_args s args in
      List.fold (fun s a -> s ^ (extract_arg a) ^ " ") (s ^ " ") args
    | Exp_match (e, pats)    ->
      let s = extract_exp e in
      s ^ "\n" ^ (extract_pats pats)
    | Exp_ascribed (e, _, _) -> extract_exp e
    | Exp_let (lbs, e)       ->
      if fst lbs then raise (NYI "Recursive let not expected")
      else
        let lb = List.hd (snd lbs) in
        "let " ^ (lbname_to_string lb.lbname) ^ " = " ^ (extract_exp lb.lbdef) ^ " in\n" ^ (extract_exp e)
    | Exp_uvar _
    | _ -> Util.print_string ("Expression not expected " ^ (tag_of_exp e)); raise (NYI "")

and extract_arg (a:arg) :string = match a with
    | Inl _, _ -> raise (NYI "This should not have happened")
    | Inr e, _ -> "( " ^ extract_exp e ^ " )"

and extract_pats (pats: list<pat * option<exp> * exp>) :string =
    List.fold (fun s (p, w, e) ->
               let s' = "| " ^ (extract_pat p) ^ " -> " ^ (extract_exp e) in
               s ^ "\n" ^ s) "" pats

and extract_pat (p:pat) :string = match p.v with
    | Pat_constant c -> extract_const c

    | _              -> raise (NYI "Pattern not expected")

let extract_sigelt (s:sigelt) :string = match s with
    | Sig_let (lbs, _, _, _) ->
      if fst lbs then raise (NYI "Recursive let not expected")
      else
        let lb = List.hd (snd lbs) in
        "let " ^ (lbname_to_string lb.lbname) ^ " = " ^ (extract_exp lb.lbdef)

    | _ -> ""

let extract (m:modul) : unit =
    let name = m.name.str in
    Util.print_string ("Extracting module: " ^ name ^ "\n")
    if name = "Examples" then
        let s = List.fold (fun s sigelt -> s ^ "\n" ^ (extract_sigelt sigelt)) "" m.declarations in
        Util.print_string (s ^ "\n")
    else ()