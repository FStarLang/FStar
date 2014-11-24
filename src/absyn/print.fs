(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
#light "off"
// (c) Microsoft Corporation. All rights reserved
module Microsoft.FStar.Absyn.Print

open Microsoft.FStar
open Microsoft.FStar.Absyn
open Microsoft.FStar.Util
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Absyn.Util

(* CH: This should later be shared with ocaml-codegen.fs and util.fs *)
let infix_prim_ops = [
    (Const.op_Addition    , "+" );
    (Const.op_Subtraction , "-" );
    (Const.op_Multiply    , "*" );
    (Const.op_Division    , "/" );
    (Const.op_Eq          , "=" );
    (Const.op_ColonEq     , ":=");
    (Const.op_notEq       , "<>");
    (Const.op_And         , "&&");
    (Const.op_Or          , "||");
    (Const.op_LTE         , "<=");
    (Const.op_GTE         , ">=");
    (Const.op_LT          , "<" );
    (Const.op_GT          , ">" );
    (Const.op_Modulus     , "mod" );
]
(* CH: What about the Lex ordering, doesn't that belong here too?
[6:23:30 PM] Nikhil Swamy: are you including printing Precedes as <<
[6:23:45 PM] Nikhil Swamy: and LexCons ... as %[v1;..vn]?
[6:23:52 PM] Catalin Hritcu: yes
 *)

let prim_uni_ops = [
    (Const.op_Negation, "not");
    (Const.op_Minus, "-")
]

let is_op ps f = match f.n with 
  | Exp_fvar(fv,_) -> ps |> Util.for_some (lid_equals fv.v)
  | _ -> false

let get_lid f = match f.n with 
  | Exp_fvar(fv,_) -> fv.v
  | _ -> failwith "get_lid"

let is_infix_prim_op = is_op (fst (List.split infix_prim_ops))

let is_uni_prim_op (e:exp) = is_op (fst (List.split prim_uni_ops)) e

(* CH: F# List.find has a different type from find in list.fst ... so just a hack for now *)
let rec find f l = match l with 
  | [] -> failwith "blah"
  | hd::tl -> if f hd then hd else find f tl

let find_lid (x:lident) xs : string =
  snd (find (fun p -> lid_equals x (fst p)) xs)

let infix_prim_op_to_string e = find_lid (get_lid e) infix_prim_ops

let uni_prim_op_to_string e = find_lid (get_lid e) prim_uni_ops

let rec sli (l:lident) : string = 
  if !Options.print_real_names
  then match l.ns with 
      | hd::tl when (hd.idText="Prims") ->
        begin match tl with 
          | [] -> l.ident.idText
          | _ -> (List.map (fun i -> i.idText) tl |> String.concat ".") ^  "." ^ l.ident.idText
        end
      | _ -> l.str
   else l.ident.idText

let strBvd bvd = 
    if !Options.print_real_names
    then bvd.ppname.idText ^ bvd.realname.idText
    else 
        if !Options.hide_genident_nums && starts_with (bvd.ppname.idText) "_" then
            try
                let _ = int_of_string (substring_from (bvd.ppname.idText) 1) in "_?"
            with _ -> bvd.ppname.idText
        else bvd.ppname.idText

let const_to_string x = match x with
  | Const_unit -> "()"
  | Const_bool b -> if b then "true" else "false"
  | Const_int32 x ->      Util.string_of_int x
  | Const_float x ->      Util.string_of_float x
  | Const_char x ->       "'" ^ (Util.string_of_char x) ^ "'"
  | Const_string(bytes, _) -> Util.format1 "\"%s\"" (Util.string_of_bytes bytes)
  | Const_bytearray _  ->  "<bytearray>"
  | Const_int64 _ -> "<int64>"
  | Const_uint8 _ -> "<uint8>"
   
let rec tag_of_typ t = match t.n with 
  | Typ_btvar _ -> "Typ_btvar"
  | Typ_const v -> "Typ_const " ^ v.v.str
  | Typ_fun _ -> "Typ_fun"
  | Typ_refine _ -> "Typ_refine"
  | Typ_app(head, args) -> 
    format2 "Typ_app(%s, [%s args])" (tag_of_typ head) (string_of_int <| List.length args)
  | Typ_lam _ -> "Typ_lam"
  | Typ_ascribed _ -> "Typ_ascribed"
  | Typ_meta(Meta_pattern _) -> "Typ_meta_pattern"
  | Typ_meta(Meta_named _) -> "Typ_meta_named"
  | Typ_meta(Meta_labeled _) -> "Typ_meta_labeled"
  | Typ_meta(Meta_refresh_label _) -> "Typ_meta_refresh_label"
  | Typ_uvar _ -> "Typ_uvar"   
  | Typ_delayed _ -> "Typ_delayed"
  | Typ_unknown -> "Typ_unknown"

and tag_of_exp e = match e.n with 
  | Exp_bvar _ -> "Exp_bvar"
  | Exp_fvar _ -> "Exp_fvar"
  | Exp_constant _ -> "Exp_constant"
  | Exp_abs _ -> "Exp_abs"
  | Exp_app _ -> "Exp_app"
  | Exp_match _ -> "Exp_match"
  | Exp_ascribed _ -> "Exp_ascribed"
  | Exp_let _ -> "Exp_let"
  | Exp_uvar _ -> "Exp_uvar"
  | Exp_delayed _ -> "Exp_delayed"
  | Exp_meta(Meta_desugared(_, m)) -> "Exp_meta_desugared " ^ (meta_e_to_string m)
  | Exp_meta(Meta_datainst(_, _)) -> "Exp_meta_datainst"
and meta_e_to_string = function 
    | Data_app -> "Data_app"
    | Sequence -> "Sequence"                  
    | Primop   -> "Primop"

(* This function prints the type it gets as argument verbatim.
   For already type-checked types use the typ_norm_to_string
   function in normalize.fs instead, since elaboration
   (higher-order unification) produces types containing lots of
   redexes that should first be reduced. *)
and typ_to_string x =
  let x = Util.compress_typ x in
  match x.n with 
  | Typ_delayed _ -> failwith "impossible"
  | Typ_meta(Meta_named(_, l)) -> sli l
  | Typ_meta meta ->           Util.format1 "(Meta %s)" (meta|> meta_to_string)
  | Typ_btvar btv -> strBvd btv.v
    //Util.format2 "(%s:%s)" (strBvd btv.v) (kind_to_string x.tk)
  | Typ_const v -> sli v.v //Util.format2 "%s:%s" (sli v.v) (kind_to_string x.tk)
  | Typ_fun(binders, c) ->     Util.format2 "(%s -> %s)"  (binders_to_string " -> " binders) (comp_typ_to_string c)
  | Typ_refine(xt, f) ->       Util.format3 "%s:%s{%s}" (strBvd xt.v) (xt.sort |> typ_to_string) (f|> formula_to_string)
  | Typ_app(t, args) ->        Util.format2 "(%s %s)"   (t |> typ_to_string) (args |> args_to_string)
  | Typ_lam(binders, t2) ->      Util.format2 "(fun %s => %s)" (binders_to_string " " binders) (t2|> typ_to_string)
  | Typ_ascribed(t, k) ->
    if !Options.print_real_names  
    then Util.format2 "(%s <: %s)" (typ_to_string t) (kind_to_string k)
    else t|> typ_to_string
  | Typ_unknown -> "<UNKNOWN>"
  | Typ_uvar(uv, k) -> (match Visit.compress_typ_aux false x with 
      | {n=Typ_uvar _} -> uvar_t_to_string (uv, k)
      | t -> t|> typ_to_string)

and uvar_t_to_string (uv, k) =
   "U" ^ (if !Options.hide_uvar_nums then "?" else Util.string_of_int (Unionfind.uvar_id uv))

and imp_to_string s = function
  | true -> "#" ^ s
  | false -> s

and binder_to_string b = match b with 
    | Inl a, imp -> if is_null_binder b then kind_to_string a.sort else imp_to_string ((strBvd a.v) ^ ":" ^ (kind_to_string a.sort)) imp
    | Inr x, imp -> if is_null_binder b then typ_to_string x.sort else imp_to_string ((strBvd x.v) ^ ":" ^ (typ_to_string x.sort)) imp
   
and binders_to_string sep bs =
    let bs = if !Options.print_implicits then bs else List.filter (fun (_,i) -> not i) bs in
    bs |> List.map binder_to_string |> String.concat sep

and arg_to_string = function 
   | Inl a, imp -> imp_to_string (typ_to_string a) imp
   | Inr x, imp -> imp_to_string (exp_to_string x) imp

and args_to_string args =
    let args = if !Options.print_implicits then args else List.filter (fun (_,i) -> not i) args in
    args |> List.map arg_to_string |> String.concat " "

and comp_typ_to_string c =
  match c.n with
    | Total t -> Util.format1 "Tot %s" (typ_to_string t)
    | Comp c ->
      let basic = 
          if c.flags |> Util.for_some (function TOTAL -> true | _ -> false) && not !Options.print_effect_args 
          then Util.format1 "Tot %s" (typ_to_string c.result_typ)
          else if not !Options.print_effect_args && (lid_equals c.effect_name Const.ml_effect_lid)//  || List.contains MLEFFECT c.flags) 
          then typ_to_string c.result_typ
          else if not !Options.print_effect_args && c.flags |> Util.for_some (function MLEFFECT -> true | _ -> false)
          then Util.format1 "ALL %s" (typ_to_string c.result_typ)
          else if !Options.print_effect_args 
          then Util.format3 "%s (%s) %s" (sli c.effect_name) (typ_to_string c.result_typ) (c.effect_args |> List.map effect_arg_to_string |> String.concat ", ")//match c.effect_args with hd::_ -> effect_arg_to_string hd | _ ->"")
          else Util.format2 "%s (%s)" (sli c.effect_name) (typ_to_string c.result_typ) in
      let dec = c.flags |> List.collect (function DECREASES e -> [Util.format1 " (decreases %s)" (exp_to_string e)] | _ -> []) |> String.concat " " in
      Util.format2 "%s%s" basic dec
       
and effect_arg_to_string e = match e with
    | Inr e, _ -> exp_to_string e
    | Inl wp, _ -> formula_to_string wp
     
and formula_to_string phi = 
    let const_op f _ = f in
    let un_op  f = function 
        | [(Inl t, _)] -> format2 "%s %s" f (formula_to_string t)
        | _ -> failwith "impos" in
    let bin_top f = function 
        | [(Inl t1, _); (Inl t2, _)] -> format3 "%s %s %s" (formula_to_string t1) f (formula_to_string t2)
        | _ -> failwith "Impos" in
    let bin_eop f = function
        | [(Inr e1, _);(Inr e2, _)] -> format3 "%s %s %s" (exp_to_string e1) f (exp_to_string e2)
        | _ -> failwith "impos" in
    let ite = function 
        | [(Inl t1, _);(Inl t2, _);(Inl t3, _)] -> format3 "if %s then %s else %s" (formula_to_string t1) (formula_to_string t2) (formula_to_string t3)
        | _ -> failwith "impos" in
    let eq_op = function 
        | [(Inl _, _); (Inl _, _); (Inr e1, _); (Inr e2, _)]
        | [(Inr e1, _); (Inr e2, _)] -> format2 "%s == %s" (exp_to_string e1) (exp_to_string e2)
        |  _ -> failwith "Impossible" in
    let connectives = [(Const.and_lid,  bin_top "/\\");
                       (Const.or_lid, bin_top "\\/");
                       (Const.imp_lid, bin_top "==>");
                       (Const.iff_lid, bin_top "<==>");
                       (Const.ite_lid, ite);
                       (Const.not_lid, un_op "~");
                       (Const.eqT_lid, bin_top "==");
                       (Const.eq2_lid, eq_op);
                       (Const.true_lid, const_op "True");
                       (Const.false_lid, const_op "False");
                       ] in

    let fallback phi = match phi.n with 
        | Typ_lam(binders, phi) ->  format2 "(fun %s => %s)" (binders_to_string " " binders) (formula_to_string phi)
        | _ -> typ_to_string phi in

    match Util.destruct_typ_as_formula phi with 
        | None -> fallback phi
        
        | Some (BaseConn(op, arms)) -> 
           (match connectives |> List.tryFind (fun (l, _) -> lid_equals op l) with 
             | None -> fallback phi
             | Some (_, f) -> f arms)

        | Some (QAll(vars, _, body)) -> 
          format2 "(forall %s. %s)" (binders_to_string " " vars) (formula_to_string body)

        | Some (QEx(vars, _, body)) -> 
          format2 "(exists %s. %s)" (binders_to_string " " vars) (formula_to_string body)
         
and exp_to_string x = match (compress_exp x).n with 
  | Exp_delayed _ -> failwith "Impossible"
  | Exp_meta(Meta_datainst(e,_))
  | Exp_meta(Meta_desugared(e, _)) -> exp_to_string e
  | Exp_uvar(uv, t) -> uvar_e_to_string (uv, t)
  | Exp_bvar bvv -> strBvd bvv.v //Util.format2 "%s : %s" (strBvd bvv.v) (typ_to_string bvv.sort)
  | Exp_fvar(fv, _) ->  sli fv.v
  | Exp_constant c -> c |> const_to_string
  | Exp_abs(binders, e) -> Util.format2 "(fun %s -> %s)" (binders_to_string " " binders) (e|> exp_to_string)
  | Exp_app(e, args) ->
      if is_infix_prim_op e && List.length args = 2 then
        Util.format3 "(%s %s %s)" (List.nth args 0 |> arg_to_string) (e|> infix_prim_op_to_string) (List.nth args 1 |> arg_to_string)
      else if is_uni_prim_op e && List.length args = 1 then
        Util.format2 "(%s %s)" (e|> uni_prim_op_to_string) (List.nth args 0 |> arg_to_string)
      else Util.format2 "(%s %s)" (e|> exp_to_string) (args_to_string args)
  | Exp_match(e, pats) -> Util.format2 "(match %s with %s)" 
    (e |> exp_to_string) 
    (Util.concat_l "\n\t" (pats |> List.map (fun (p,wopt,e) -> Util.format3 "%s %s -> %s" 
      (p |> pat_to_string)
      (match wopt with | None -> "" | Some w -> Util.format1 "when %s" (w |> exp_to_string)) 
      (e |> exp_to_string))))
  | Exp_ascribed(e, t) -> Util.format2 "(%s:%s)" (e|> exp_to_string) (t |> typ_to_string)
  | Exp_let(lbs, e) -> Util.format2 "%s in %s" 
    (lbs_to_string lbs)
    (e|> exp_to_string)

and uvar_e_to_string (uv, _) =
    "'e" ^ (if !Options.hide_uvar_nums then "?" else Util.string_of_int (Unionfind.uvar_id uv))

and lbs_to_string lbs = 
    Util.format2 "let %s %s"
    (if fst lbs then "rec" else "") 
    (Util.concat_l "\n and " (snd lbs |> List.map (fun (x, t, e) -> Util.format3 "%s:%s = %s" (lbname_to_string x) (t |> typ_to_string) (e|> exp_to_string)))) 
    
and lbname_to_string x = match x with
  | Inl bvd -> strBvd bvd 
  | Inr lid -> sli lid

and either_to_string x = match x with
  | Inl t -> typ_to_string t
  | Inr e -> exp_to_string e

 and either_l_to_string delim l = 
  l |> List.map either_to_string |> Util.concat_l delim

and meta_to_string x = match x with 
  | Meta_refresh_label(t, _, _) -> Util.format1 "(refresh) %s" (typ_to_string t)
  | Meta_labeled(t, l, _) -> Util.format2 "(labeled \"%s\") %s" l (typ_to_string t)
  | Meta_named(_, l) -> sli l
  | Meta_pattern(t,ps) -> Util.format2 "{:pattern %s} %s" (args_to_string ps) (t |> typ_to_string) 

and kind_to_string x = match (compress_kind x).n with 
  | Kind_lam _ -> failwith "Impossible"
  | Kind_delayed _ -> failwith "Impossible"
  | Kind_uvar (uv,args) -> uvar_k_to_string' (uv,args)
  | Kind_type -> "Type"
  | Kind_effect -> "Effect"
  | Kind_abbrev((n, args), k) -> 
    if !Options.print_real_names
    then kind_to_string k
    else Util.format2 "%s %s" (sli n) (args_to_string args)
  | Kind_arrow(binders, k) -> Util.format2 "(%s => %s)" (binders_to_string " => " binders) (k |> kind_to_string)
  | Kind_unknown -> "_"

and uvar_k_to_string uv =
    "'k_" ^ (if !Options.hide_uvar_nums then "?" else Util.string_of_int (Unionfind.uvar_id uv))

and uvar_k_to_string' (uv,args) =
   let str = if !Options.hide_uvar_nums then "?" else Util.string_of_int (Unionfind.uvar_id uv) in
   format2 "('k_%s %s)" str (args_to_string args)

and pat_to_string x = match x.v with
  | Pat_cons(l, pats) -> Util.format2 "(%s %s)" (sli l.v) (List.map pat_to_string pats |> String.concat " ") 
  | Pat_dot_term (x, _) -> Util.format1 ".%s" (strBvd x.v)
  | Pat_dot_typ (x, _) -> Util.format1 ".'%s" (strBvd x.v)
  | Pat_var x -> strBvd x.v
  | Pat_tvar a -> strBvd a.v
  | Pat_constant c -> const_to_string c
  | Pat_wild _ -> "_"
  | Pat_twild _ -> "'_"
  | Pat_disj ps ->  Util.concat_l " | " (List.map pat_to_string ps)

let subst_to_string subst = 
   Util.format1 "{%s}" <|
    (List.map (function 
        | Inl (a, t) -> Util.format2 "(%s -> %s)" (strBvd a) (typ_to_string t)
        | Inr (x, e) -> Util.format2 "(%s -> %s)" (strBvd x) (exp_to_string e)) subst |> String.concat ", ")
let freevars_to_string (fvs:freevars) = 
    let f (l:set<bvar<'a,'b>>) = l |> Util.set_elements |> List.map (fun t -> strBvd t.v) |> String.concat ", " in
    Util.format2 "ftvs={%s}, fxvs={%s}" (f fvs.ftvs) (f fvs.fxvs) 

let qual_to_string = function
    | Logic -> "logic"
    | Opaque -> "opaque"
    | Discriminator _ -> "discriminator"
    | Projector _ -> "projector"
    | _ -> "other"
let quals_to_string quals = quals |> List.map qual_to_string |> String.concat " " 
let rec sigelt_to_string x = match x with 
  | Sig_tycon(lid, tps, k, _, _, quals, _) -> Util.format4 "%s type %s %s : %s" (quals_to_string quals) lid.str (binders_to_string " " tps) (kind_to_string k)
  | Sig_typ_abbrev(lid, tps, k, t, _, _) ->  Util.format4 "type %s %s : %s = %s" lid.str (binders_to_string " " tps) (kind_to_string k) (typ_to_string t)
  | Sig_datacon(lid, t, _, _, _) -> Util.format2 "datacon %s : %s" lid.str (typ_to_string t)
  | Sig_val_decl(lid, t, quals, _) -> Util.format3 "%s val %s : %s" (quals_to_string quals) lid.str (typ_to_string t)
  | Sig_assume(lid, f, _, _) -> Util.format2 "val %s : %s" lid.str (typ_to_string f)
  | Sig_let(lbs, _, _) -> lbs_to_string lbs
  | Sig_main(e, _) -> Util.format1 "let _ = %s" (exp_to_string e)
  | Sig_bundle(ses, _, _) -> List.map sigelt_to_string ses |> String.concat "\n"
  | Sig_monads _ -> "monad_lattice { ... }"

let rec sigelt_to_string_short x = match x with 
  | Sig_let((_, [(Inr l, t, _)]), _, _) -> Util.format2 "let %s : %s" l.str (typ_to_string t) 
  | _ -> lids_of_sigelt x |> List.map (fun l -> l.str) |> String.concat ", "

let rec modul_to_string (m:modul) = 
  Util.format2 "module %s\n%s" (sli m.name) (List.map sigelt_to_string m.declarations |> String.concat "\n")
