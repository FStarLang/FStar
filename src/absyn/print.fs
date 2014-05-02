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
open Microsoft.FStar.Util
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Absyn.Util

let rec sli (l:lident) : string = match l.ns with 
  | hd::tl when (hd.idText="Prims") ->
    begin match tl with 
      | [] -> l.ident.idText
      | _ -> (List.map (fun i -> i.idText) tl |> String.concat ".") ^  "." ^ l.ident.idText
    end
  | _ -> l.str

let strBvd bvd = 
    if !Options.print_real_names
    then bvd.realname.idText
    else bvd.ppname.idText

let const_to_string x = match x with
  | Const_unit -> "()"
  | Const_bool b -> if b then "true" else "false"
  | Const_int32 x ->      Util.string_of_int x
  | Const_float x ->      Util.string_of_float x
  | Const_char x ->       Util.string_of_char x
  | Const_string(bytes, _) -> Util.string_of_bytes bytes
  | Const_bytearray _  ->  "<bytearray>"
  | Const_int64 _ -> "<int64>"
  | Const_uint8 _ -> "<uint8>"
     
let rec typ_to_string x =
  let x = if !Options.print_real_names then x else whnf x in
  match (compress_typ x).t with 
  | Typ_btvar btv -> 
    (match !btv.v.instantiation with 
      | None -> strBvd btv.v
      | Some x -> x|> typ_to_string)
  | Typ_const v -> Util.format1 "%s" (sli v.v)
  | Typ_fun(Some x, t1, t2, imp) -> Util.format4 "%s%s%s -> %s"  (strBvd x) (if imp then "@" else ":") (t1 |> typ_to_string) (t2|> typ_to_string)
  | Typ_fun(None, t1, t2, _) -> Util.format2 "%s -> %s"  (t1|> typ_to_string) (t2|> typ_to_string)
  | Typ_univ(a, k, t) ->       Util.format3 "%s:%s -> %s" (strBvd a) (k |> kind_to_string) (t|> typ_to_string)
  | Typ_refine(x, t, f) ->     Util.format3 "%s:%s{%s}" (strBvd x) (t|> typ_to_string) (f|> typ_to_string)
  | Typ_app(t1, t2, imp) ->    Util.format3 "(%s %s%s)" (t1|> typ_to_string) (if imp then "#" else "") (t2|> typ_to_string)
  | Typ_dep(t, v, imp) ->      Util.format3 "(%s %s%s)" (t|> typ_to_string) (if imp then "#" else "") (v|> exp_to_string)
  | Typ_lam(x, t1, t2) ->      Util.format3 "(fun (%s:%s) => %s)" (strBvd x) (t1 |> typ_to_string) (t2|> typ_to_string)
  | Typ_tlam(a, k, t) ->       Util.format3 "(fun (%s:%s) => %s)" (strBvd a) (k |> kind_to_string) (t|> typ_to_string)
  | Typ_ascribed(t, k) when !Options.print_real_names -> Util.format2 "(%s <: %s)" (typ_to_string t) (kind_to_string k)
  | Typ_ascribed(t, _) ->      t|> typ_to_string
  | Typ_unknown -> "_"
  | Typ_meta meta ->           Util.format1 "(Meta %s)" (meta|> meta_to_string)
  | Typ_uvar(uv, k) -> (match Unionfind.find uv with 
      | Fixed t -> t|> typ_to_string
      | Uvar _ when !Options.print_real_names ->  Util.format2 "'U%s : %s"  (Util.string_of_int (Unionfind.uvar_id uv)) (kind_to_string k)
      | Uvar _ ->               Util.format1 "'U%s"  (Util.string_of_int (Unionfind.uvar_id uv)))

and exp_to_string x = match compress_exp x with 
  | Exp_meta(Meta_datainst(e,_)) -> exp_to_string e 
  | Exp_uvar(uv, _) -> Util.format1 "'e%s" (Util.string_of_int (Unionfind.uvar_id uv))
  | Exp_bvar bvv -> 
    (match !bvv.v.instantiation with 
      | None -> strBvd bvv.v
      | Some x -> x|> exp_to_string)
  | Exp_fvar(fv, _) ->  sli fv.v
  | Exp_constant c -> c |> const_to_string
  | Exp_abs(x, t, e) -> Util.format3 "(fun (%s:%s) -> %s)" (strBvd x) (t |> typ_to_string) (e|> exp_to_string)
  | Exp_tabs(a, k, e) -> Util.format3 "(fun (%s::%s) -> %s)" (strBvd a) (k |> kind_to_string) (e|> exp_to_string)
  | Exp_app(e1, e2, imp) -> Util.format3 "(%s %s%s)" (e1|> exp_to_string) (if imp then "#" else "") (e2|> exp_to_string)
  | Exp_tapp(e, t) -> Util.format2 "(%s %s)" (e|> exp_to_string) (t |> typ_to_string)
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
  | Exp_primop(id, el)-> Util.format2 "(%s %s)" (id.idText) (Util.concat_l " " (List.map exp_to_string el))

and lbs_to_string lbs = 
    Util.format2 "let %s %s"
    (if fst lbs then "rec" else "") 
    (Util.concat_l "\n and" (snd lbs |> List.map (fun (x, t, e) -> Util.format3 "%s:%s = %s" (lbname_to_string x) (t |> typ_to_string) (e|> exp_to_string)))) 
    
and lbname_to_string x = match x with
  | Inl bvd -> strBvd bvd 
  | Inr lid -> sli lid

and either_to_string x = match x with
  | Inl t -> typ_to_string t
  | Inr e -> exp_to_string e

and meta_to_string x = match x with 
  | Meta_pos(t, _) -> typ_to_string t
  | Meta_cases tl -> Util.format1 "\n\tMetaCases [%s]\n" (Util.concat_l ";\n" (List.map typ_to_string tl))
  | Meta_tid i -> Util.format1 "(Meta_tid %d)" (Util.string_of_int i)
  | Meta_pattern(t,ps) -> Util.format2 "{:pattern %s} %s" (t |> typ_to_string) (Util.concat_l ", " (ps |> List.map either_to_string))

and kind_to_string x = match compress_kind x with 
  | Kind_uvar uv -> format1 "'k_%s" (Util.string_of_int (Unionfind.uvar_id uv))
  | Kind_star -> "Type"
  | Kind_tcon(Some x, k, k', imp) -> Util.format4 "(%s%s:%s => %s)" (if imp then "#" else "") (strBvd x) (k |> kind_to_string) (k' |> kind_to_string)
  | Kind_tcon(_, k, k', _) -> Util.format2 "(%s => %s)" (k |> kind_to_string) (k' |> kind_to_string)
  | Kind_dcon(Some x, t, k, imp) -> Util.format4 "(%s%s:%s => %s)" (if imp then "#" else "") (strBvd x) (t |> typ_to_string) (k |> kind_to_string)
  | Kind_dcon(_, t, k, _) -> Util.format2 "(%s => %s)" (t |> typ_to_string) (k |> kind_to_string)
  | Kind_unknown -> "_"

and pat_to_string x = match x with
  | Pat_cons(l, pats) -> Util.format2 "(%s %s)" (sli l) (List.map pat_to_string pats |> String.concat " ") 
  | Pat_var x -> strBvd x
  | Pat_tvar a -> strBvd a
  | Pat_constant c -> const_to_string c 
  | Pat_wild -> "_"
  | Pat_twild -> "'_"
  | Pat_disj ps ->  Util.concat_l " | " (List.map pat_to_string ps)
  | Pat_withinfo (p, _) -> pat_to_string p

let tparam_to_string = function
  | Tparam_typ(a, k) -> Util.format2 "(%s:%s)" (strBvd a) (kind_to_string k)
  | Tparam_term(x, t) -> Util.format2 "(%s:%s)" (strBvd x) (typ_to_string t)

let tparams_to_string tps = List.map tparam_to_string tps |> String.concat " "

let rec sigelt_to_string x = match x with 
  | Sig_tycon(lid, tps, k, _, _, _, _) -> Util.format3 "type %s %s : %s" lid.str (tparams_to_string tps) (kind_to_string k)
  | Sig_typ_abbrev(lid, tps, k, t, _) ->  Util.format4 "type %s %s : %s = %s" lid.str (tparams_to_string tps) (kind_to_string k) (typ_to_string t)
  | Sig_datacon(lid, t, _, _) -> Util.format2 "datacon %s : %s" lid.str (typ_to_string t)
  | Sig_val_decl(lid, t, _, _, _) -> Util.format2 "val %s : %s" lid.str (typ_to_string t)
  | Sig_assume(lid, f, _, _, _) -> Util.format2 "val %s : %s" lid.str (typ_to_string f)
  | Sig_logic_function(lid, t, _, _) -> Util.format2 "logic val %s : %s" lid.str (typ_to_string t)
  | Sig_let(lbs, _) -> lbs_to_string lbs
  | Sig_main(e, _) -> Util.format1 "let _ = %s" (exp_to_string e)
  | Sig_bundle(ses, _) -> List.map sigelt_to_string ses |> String.concat "\n"

let rec sigelt_to_string_short x = match x with 
  | Sig_let((_, [(Inr l, t, _)]), _) -> Util.format2 "%s : %s" l.str (typ_to_string t) 
  | _ -> lids_of_sigelt x |> List.map (fun l -> l.str) |> String.concat ", "