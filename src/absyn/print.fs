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

let rec sli (l:lident) : string = match l.lid with 
  | hd::tl when (hd.idText="Prims") -> Util.concat_l "." (tl |> List.map (fun x -> x.idText))
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
  | Const_bytearray _  ->  failwith "NYI: to string of byte array"
    
let rec typ_to_string x = match whnf x with 
  | Typ_btvar btv -> 
    (match !btv.v.instantiation with 
      | None -> 
        if !Options.print_real_names then btv.v.realname.idText else btv.v.realname.idText
      | Some x -> x|> typ_to_string)
  | Typ_const v -> Util.format1 "%s" (sli v.v)
  | Typ_fun(Some x, t1, t2) -> Util.format3 "%s:%s -> %s"  (strBvd x) (t1 |> typ_to_string) (t2|> typ_to_string)
  | Typ_fun(None, t1, t2) ->   Util.format2 "%s -> %s"  (t1|> typ_to_string) (t2|> typ_to_string)
  | Typ_univ(a, k, t) ->       Util.format3 "%s::%s -> %s" (strBvd a) (k |> kind_to_string) (t|> typ_to_string)
  | Typ_refine(x, t, f) ->     Util.format3 "%s:%s{%s}" (strBvd x) (t|> typ_to_string) (f|> typ_to_string)
  | Typ_app(t1, t2) ->         Util.format2 "(%s %s)" (t1|> typ_to_string) (t2|> typ_to_string)
  | Typ_dep(t, v) ->           Util.format2 "(%s %s)" (t|> typ_to_string) (v|> exp_to_string)
  | Typ_lam(x, t1, t2) ->      Util.format2 "(fun %s => %s)" (strBvd x) (t2|> typ_to_string)
  | Typ_tlam(a, k, t) ->       Util.format2 "(fun %s => %s)" (strBvd a) (t|> typ_to_string)
  | Typ_ascribed(t, k) ->      t|> typ_to_string
  | Typ_unknown -> "_"
  | Typ_meta meta ->           Util.format1 "(Meta %s)" (meta|> meta_to_string)
  | Typ_uvar(uv, _) -> (match Unionfind.find uv with 
      | Delayed t
      | Fixed t -> t|> typ_to_string
      | Uvar _ ->               Util.format1 "'U%s"  (Util.string_of_int (Unionfind.uvar_id uv)))

and exp_to_string x = match x.v with 
  | Exp_bvar bvv -> 
    (match !bvv.v.instantiation with 
      | None -> 
        if !Options.print_real_names then bvv.v.realname.idText else bvv.v.realname.idText
      | Some x -> x|> exp_to_string)
  | Exp_fvar fv ->  sli fv.v
  | Exp_constant c -> c |> const_to_string
  | Exp_constr_app(d, args) -> Util.format2 "(%s %s)" (sli d.v) (Util.concat_l " " (List.map either_to_string args))
  | Exp_abs(x, t, e) -> Util.format3 "(fun (%s:%s) -> %s)" (strBvd x) (t |> typ_to_string) (e|> exp_to_string)
  | Exp_tabs(a, k, e) -> Util.format3 "(fun (%s::%s) -> %s)" (strBvd a) (k |> kind_to_string) (e|> exp_to_string)
  | Exp_app(e1, e2) -> Util.format2 "(%s %s)" (e1|> exp_to_string) (e2|> exp_to_string)
  | Exp_tapp(e, t) -> Util.format2 "(%s %s)" (e|> exp_to_string) (t |> typ_to_string)
  | Exp_match(e, pats) -> Util.format2 "(match %s with %s)" 
    (e |> exp_to_string) 
    (Util.concat_l "\n\t" (pats |> List.map (fun (p,wopt,e) -> Util.format3 "%s %s -> %s" 
      (p |> pat_to_string)
      (match wopt with | None -> "" | Some w -> Util.format1 "when %s" (w |> exp_to_string)) 
      (e |> exp_to_string))))
  | Exp_ascribed(e, t) -> Util.format2 "(%s:%s)" (e|> exp_to_string) (t |> typ_to_string)
  | Exp_let(r, lbs, e) -> Util.format3 "let %s %s in %s" 
    (if r then "rec" else "") 
    (Util.concat_l "\n and" (lbs |> List.map (fun (x, t, e) -> Util.format3 "%s:%s = %s" (strBvd x) (t |> typ_to_string) (e|> exp_to_string)))) 
    (e|> exp_to_string)
  | Exp_primop(id, el)-> Util.format2 "(%s %s)" (id.idText) (Util.concat_l " " (List.map exp_to_string el))

and either_to_string x = match x with
  | Inl t -> typ_to_string t
  | Inr e -> exp_to_string e

and meta_to_string x = match x with 
  | Meta_cases tl -> Util.format1 "\n\tMetaCases [%s]\n" (Util.concat_l ";\n" (List.map typ_to_string tl))
  | Meta_tid i -> Util.format1 "(Meta_tid %d)" (Util.string_of_int i)
  | Meta_pattern(t,ps) -> Util.format2 "{:pattern %s} %s" (t |> typ_to_string) (Util.concat_l ", " (ps |> List.map either_to_string))

and kind_to_string x = match x with 
  | Kind_star -> "*"
  | Kind_prop -> "P"
  | Kind_erasable -> "E"
  | Kind_tcon(Some x, k, k') -> Util.format3 "(%s::%s => %s)" (strBvd x) (k |> kind_to_string) (k' |> kind_to_string)
  | Kind_tcon(_, k, k') -> Util.format2 "(%s => %s)" (k |> kind_to_string) (k' |> kind_to_string)
  | Kind_dcon(Some x, t, k) -> Util.format3 "(%s:%s => %s)" (strBvd x) (t |> typ_to_string) (k |> kind_to_string)
  | Kind_dcon(_, t, k) -> Util.format2 "(%s => %s)" (t |> typ_to_string) (k |> kind_to_string)
  | Kind_unknown -> "_"

and pat_to_string x = match x with
  | Pat_cons(l, pats) -> Util.format2 "(%s %s)" (sli l) (List.map pat_to_string pats |> String.concat " ") 
  | Pat_var x -> strBvd x
  | Pat_tvar a -> strBvd a
  | Pat_constant c -> const_to_string c 
  | Pat_wild -> "_"
  | Pat_twild -> "'_"
  | Pat_disj ps ->  Util.concat_l " | " (List.map pat_to_string ps)
