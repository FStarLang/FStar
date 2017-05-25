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
module FStar.Syntax.Print
open FStar.All

open FStar
open FStar.Syntax
open FStar.Util
open FStar.Syntax.Syntax
open FStar.Syntax.Util
open FStar.Syntax.Subst
open FStar.Ident
open FStar.Const
module U = FStar.Util
module A = FStar.Parser.AST
module Resugar = FStar.Syntax.Resugar
module ToDocument = FStar.Parser.ToDocument
module Pp = FStar.Pprint

let sli (l:lident) : string =
    if Options.print_real_names()
    then l.str
    else l.ident.idText
//    Util.format3 "%s@{def=%s;use=%s}" s
//        (Range.string_of_range (Ident.range_of_lid l))
//        (Range.string_of_use_range (Ident.range_of_lid l))

let lid_to_string (l:lid) = sli l

//let fv_to_string fv = Printf.sprintf "%s@%A" (lid_to_string fv.fv_name.v) fv.fv_delta
let fv_to_string fv = lid_to_string fv.fv_name.v

let bv_to_string bv = bv.ppname.idText ^ "#" ^ (string_of_int bv.index)

let nm_to_string bv =
    if Options.print_real_names()
    then bv_to_string bv
    else bv.ppname.idText

let db_to_string bv = bv.ppname.idText ^ "@" ^ string_of_int bv.index

(* CH: This should later be shared with ocaml-codegen.fs and util.fs (is_primop and destruct_typ_as_formula) *)
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
    (Const.op_Modulus     , "mod");
    (Const.and_lid     , "/\\");
    (Const.or_lid      , "\\/");
    (Const.imp_lid     , "==>");
    (Const.iff_lid     , "<==>");
    (Const.precedes_lid, "<<");
    (Const.eq2_lid     , "==");
    (Const.eq3_lid     , "===");
]

let unary_prim_ops = [
    (Const.op_Negation, "not");
    (Const.op_Minus, "-");
    (Const.not_lid, "~")
]

let is_prim_op ps f = match f.n with
  | Tm_fvar fv -> ps |> U.for_some (fv_eq_lid fv)
  | _ -> false

let get_lid f = match f.n with
  | Tm_fvar fv -> fv.fv_name.v
  | _ -> failwith "get_lid"

let is_infix_prim_op (e:term) = is_prim_op (fst (List.split infix_prim_ops)) e
let is_unary_prim_op (e:term) = is_prim_op (fst (List.split unary_prim_ops)) e

let quants = [
  (Const.forall_lid, "forall");
  (Const.exists_lid, "exists")
]
type exp = term

let is_b2t (t:typ)   = is_prim_op [Const.b2t_lid] t
let is_quant (t:typ) = is_prim_op (fst (List.split quants)) t
let is_ite (t:typ)   = is_prim_op [Const.ite_lid] t

let is_lex_cons (f:exp) = is_prim_op [Const.lexcons_lid] f
let is_lex_top (f:exp) = is_prim_op [Const.lextop_lid] f
let is_inr = function Inl _ -> false | Inr _ -> true
let filter_imp a = a |> List.filter (function (_, Some (Implicit _)) -> false | _ -> true)
let rec reconstruct_lex (e:exp) =
  match (compress e).n with
  | Tm_app (f, args) ->
      let args = filter_imp args in
      let exps = List.map fst args in
      if is_lex_cons f && List.length exps = 2 then
        match reconstruct_lex (List.nth exps 1) with
        | Some xs -> Some (List.nth exps 0 :: xs)
        | None    -> None
      else None
  | _ -> if is_lex_top e then Some [] else None

(* CH: F# List.find has a different type from find in list.fst ... so just a hack for now *)
let rec find  (f:'a -> bool) (l:list<'a>) : 'a = match l with
  | [] -> failwith "blah"
  | hd::tl -> if f hd then hd else find f tl

let find_lid (x:lident) xs : string =
  snd (find (fun p -> lid_equals x (fst p)) xs)

let infix_prim_op_to_string e = find_lid (get_lid e)      infix_prim_ops
let unary_prim_op_to_string e = find_lid (get_lid e)      unary_prim_ops
let quant_to_string t = find_lid (get_lid t) quants

let const_to_string x = match x with
  | Const_effect -> "Effect"
  | Const_unit -> "()"
  | Const_bool b -> if b then "true" else "false"
  | Const_float x ->      U.string_of_float x
  | Const_string(bytes, _) -> U.format1 "\"%s\"" (U.string_of_bytes bytes)
  | Const_bytearray _  ->  "<bytearray>"
  | Const_int (x, _) -> x
  | Const_char c -> "'" ^ U.string_of_char c ^ "'"
  | Const_range r -> Range.string_of_range r
  | Const_reify -> "reify"
  | Const_reflect l -> U.format1 "[[%s.reflect]]" (sli l)

let lbname_to_string = function
  | Inl l -> bv_to_string l
  | Inr l -> lid_to_string l.fv_name.v

let tag_of_term (t:term) = match t.n with
  | Tm_bvar x -> "Tm_bvar: "   ^ db_to_string x
  | Tm_name x -> "Tm_name: " ^ nm_to_string x
  | Tm_fvar x -> "Tm_fvar: "   ^ lid_to_string x.fv_name.v
  | Tm_uinst _ -> "Tm_uinst"
  | Tm_constant _ -> "Tm_constant"
  | Tm_type _ -> "Tm_type"
  | Tm_abs _ -> "Tm_abs"
  | Tm_arrow _ -> "Tm_arrow"
  | Tm_refine _ -> "Tm_refine"
  | Tm_app _ -> "Tm_app"
  | Tm_match _ -> "Tm_match"
  | Tm_ascribed _ -> "Tm_ascribed"
  | Tm_let _ -> "Tm_let"
  | Tm_uvar _ -> "Tm_uvar"
  | Tm_delayed(_, m) ->
    begin match !m with
        | None -> "Tm_delayed"
        | Some _ -> "Tm_delayed-resolved"
    end
  | Tm_meta _ -> "Tm_meta"
  | Tm_unknown -> "Tm_unknown"

let uvar_to_string u = if (Options.hide_uvar_nums()) then "?" else "?" ^ (Unionfind.uvar_id u |> string_of_int)

let rec int_of_univ n u = match Subst.compress_univ u with
    | U_zero -> n, None
    | U_succ u -> int_of_univ (n+1) u
    | _ -> n, Some u

let rec univ_to_string u = 
  if not (Options.ugly()) then
    let e = Resugar.resugar_universe u Range.dummyRange in
    let d = ToDocument.term_to_document e in
    Pp.pretty_string (float_of_string "1.0") 100 d
  else match Subst.compress_univ u with
    | U_unif u -> uvar_to_string u
    | U_name x -> x.idText
    | U_bvar x -> "@"^string_of_int x
    | U_zero   -> "0"
    | U_succ u ->
        begin match int_of_univ 1 u with
            | n, None -> string_of_int n
            | n, Some u -> U.format2 "(%s + %s)" (univ_to_string u) (string_of_int n)
        end
    | U_max us -> U.format1 "(max %s)" (List.map univ_to_string us |> String.concat ", ")
    | U_unknown -> "unknown"

let univs_to_string us = List.map univ_to_string us |> String.concat ", "

let univ_names_to_string us = List.map (fun x -> x.idText) us |> String.concat ", "

let qual_to_string = function
  | Assumption            -> "assume"
  | New                   -> "new"
  | Private               -> "private"
  | Unfold_for_unification_and_vcgen  -> "unfold"
  | Inline_for_extraction -> "inline"
  | NoExtract             -> "noextract"
  | Visible_default       -> "visible"
  | Irreducible           -> "irreducible"
  | Abstract              -> "abstract"
  | Noeq                  -> "noeq"
  | Unopteq               -> "unopteq"
  | Logic                 -> "logic"
  | TotalEffect           -> "total"
  | Discriminator l       -> U.format1 "(Discriminator %s)" (lid_to_string l)
  | Projector (l, x)      -> U.format2 "(Projector %s %s)" (lid_to_string l) x.idText
  | RecordType (ns, fns)  -> U.format2 "(RecordType %s %s)" (text_of_path (path_of_ns ns)) (fns |> List.map text_of_id |> String.concat ", ")
  | RecordConstructor (ns, fns) -> U.format2 "(RecordConstructor %s %s)" (text_of_path (path_of_ns ns))  (fns |> List.map text_of_id |> String.concat ", ")
  | Action eff_lid        -> U.format1 "(Action %s)" (lid_to_string eff_lid)
  | ExceptionConstructor  -> "ExceptionConstructor"
  | HasMaskedEffect       -> "HasMaskedEffect"
  | Effect                -> "Effect"
  | Reifiable             -> "reify"
  | Reflectable l         -> U.format1 "(reflect %s)" l.str
  | OnlyName              -> "OnlyName"

let quals_to_string quals =
    match quals with
    | [] -> ""
    | _ -> quals |> List.map qual_to_string |> String.concat " "

let quals_to_string' quals =
    match quals with
    | [] -> ""
    | _ -> quals_to_string quals ^ " "

(* This function prints the type it gets as argument verbatim.
   For already type-checked types use the typ_norm_to_string
   function in normalize.fs instead, since elaboration
   (higher-order unification) produces types containing lots of
   redexes that should first be reduced. *)
let rec term_to_string x =
  if not (Options.ugly()) then
    let e = Resugar.resugar_term x in
    let d = ToDocument.term_to_document e in
    Pp.pretty_string (float_of_string "1.0") 100 d
  else begin
      let x = Subst.compress x in
      let x = if Options.print_implicits() then x else unmeta x in
      match x.n with
      | Tm_delayed _ ->   failwith "impossible"
      | Tm_app(_, []) ->  failwith "Empty args!"

      | Tm_meta(t, Meta_pattern ps) ->
        let pats = ps |> List.map (fun args -> args |> List.map (fun (t, _) -> term_to_string t) |> String.concat "; ") |> String.concat "\/" in
        U.format2 "{:pattern %s} %s" pats (term_to_string t)

      | Tm_meta(t, Meta_monadic (m, t')) -> U.format4 ("(Monadic-%s{%s %s} %s)") (tag_of_term t) (sli m) (term_to_string t') (term_to_string t)
      | Tm_meta(t, Meta_monadic_lift(m0, m1, t')) -> U.format5 ("(MonadicLift-%s{%s : %s -> %s} %s)") (tag_of_term t) (term_to_string t') (sli m0) (sli m1) (term_to_string t)
      | Tm_meta(t, Meta_labeled(l,r,b)) when Options.print_implicits() ->
        U.format3 "Meta_labeled(%s, %s){%s}" l (Range.string_of_range r) (term_to_string t)
      | Tm_meta(t, _) ->    term_to_string t
      | Tm_bvar x ->        db_to_string x
      | Tm_name x ->        nm_to_string x
      | Tm_fvar f ->        fv_to_string f
      | Tm_uvar (u, _) ->   uvar_to_string u
      | Tm_constant c ->    const_to_string c
      | Tm_type u ->        if (Options.print_universes()) then U.format1 "Type u#(%s)" (univ_to_string u) else "Type"
      | Tm_arrow(bs, c) ->  U.format2 "(%s -> %s)"  (binders_to_string " -> " bs) (comp_to_string c)
      | Tm_abs(bs, t2, lc) ->
        begin match lc with
            | Some (Inl l) when (Options.print_implicits()) ->
              U.format3 "(fun %s -> (%s $$ %s))" (binders_to_string " " bs) (term_to_string t2) (comp_to_string <| l.comp())
              (* TODO : Consider adding an option printing the cflags *)
            | Some (Inr (l, flags)) when (Options.print_implicits()) ->
              U.format3 "(fun %s -> (%s $$ (name only) %s))" (binders_to_string " " bs) (term_to_string t2) l.str
            | _ ->
              U.format2 "(fun %s -> %s)" (binders_to_string " " bs) (term_to_string t2)
        end
      | Tm_refine(xt, f) -> U.format3 "(%s:%s{%s})" (bv_to_string xt) (xt.sort |> term_to_string) (f |> formula_to_string)
      | Tm_app(t, args) ->  U.format2 "(%s %s)" (term_to_string t) (args_to_string args)
      | Tm_let(lbs, e) ->   U.format2 "%s\nin\n%s" (lbs_to_string [] lbs) (term_to_string e)
      | Tm_ascribed(e,(annot, topt),eff_name) ->
        let annot = match annot with
            | Inl t -> U.format2 "[%s] %s" (map_opt eff_name Ident.text_of_lid |> dflt "default") (term_to_string t)
            | Inr c -> comp_to_string c in
        let topt = match topt with
            | None -> ""
            | Some t -> U.format1 "by %s" (term_to_string t) in
        U.format3 "(%s <: %s %s)" (term_to_string e) annot topt
      | Tm_match(head, branches) ->
        U.format2 "(match %s with\n\t| %s)"
          (term_to_string head)
          (U.concat_l "\n\t|" (branches |> List.map (fun (p,wopt,e) ->
                U.format3 "%s %s -> %s"
                            (p |> pat_to_string)
                            (match wopt with | None -> "" | Some w -> U.format1 "when %s" (w |> term_to_string))
                            (e |> term_to_string))))
      | Tm_uinst(t, us) ->
        if (Options.print_universes())
        then U.format2 "%s<%s>" (term_to_string t) (univs_to_string us)
        else term_to_string t
      | _ -> tag_of_term x
  end

and pat_to_string x = 
  if not (Options.ugly()) then
    let e = Resugar.resugar_pat x in
    let d = ToDocument.pat_to_document e in
    Pp.pretty_string (float_of_string "1.0") 100 d
  else match x.v with
    | Pat_cons(l, pats) -> U.format2 "(%s %s)" (fv_to_string l) (List.map (fun (x, b) -> let p = pat_to_string x in if b then "#"^p else p) pats |> String.concat " ")
    | Pat_dot_term (x, _) ->
      if Options.print_bound_var_types()
      then U.format2 ".%s:%s" (bv_to_string x) (term_to_string x.sort)
      else U.format1 ".%s" (bv_to_string x)
    | Pat_var x ->
      if Options.print_bound_var_types()
      then U.format2 "%s:%s" (bv_to_string x) (term_to_string x.sort)
      else bv_to_string x
    | Pat_constant c -> const_to_string c
    | Pat_wild x -> if (Options.print_real_names()) then "Pat_wild " ^ (bv_to_string x) else "_"
    | Pat_disj ps ->  U.concat_l " | " (List.map pat_to_string ps)


and lbs_to_string quals lbs =
    let lbs =
        if (Options.print_universes())
        then (fst lbs, snd lbs |> List.map (fun lb -> let us, td = Subst.open_univ_vars lb.lbunivs (Util.mk_conj lb.lbtyp lb.lbdef) in
                                        let t, d = match (Subst.compress td).n with
                                            | Tm_app(_, [(t, _); (d, _)]) -> t, d
                                            | _ -> failwith "Impossibe" in
                                        {lb with lbunivs=us; lbtyp=t; lbdef=d}))
        else lbs in
    U.format3 "%slet %s %s"
    (quals_to_string' quals)
    (if fst lbs then "rec" else "")
    (U.concat_l "\n and " (snd lbs |> List.map (fun lb ->
                                                    U.format4 "%s %s : %s = %s"
                                                            (lbname_to_string lb.lbname)
                                                            (if (Options.print_universes())
                                                             then "<"^univ_names_to_string lb.lbunivs^">"
                                                             else "")
                                                            (term_to_string lb.lbtyp)
                                                            (lb.lbdef |> term_to_string))))

and lcomp_to_string lc =
    if Options.print_effect_args () then
        comp_to_string (lc.comp ())
    else
        U.format2 "%s %s" (sli lc.eff_name) (term_to_string lc.res_typ)

//and uvar_t_to_string (uv, k) =
//   if false && (Options.print_real_names())
//   then
//       U.format2 "(U%s : %s)"
//       (if (Options.hide_uvar_nums()) then "?" else U.string_of_int (Unionfind.uvar_id uv))
//       (kind_to_string k)
//   else U.format1 "U%s"  (if (Options.hide_uvar_nums()) then "?" else U.string_of_int (Unionfind.uvar_id uv))

and imp_to_string s = function
  | Some (Implicit false) -> "#" ^ s
  | Some (Implicit true) -> "#." ^ s
  | Some Equality -> "$" ^ s
  | _ -> s

and binder_to_string' is_arrow b =
  if not (Options.ugly()) then
    let e = Resugar.resugar_binder b Range.dummyRange in
    let d = ToDocument.binder_to_document e in
    Pp.pretty_string (float_of_string "1.0") 100 d
  else 
    let (a, imp) = b in
    if is_null_binder b
    then ("_:" ^ term_to_string a.sort)
    else if not is_arrow && not (Options.print_bound_var_types()) then imp_to_string (nm_to_string a) imp
    else imp_to_string (nm_to_string a ^ ":" ^ term_to_string a.sort) imp

and binder_to_string b =  binder_to_string' false b

and arrow_binder_to_string b = binder_to_string' true b

and binders_to_string sep bs =
    let bs = if (Options.print_implicits()) then bs else filter_imp bs in
    if sep = " -> "
    then bs |> List.map arrow_binder_to_string |> String.concat sep
    else bs |> List.map binder_to_string |> String.concat sep

and arg_to_string = function
   | a, imp -> imp_to_string (term_to_string a) imp

and args_to_string args =
    let args = if (Options.print_implicits()) then args else filter_imp args in
    args |> List.map arg_to_string |> String.concat " "

and comp_to_string c =
  if not (Options.ugly()) then
    let e = Resugar.resugar_comp c in
    let d = ToDocument.term_to_document e in
    Pp.pretty_string (float_of_string "1.0") 100 d
  else 
    match c.n with
    | Total (t, _) ->
      begin match (compress t).n with
        | Tm_type _ when not (Options.print_implicits()) -> term_to_string t
        | _ -> U.format1 "Tot %s" (term_to_string t)
      end
    | GTotal (t, _) ->
      begin match (compress t).n with
        | Tm_type _ when not (Options.print_implicits()) -> term_to_string t
        | _ -> U.format1 "GTot %s" (term_to_string t)
      end
    | Comp c ->
        let basic =
          if (Options.print_effect_args())
          then U.format4 "%s (%s) %s (attributes %s)"
                            (sli c.effect_name)
                            (term_to_string c.result_typ)
                            (c.effect_args |> List.map arg_to_string |> String.concat ", ")
                            (c.flags |> List.map cflags_to_string |> String.concat " ")
          else if c.flags |> U.for_some (function TOTAL -> true | _ -> false)
          && not (Options.print_effect_args())
          then U.format1 "Tot %s" (term_to_string c.result_typ)
          else if not (Options.print_effect_args())
                  && not (Options.print_implicits())
                  && lid_equals c.effect_name Const.effect_ML_lid
          then term_to_string c.result_typ
          else if not (Options.print_effect_args())
               && c.flags |> U.for_some (function MLEFFECT -> true | _ -> false)
          then U.format1 "ALL %s" (term_to_string c.result_typ)
          else U.format2 "%s (%s)" (sli c.effect_name) (term_to_string c.result_typ) in
      let dec = c.flags |> List.collect (function DECREASES e -> [U.format1 " (decreases %s)" (term_to_string e)] | _ -> []) |> String.concat " " in
      U.format2 "%s%s" basic dec

and cflags_to_string c =
    match c with
        | TOTAL -> "total"
        | MLEFFECT -> "ml"
        | RETURN -> "return"
        | PARTIAL_RETURN -> "partial_return"
        | SOMETRIVIAL -> "sometrivial"
        | LEMMA -> "lemma"
        | CPS -> "cps"
        | DECREASES _ -> "" (* TODO : already printed for now *)


(* CH: at this point not even trying to detect if something looks like a formula,
       only locally detecting certain patterns *)
and formula_to_string phi = term_to_string phi


//let subst_to_string subst =
//   U.format1 "{%s}" <|
//    (List.map (function
//        | Inl (a, t) -> U.format2 "(%s -> %s)" (strBvd a) (typ_to_string t)
//        | Inr (x, e) -> U.format2 "(%s -> %s)" (strBvd x) (exp_to_string e)) subst |> String.concat ", ")
//let freevars_to_string (fvs:freevars) =
//    let f (l:set<bvar<'a,'b>>) = l |> U.set_elements |> List.map (fun t -> strBvd t.v) |> String.concat ", " in
//    U.format2 "ftvs={%s}, fxvs={%s}" (f fvs.ftvs) (f fvs.fxvs)


let enclose_universes s =
    if Options.print_universes ()
    then "<" ^ s ^ ">"
    else ""

let tscheme_to_string s = 
  if not (Options.ugly()) then
    let d = Resugar.resugar_tscheme s in
    let d = ToDocument.decl_to_document d in
    Pp.pretty_string (float_of_string "1.0") 100 d
  else 
    let (us, t) = s in
    U.format2 "%s%s" (enclose_universes <| univ_names_to_string us) (term_to_string t)

let eff_decl_to_string' for_free r q ed =
 if not (Options.ugly()) then
    let d = Resugar.resugar_eff_decl for_free r q ed in
    let d = ToDocument.decl_to_document d in
    Pp.pretty_string (float_of_string "1.0") 100 d
 else
    let actions_to_string actions =
        actions |> List.map (fun a ->
          U.format5 "%s%s %s : %s = %s"
            (sli a.action_name)
            (binders_to_string " " a.action_params)
            (enclose_universes <| univ_names_to_string a.action_univs)
            (term_to_string a.action_typ)
            (term_to_string a.action_defn))
        |> String.concat ",\n\t" in
    U.format "new_effect%s { \
      %s%s %s : %s \n  \
        return_wp   = %s\n\
      ; bind_wp     = %s\n\
      ; if_then_else= %s\n\
      ; ite_wp      = %s\n\
      ; stronger    = %s\n\
      ; close_wp    = %s\n\
      ; assert_p    = %s\n\
      ; assume_p    = %s\n\
      ; null_wp     = %s\n\
      ; trivial     = %s\n\
      ; repr        = %s\n\
      ; bind_repr   = %s\n\
      ; return_repr = %s\n\
      and effect_actions\n\t%s\n}\n"
        [(if for_free then "_for_free " else "");
         lid_to_string ed.mname;
         enclose_universes <| univ_names_to_string ed.univs;
         binders_to_string " " ed.binders;
         term_to_string ed.signature;
         tscheme_to_string ed.ret_wp;
         tscheme_to_string ed.bind_wp;
         tscheme_to_string ed.if_then_else;
         tscheme_to_string ed.ite_wp;
         tscheme_to_string ed.stronger;
         tscheme_to_string ed.close_wp;
         tscheme_to_string ed.assert_p;
         tscheme_to_string ed.assume_p;
         tscheme_to_string ed.null_wp;
         tscheme_to_string ed.trivial;
         term_to_string ed.repr;
         tscheme_to_string ed.bind_repr;
         tscheme_to_string ed.return_repr;
         actions_to_string ed.actions]

let eff_decl_to_string for_free ed = 
  eff_decl_to_string' for_free Range.dummyRange [] ed

let rec sigelt_to_string (x: sigelt) = 
 if not (Options.ugly()) then
    let e = Resugar.resugar_sigelt x in
    begin match e with 
    | Some d ->
      let d = ToDocument.decl_to_document d in
      Pp.pretty_string (float_of_string "1.0") 100 d
    | _ -> ""
    end
 else
  begin match x.sigel with
  | Sig_pragma(LightOff) -> "#light \"off\""
  | Sig_pragma(ResetOptions None) -> "#reset-options"
  | Sig_pragma(ResetOptions (Some s)) -> U.format1 "#reset-options \"%s\"" s
  | Sig_pragma(SetOptions s) -> U.format1 "#set-options \"%s\"" s
  | Sig_inductive_typ(lid, univs, tps, k, _, _) ->
    U.format4 "%stype %s %s : %s"
             (quals_to_string' x.sigquals)
             lid.str
             (binders_to_string " " tps)
             (term_to_string k)
  | Sig_datacon(lid, univs, t, _, _, _) ->
    if (Options.print_universes())
    then let univs, t = Subst.open_univ_vars univs t in
         U.format3 "datacon<%s> %s : %s" (univ_names_to_string univs) lid.str (term_to_string t)
    else U.format2 "datacon %s : %s" lid.str (term_to_string t)
  | Sig_declare_typ(lid, univs, t) ->
    let univs, t = Subst.open_univ_vars univs t in
    U.format4 "%sval %s %s : %s" (quals_to_string' x.sigquals) lid.str
        (if (Options.print_universes())
         then U.format1 "<%s>" (univ_names_to_string univs)
         else "")
        (term_to_string t)
  | Sig_assume(lid, f) -> U.format2 "val %s : %s" lid.str (term_to_string f)
  | Sig_let(lbs, _, _) -> lbs_to_string x.sigquals lbs
  | Sig_main(e) -> U.format1 "let _ = %s" (term_to_string e)
  | Sig_bundle(ses, _) -> List.map sigelt_to_string ses |> String.concat "\n"
  | Sig_new_effect(ed) -> eff_decl_to_string' false x.sigrng x.sigquals ed
  | Sig_new_effect_for_free (ed) -> eff_decl_to_string' true x.sigrng x.sigquals ed
  | Sig_sub_effect (se) ->
    let lift_wp = match se.lift_wp, se.lift with
      // TODO pretty-print this better
      | None, None ->
          failwith "impossible"
      | Some lift_wp, _ ->
          lift_wp
      | _, Some lift ->
          lift
    in
    let us, t = Subst.open_univ_vars (fst lift_wp) (snd lift_wp) in
    U.format4 "sub_effect %s ~> %s : <%s> %s"
        (lid_to_string se.source) (lid_to_string se.target)
        (univ_names_to_string us) (term_to_string t)
  | Sig_effect_abbrev(l, univs, tps, c, flags) ->
    if (Options.print_universes())
    then let univs, t = Subst.open_univ_vars univs (mk (Tm_arrow(tps, c)) None Range.dummyRange) in
         let tps, c = match (Subst.compress t).n with
            | Tm_arrow(bs, c) -> bs, c
            | _ -> failwith "impossible" in
         U.format4 "effect %s<%s> %s = %s" (sli l) (univ_names_to_string univs) (binders_to_string " " tps) (comp_to_string c)
    else U.format3 "effect %s %s = %s" (sli l) (binders_to_string " " tps) (comp_to_string c)
  end

let format_error r msg = format2 "%s: %s\n" (Range.string_of_range r) msg

let rec sigelt_to_string_short (x: sigelt) = match x.sigel with
  | Sig_let((_, [{lbname=lb; lbtyp=t}]), _, _) -> U.format2 "let %s : %s" (lbname_to_string lb) (term_to_string t)
  | _ -> lids_of_sigelt x |> List.map (fun l -> l.str) |> String.concat ", "

let rec modul_to_string (m:modul) =
  U.format2 "module %s\n%s" (sli m.name) (List.map sigelt_to_string m.declarations |> String.concat "\n")

let subst_elt_to_string = function
   | DB(i, x) -> U.format2 "DB (%s, %s)" (string_of_int i) (bv_to_string x)
   | NM(x, i) -> U.format2 "NM (%s, %s)" (bv_to_string x) (string_of_int i)
   | NT(x, t) -> U.format2 "DB (%s, %s)" (bv_to_string x) (term_to_string t)
   | UN(i, u) -> U.format2 "UN (%s, %s)" (string_of_int i) (univ_to_string u)
   | UD(u, i) -> U.format2 "UD (%s, %s)" u.idText (string_of_int i)

let subst_to_string s = s |> List.map subst_elt_to_string |> String.concat "; "

let abs_ascription_to_string ascription =
  let strb = U.new_string_builder () in
  begin match ascription with
      | None -> U.string_builder_append strb "None"
      | Some (Inl lc) ->
          U.string_builder_append strb "Some Inr " ;
          U.string_builder_append strb (Ident.text_of_lid lc.eff_name)
      | Some (Inr lid) ->
          U.string_builder_append strb "Some Inr " ;
          U.string_builder_append strb (Ident.text_of_lid lid)
  end ;
  U.string_of_string_builder strb

let list_to_string f elts =
    match elts with
        | [] -> "[]"
        | x::xs ->
            let strb = U.new_string_builder () in
            U.string_builder_append strb "[" ;
            U.string_builder_append strb (f x) ;
            List.iter (fun x ->
                       U.string_builder_append strb "; " ;
                       U.string_builder_append strb (f x)
                       ) xs ;
            U.string_builder_append strb "]" ;
            U.string_of_string_builder strb

let set_to_string f s =
    let elts = U.set_elements s in
    match elts with
        | [] -> "{}"
        | x::xs ->
            let strb = U.new_string_builder () in
            U.string_builder_append strb "{" ;
            U.string_builder_append strb (f x) ;
            List.iter (fun x ->
                       U.string_builder_append strb ", " ;
                       U.string_builder_append strb (f x)
                       ) xs ;
            U.string_builder_append strb "}" ;
            (* U.string_builder_append strb (list_to_string f (raw_list s)) ; *)
            U.string_of_string_builder strb
