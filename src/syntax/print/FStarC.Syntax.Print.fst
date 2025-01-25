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

module FStarC.Syntax.Print
open FStar.Pervasives
open FStarC.Effect

open FStar open FStarC
open FStarC
open FStarC.Range
open FStarC.Syntax
open FStarC.Util
open FStarC.Syntax.Syntax
open FStarC.Syntax.Subst
open FStarC.Ident
open FStarC.Const
open FStarC.Json

module Errors     = FStarC.Errors
module U          = FStarC.Util
module A          = FStarC.Parser.AST
module Unionfind  = FStarC.Syntax.Unionfind
module C          = FStarC.Parser.Const
module SU         = FStarC.Syntax.Util

module Pretty     = FStarC.Syntax.Print.Pretty
module Ugly       = FStarC.Syntax.Print.Ugly

let sli (l:lident) : string =
    if Options.print_real_names()
    then string_of_lid l
    else string_of_id (ident_of_lid l)
//    Util.format3 "%s@{def=%s;use=%s}" s
//        (Range.string_of_range (Ident.range_of_lid l))
//        (Range.string_of_use_range (Ident.range_of_lid l))

let lid_to_string (l:lid) = sli l

// let fv_to_string fv = Printf.sprintf "%s@%A" (lid_to_string fv.fv_name.v) fv.fv_delta
let fv_to_string fv = lid_to_string fv.fv_name.v //^ "(@@" ^ showfv.fv_delta ^ ")"
let bv_to_string bv =
  if Options.print_real_names ()
  then show bv.ppname ^ "#" ^ show bv.index
  else show bv.ppname

let nm_to_string bv =
    if Options.print_real_names()
    then bv_to_string bv
    else (string_of_id bv.ppname)

let db_to_string bv = (string_of_id bv.ppname) ^ "@" ^ string_of_int bv.index

let filter_imp aq =
   (* keep typeclass args *)
   match aq with
   | Some (Meta t) when SU.is_fvar C.tcresolve_lid t -> true
   | Some (Implicit _)
   | Some (Meta _) -> false
   | _ -> true
let filter_imp_args args =
  args |> List.filter (function (_, None) -> true | (_, Some a) -> not a.aqual_implicit)
let filter_imp_binders bs =
  bs |> List.filter (fun b -> b.binder_qual |> filter_imp)

let const_to_string = C.const_to_string

let lbname_to_string = function
  | Inl l -> bv_to_string l
  | Inr l -> lid_to_string l.fv_name.v

let uvar_to_string u = if (Options.hide_uvar_nums()) then "?" else "?" ^ (Unionfind.uvar_id u |> string_of_int)
let version_to_string v = U.format2 "%s.%s" (U.string_of_int v.major) (U.string_of_int v.minor)
let univ_uvar_to_string u =
    if (Options.hide_uvar_nums())
    then "?"
    else "?" ^ (Unionfind.univ_uvar_id u |> string_of_int)
            ^ ":" ^ (u |> (fun (_, u, _) -> version_to_string u))

let rec int_of_univ n u = match Subst.compress_univ u with
    | U_zero -> n, None
    | U_succ u -> int_of_univ (n+1) u
    | _ -> n, Some u

let rec univ_to_string u =
Errors.with_ctx "While printing universe" (fun () ->
  // VD: commented out for testing NBE
  // if not (Options.ugly()) then
  //   Pretty.univ_to_string u
  // else
  match Subst.compress_univ u with
    | U_unif u -> "U_unif "^univ_uvar_to_string u
    | U_name x -> "U_name "^(string_of_id x)
    | U_bvar x -> "@"^string_of_int x
    | U_zero   -> "0"
    | U_succ u ->
        begin match int_of_univ 1 u with
            | n, None -> string_of_int n
            | n, Some u -> U.format2 "(%s + %s)" (univ_to_string u) (string_of_int n)
        end
    | U_max us -> U.format1 "(max %s)" (List.map univ_to_string us |> String.concat ", ")
    | U_unknown -> "unknown"
)

let univs_to_string us = List.map univ_to_string us |> String.concat ", "

let qual_to_string = function
  | Assumption            -> "assume"
  | InternalAssumption    -> "internal_assume"
  | New                   -> "new"
  | Private               -> "private"
  | Unfold_for_unification_and_vcgen  -> "unfold"
  | Inline_for_extraction -> "inline_for_extraction"
  | NoExtract             -> "noextract"
  | Visible_default       -> "visible"
  | Irreducible           -> "irreducible"
  | Noeq                  -> "noeq"
  | Unopteq               -> "unopteq"
  | Logic                 -> "logic"
  | TotalEffect           -> "total"
  | Discriminator l       -> U.format1 "(Discriminator %s)" (lid_to_string l)
  | Projector (l, x)      -> U.format2 "(Projector %s %s)" (lid_to_string l) (string_of_id x)
  | RecordType (ns, fns)  -> U.format2 "(RecordType %s %s)" (text_of_path (path_of_ns ns)) (fns |> List.map string_of_id |> String.concat ", ")
  | RecordConstructor (ns, fns) -> U.format2 "(RecordConstructor %s %s)" (text_of_path (path_of_ns ns))  (fns |> List.map string_of_id |> String.concat ", ")
  | Action eff_lid        -> U.format1 "(Action %s)" (lid_to_string eff_lid)
  | ExceptionConstructor  -> "ExceptionConstructor"
  | HasMaskedEffect       -> "HasMaskedEffect"
  | Effect                -> "Effect"
  | Reifiable             -> "reify"
  | Reflectable l         -> U.format1 "(reflect %s)" (string_of_lid l)
  | OnlyName              -> "OnlyName"

let quals_to_string quals =
    match quals with
    | [] -> ""
    | _ -> quals |> List.map qual_to_string |> String.concat " "

let quals_to_string' quals =
    match quals with
    | [] -> ""
    | _ -> quals_to_string quals ^ " "

let paren s = "(" ^ s ^ ")"

let lkind_to_string = function
  | BadLazy -> "BadLazy"
  | Lazy_bv -> "Lazy_bv"
  | Lazy_namedv -> "Lazy_namedv"
  | Lazy_binder -> "Lazy_binder"
  | Lazy_optionstate -> "Lazy_optionstate"
  | Lazy_fvar -> "Lazy_fvar"
  | Lazy_comp -> "Lazy_comp"
  | Lazy_env -> "Lazy_env"
  | Lazy_proofstate -> "Lazy_proofstate"
  | Lazy_goal -> "Lazy_goal"
  | Lazy_sigelt -> "Lazy_sigelt"
  | Lazy_uvar -> "Lazy_uvar"
  | Lazy_letbinding -> "Lazy_letbinding"
  | Lazy_embedding (e, _) -> "Lazy_embedding(" ^ show e ^ ")"
  | Lazy_universe -> "Lazy_universe"
  | Lazy_universe_uvar -> "Lazy_universe_uvar"
  | Lazy_issue -> "Lazy_issue"
  | Lazy_ident -> "Lazy_ident"
  | Lazy_doc -> "Lazy_doc"
  | Lazy_extension s -> "Lazy_extension:" ^ s

let term_to_string x =
  if Options.ugly ()
  then Ugly.term_to_string x
  else Pretty.term_to_string x

let term_to_string' env x =
  if Options.ugly ()
  then Ugly.term_to_string x
  else Pretty.term_to_string' env x

let comp_to_string c =
  if Options.ugly ()
  then Ugly.comp_to_string c
  else Pretty.comp_to_string c

let comp_to_string' env c =
  if Options.ugly ()
  then Ugly.comp_to_string c
  else Pretty.comp_to_string' env c

let sigelt_to_string x =
  if Options.ugly ()
  then Ugly.sigelt_to_string x
  else Pretty.sigelt_to_string x

let sigelt_to_string' env x =
  if Options.ugly ()
  then Ugly.sigelt_to_string x
  else Pretty.sigelt_to_string' env x

let pat_to_string x =
  if Options.ugly ()
  then Ugly.pat_to_string x
  else Pretty.pat_to_string x

let term_to_doc' dsenv t =
  if Options.ugly ()
  then Pprint.arbitrary_string (Ugly.term_to_string t)
  else Pretty.term_to_doc' dsenv t

let univ_to_doc' dsenv t =
  if Options.ugly ()
  then Pprint.arbitrary_string (Ugly.univ_to_string t)
  else Pretty.univ_to_doc' dsenv t

let comp_to_doc' dsenv t =
  if Options.ugly ()
  then Pprint.arbitrary_string (Ugly.comp_to_string t)
  else Pretty.comp_to_doc' dsenv t

let sigelt_to_doc' dsenv t =
  if Options.ugly ()
  then Pprint.arbitrary_string (Ugly.sigelt_to_string t)
  else Pretty.sigelt_to_doc' dsenv t

let term_to_doc t =
  if Options.ugly ()
  then Pprint.arbitrary_string (Ugly.term_to_string t)
  else Pretty.term_to_doc t

let univ_to_doc t =
  if Options.ugly ()
  then Pprint.arbitrary_string (Ugly.univ_to_string t)
  else Pretty.univ_to_doc t

let comp_to_doc t =
  if Options.ugly ()
  then Pprint.arbitrary_string (Ugly.comp_to_string t)
  else Pretty.comp_to_doc t

let sigelt_to_doc t =
  if Options.ugly ()
  then Pprint.arbitrary_string (Ugly.sigelt_to_string t)
  else Pretty.sigelt_to_doc t

let binder_to_string b =
  if Options.ugly ()
  then Pretty.binder_to_string' false b
  else Ugly.binder_to_string b

let aqual_to_string (q:aqual) : string =
  match q with
  | Some { aqual_implicit=true } -> "#"
  | _ -> ""

let bqual_to_string' (s:string) (b:bqual) : string =
  match b with
  | Some (Implicit false) -> "#" ^ s
  | Some (Implicit true) -> "#." ^ s
  | Some Equality -> "$" ^ s
  | Some (Meta t) when SU.is_fvar C.tcresolve_lid t -> "{|" ^ s ^ "|}"
  | Some (Meta t) -> "#[" ^ term_to_string t ^ "]" ^ s
  | None -> s

let bqual_to_string (q:bqual) : string =
  bqual_to_string' "" q

let subst_elt_to_string = function
   | DB(i, x) -> U.format2 "DB (%s, %s)" (string_of_int i) (bv_to_string x)
   | DT(i, t) -> U.format2 "DT (%s, %s)" (string_of_int i) (term_to_string t)
   | NM(x, i) -> U.format2 "NM (%s, %s)" (bv_to_string x) (string_of_int i)
   | NT(x, t) -> U.format2 "NT (%s, %s)" (bv_to_string x) (term_to_string t)
   | UN(i, u) -> U.format2 "UN (%s, %s)" (string_of_int i) (univ_to_string u)
   | UD(u, i) -> U.format2 "UD (%s, %s)" (string_of_id u) (string_of_int i)

(*
 * AR: 07/19: exports is redundant, keeping it here until vale is fixed to not parse it
 *)
let modul_to_string (m:modul) =
  U.format2 "module %s\nDeclarations: [\n%s\n]\n"
    (show m.name) (List.map sigelt_to_string m.declarations |> String.concat "\n")

let metadata_to_string = function
    | Meta_pattern (_, ps) ->
        let pats = ps |> List.map (fun args -> args |> List.map (fun (t, _) -> term_to_string t) |> String.concat "; ") |> String.concat "\/" in
        U.format1 "{Meta_pattern %s}" pats

    | Meta_named lid ->
        U.format1 "{Meta_named %s}" (sli lid)

    | Meta_labeled (l, r, _) ->
        U.format2 "{Meta_labeled (%s, %s)}" (Errors.Msg.rendermsg l) (Range.string_of_range r)

    | Meta_desugared msi ->
        "{Meta_desugared}"

    | Meta_monadic (m, t) ->
        U.format2 "{Meta_monadic(%s @ %s)}" (sli m) (term_to_string t)

    | Meta_monadic_lift (m, m', t) ->
        U.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" (sli m) (sli m') (term_to_string t)


instance showable_term   = { show = term_to_string; }
instance showable_univ   = { show = univ_to_string; }
instance showable_comp   = { show = comp_to_string; }
instance showable_sigelt = { show = sigelt_to_string; }
instance showable_bv     = { show = bv_to_string; }
instance showable_fv     = { show = fv_to_string; }
instance showable_binder = { show = binder_to_string; }
instance showable_uvar   = { show = uvar_to_string; }
let ctx_uvar_to_string ctx_uvar =
    let reason_string = U.format1 "(* %s *)\n" ctx_uvar.ctx_uvar_reason in
    format5 "%s(%s |- %s : %s) %s"
            reason_string
            (String.concat ", " <| List.map show ctx_uvar.ctx_uvar_binders)
            (uvar_to_string ctx_uvar.ctx_uvar_head)
            (term_to_string (SU.ctx_uvar_typ ctx_uvar))
            (match SU.ctx_uvar_should_check ctx_uvar with
             | Allow_unresolved s -> "Allow_unresolved " ^s
             | Allow_untyped s -> "Allow_untyped " ^s
             | Allow_ghost s -> "Allow_ghost " ^s
             | Strict   -> "Strict"
             | Already_checked -> "Already_checked")

instance showable_ctxu   = { show = ctx_uvar_to_string; }
instance showable_binding = {
  show = (function
          | Binding_var x -> "Binding_var " ^ show x
          | Binding_lid x -> "Binding_lid " ^ show x
          | Binding_univ x -> "Binding_univ " ^ show x);
}
instance showable_subst_elt = { show = subst_elt_to_string; }
instance showable_branch = { show = Ugly.branch_to_string; }
instance showable_qualifier = { show = qual_to_string; }
instance showable_pat    = { show = pat_to_string; }
instance showable_const  = { show = const_to_string; }
instance showable_letbinding  = { show = Ugly.lb_to_string; }
instance showable_modul       = { show = modul_to_string; }
instance showable_metadata    = { show = metadata_to_string; }
instance showable_ctx_uvar_meta = {
  show = (function
          | Ctx_uvar_meta_attr attr -> "Ctx_uvar_meta_attr " ^ show attr
          | Ctx_uvar_meta_tac r -> "Ctx_uvar_meta_tac " ^ show r);
}
instance showable_bqual   = { show = (fun b -> bqual_to_string (Some b)); } // really silly but OK
instance showable_aqual   = { show = aqual_to_string; }

let tscheme_to_string ts =
  if Options.ugly ()
  then Ugly.tscheme_to_string ts
  else Pretty.tscheme_to_string ts

let sub_eff_to_string se =
  let tsopt_to_string ts_opt =
    if is_some ts_opt then ts_opt |> must |> tscheme_to_string
    else "<None>" in
  U.format4 "sub_effect %s ~> %s : lift = %s ;; lift_wp = %s"
    (lid_to_string se.source) (lid_to_string se.target)
    (tsopt_to_string se.lift) (tsopt_to_string se.lift_wp)

instance showable_sub_eff = { show = sub_eff_to_string; }

instance pretty_term     = { pp   = term_to_doc; }
instance pretty_univ     = { pp   = univ_to_doc; }
instance pretty_sigelt   = { pp   = sigelt_to_doc; }
instance pretty_comp     = { pp   = comp_to_doc; }
instance pretty_ctxu     = { pp   = (fun x -> Pprint.doc_of_string (show x)); }
instance pretty_uvar     = { pp   = (fun x -> Pprint.doc_of_string (show x)); }
instance pretty_binder   = { pp   = (fun x -> Pprint.doc_of_string (show x)); }
instance pretty_bv       = { pp   = (fun x -> Pprint.doc_of_string (show x)); }

open FStarC.Pprint

instance pretty_binding : pretty binding = {
  pp = (function Binding_var bv -> pp bv
               | Binding_lid (l, (us, t)) -> pp l ^^ colon ^^ pp t
               | Binding_univ u -> pp u);
}

let rec sigelt_to_string_short (x: sigelt) = match x.sigel with
  | Sig_pragma p ->
    show p

  | Sig_let {lbs=(false, [{lbname=lb}])} ->
    U.format1 "let %s" (lbname_to_string lb)

  | Sig_let {lbs=(true, [{lbname=lb}])} ->
    U.format1 "let rec %s" (lbname_to_string lb)

  | Sig_let {lbs=(true, lbs)} ->
    U.format1 "let rec %s" (String.concat " and " (List.map (fun lb -> lbname_to_string lb.lbname) lbs))

  | Sig_let _ ->
    failwith "Impossible: sigelt_to_string_short, ill-formed let"

  | Sig_declare_typ {lid} ->
    U.format1 "val %s" (string_of_lid lid)

  | Sig_inductive_typ {lid} ->
    U.format1 "type %s" (string_of_lid lid)

  | Sig_datacon {lid; ty_lid=t_lid} ->
    U.format2 "datacon %s for type %s" (string_of_lid lid) (string_of_lid t_lid)

  | Sig_assume {lid} ->
    U.format1 "assume %s" (string_of_lid lid)

  | Sig_bundle {ses} -> List.hd ses |> sigelt_to_string_short

  | Sig_fail {ses} ->
    U.format1 "[@@expect_failure] %s" (ses |> List.hd |> sigelt_to_string_short)

  | Sig_new_effect ed ->
    let kw =
      if SU.is_layered ed then "layered_effect"
      else if SU.is_dm4f ed then "new_effect_for_free"
      else "new_effect"
    in
    U.format2 "%s { %s ... }" kw (lid_to_string ed.mname)

  | Sig_sub_effect se ->
    U.format2 "sub_effect %s ~> %s" (lid_to_string se.source) (lid_to_string se.target)

  | Sig_effect_abbrev {lid=l; bs=tps; comp=c} ->
    U.format3 "effect %s %s = %s" (sli l)
       (String.concat " " <| List.map show tps)
       (show c)

  | Sig_splice {is_typed; lids} ->
    U.format3 "%splice%s[%s] (...)"
              "%s" // sigh, no escape for format
              (if is_typed then "_t" else "")
              (String.concat "; " <| List.map Ident.string_of_lid lids)

  | Sig_polymonadic_bind {m_lid=m; n_lid=n; p_lid=p} ->
    U.format3 "polymonadic_bind (%s, %s) |> %s"
              (Ident.string_of_lid m) (Ident.string_of_lid n) (Ident.string_of_lid p)

  | Sig_polymonadic_subcomp {m_lid=m; n_lid=n} ->
    U.format2 "polymonadic_subcomp %s <: %s" (Ident.string_of_lid m) (Ident.string_of_lid n)

let binder_to_json env b =
    let n = JsonStr (bqual_to_string' (nm_to_string b.binder_bv) b.binder_qual) in
    let t = JsonStr (term_to_string' env b.binder_bv.sort) in
    JsonAssoc [("name", n); ("type", t)]

let binders_to_json env bs =
    JsonList (List.map (binder_to_json env) bs)

let eff_decl_to_string ed =
  if Options.ugly ()
  then Ugly.eff_decl_to_string ed
  else Pretty.eff_decl_to_string ed

instance showable_eff_decl = { show = eff_decl_to_string; }

let args_to_string (args:Syntax.args) : string =
  String.concat " " <|
    List.map (fun (a, q) ->
      aqual_to_string q ^ term_to_string a) args

instance showable_decreases_order = {
  show = (function
          | Decreases_lex l -> "Decreases_lex " ^ show l
          | Decreases_wf l -> "Decreases_wf " ^ show l);
}

let cflag_to_string (c:cflag) : string =
  match c with
  | TOTAL -> "total"
  | MLEFFECT -> "ml"
  | RETURN -> "return"
  | PARTIAL_RETURN -> "partial_return"
  | SOMETRIVIAL -> "sometrivial"
  | TRIVIAL_POSTCONDITION -> "trivial_postcondition"
  | SHOULD_NOT_INLINE -> "should_not_inline"
  | LEMMA -> "lemma"
  | CPS -> "cps"
  | DECREASES do -> "decreases " ^ show do

instance showable_cflag  = { show = cflag_to_string; }

let binder_to_string_with_type b =
  if Options.ugly () then
    let attrs =
      match b.binder_attrs with
      | [] -> ""
      | ts -> "[@@@" ^ (String.concat ", " (List.map show ts)) ^ "] "
    in
    if is_null_binder b
    then attrs ^ "_:" ^ term_to_string b.binder_bv.sort
    else bqual_to_string' (attrs ^ nm_to_string b.binder_bv ^ ": " ^ term_to_string b.binder_bv.sort) b.binder_qual
  else
    Pretty.binder_to_string' false b
