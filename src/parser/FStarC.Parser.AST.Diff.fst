(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Authors: N. Swamy and Copilot
*)
module FStarC.Parser.AST.Diff

open FStarC
open FStarC.Effect
open FStarC.Ident
open FStarC.Const
open FStarC.Parser.AST

let eq_ident (i1 i2:ident) =
  Ident.ident_equals i1 i2

let eq_list (f: 'a -> 'a -> bool) (t1 t2:list 'a)
  : bool
  = List.length t1 = List.length t2 &&
    List.forall2 f t1 t2

let eq_option (f: 'a -> 'a -> bool) (t1 t2:option 'a)
  : bool
  = match t1, t2 with
    | None, None -> true
    | Some t1, Some t2 -> f t1 t2
    | _ -> false

//
// TODO: There is an eq_const in FStarC.Const.fst, can we use that?
//
let eq_sconst (c1 c2: sconst) : bool =
    match c1, c2 with
    | Const_effect, Const_effect -> true
    | Const_unit, Const_unit -> true
    | Const_bool b1, Const_bool b2 -> b1 = b2
    | Const_int (s1, sw1), Const_int (s2, sw2) -> s1=s2 && sw1=sw2
    | Const_char c1, Const_char c2 -> c1 = c2
    | Const_string (s1, _), Const_string (s2, _) -> s1 = s2
    | Const_real s1, Const_real s2 -> s1 = s2
    | Const_range r1, Const_range r2 -> r1 = r2
    | Const_reify _, Const_reify _ -> true
    | Const_reflect l1, Const_reflect l2 -> Ident.lid_equals l1 l2
    | _ -> false

let rec eq_term (t1 t2:term)
  : bool
  = eq_term' t1.tm t2.tm

and eq_terms (t1 t2:list term)
  : bool
  = eq_list eq_term t1 t2

and eq_arg (t1 t2 : (term & imp))
  = let t1, a1 = t1 in
    let t2, a2 = t2 in
    eq_term t1 t2 &&
    eq_imp a1 a2

and eq_imp (i1 i2: imp)
  = match i1, i2 with
    | FsTypApp, FsTypApp
    | Hash, Hash
    | UnivApp, UnivApp
    | Infix, Infix
    | Nothing, Nothing -> true
    | HashBrace t1, HashBrace t2 ->
      eq_term t1 t2
    | _ -> false

and eq_args (t1 t2: list (term & imp))
  : bool
  = eq_list eq_arg t1 t2

and eq_arg_qualifier (arg_qualifier1:arg_qualifier) (arg_qualifier2:arg_qualifier) : bool =
  match arg_qualifier1, arg_qualifier2 with
  | Implicit, Implicit -> true
  | Equality, Equality -> true
  | Meta t1, Meta t2 -> eq_term t1 t2
  | TypeClassArg, TypeClassArg -> true
  | _ -> false

and eq_pattern (p1 p2:pattern)
  : bool
  = eq_pattern' p1.pat p2.pat

and eq_aqual a1 a2 = eq_option eq_arg_qualifier a1 a2

and eq_pattern' (p1 p2:pattern')
  : bool
  = match p1, p2 with
    | PatWild(q1, a1), PatWild(q2, a2) ->
      eq_aqual q1 q2 &&
      eq_terms a1 a2
    | PatConst s1, PatConst s2 ->
      eq_sconst s1 s2
    | PatApp (p1, ps1), PatApp(p2, ps2) ->
      eq_pattern p1 p2 &&
      eq_list eq_pattern ps1 ps2
    | PatVar (i1, aq1, as1), PatVar(i2, aq2, as2) ->
      Ident.ident_equals i1 i2 &&
      eq_aqual aq1 aq2 &&
      eq_terms as1 as2
    | PatName l1, PatName l2 ->
      Ident.lid_equals l1 l2
    | PatOr ps1, PatOr ps2
    | PatList ps1, PatList ps2 ->
      eq_list eq_pattern ps1 ps2
    | PatTuple(ps1, b1), PatTuple(ps2, b2) ->
      eq_list eq_pattern ps1 ps2 &&
      b1 = b2
    | PatRecord ps1, PatRecord ps2 ->
      eq_list (fun (l1, p1) (l2, p2) ->
                 Ident.lid_equals l1 l2 &&
                 eq_pattern p1 p2)
              ps1 ps2
    | PatAscribed (p1, (t1, topt1)), PatAscribed (p2, (t2, topt2)) ->
      eq_pattern p1 p2 &&
      eq_term t1 t2 &&
      eq_option eq_term topt1 topt2
    | PatOp i1, PatOp i2 ->
      eq_ident i1 i2
    | PatVQuote t1, PatVQuote t2 ->
      eq_term t1 t2
    | PatRest, PatRest ->
      true
    | _ -> false

and eq_term' (t1 t2:term')
  : bool
  = match t1, t2 with
    | Wild, Wild -> true
    | Const s1, Const s2 -> eq_const s1 s2
    | Op (i1, ts1), Op (i2, ts2) ->
      eq_ident i1 i2 &&
      eq_terms ts1 ts2
    | Uvar i1, Uvar i2 ->
      eq_ident i1 i2
    | Var l1, Var l2
    | Name l1, Name l2 ->
      Ident.lid_equals l1 l2
    | Projector (l1, i1), Projector (l2, i2) ->
      Ident.lid_equals l1 l2 &&
      Ident.ident_equals i1 i2
    | Construct (l1, args1), Construct (l2, args2) ->
      Ident.lid_equals l1 l2 &&
      eq_args args1 args2
    | Function (brs1, _r1), Function (brs2, _r2) ->
      eq_list eq_branch brs1 brs2
    | Abs (ps1, t1), Abs (ps2, t2) ->
      eq_list eq_pattern ps1 ps2 &&
      eq_term t1 t2
    | App (h1, t1, i1), App(h2, t2, i2) ->
      eq_term h1 h2 &&
      eq_term t1 t2 &&
      eq_imp i1 i2
    | Let (lq1, defs1, t1), Let (lq2, defs2, t2) ->
      lq1=lq2 &&
      eq_list (fun (o1, (p1, t1)) (o2, (p2, t2)) ->
                 eq_option eq_terms o1 o2 &&
                 eq_pattern p1 p2 &&
                 eq_term t1 t2)
              defs1 defs2 &&
      eq_term t1 t2
    | LetOperator (defs1, t1), LetOperator (defs2, t2) ->
      eq_list (fun (i1, ps1, t1) (i2, ps2, t2) ->
                 eq_ident i1 i2 &&
                 eq_pattern ps1 ps2 &&
                 eq_term t1 t2)
              defs1 defs2 &&
      eq_term t1 t2
    | LetOpen (l1, t1), LetOpen (l2, t2) ->
      Ident.lid_equals l1 l2 &&
      eq_term t1 t2
    // compare all the remaining cases of terms starting with LetOperator
    | LetOpenRecord (t1, t2, t3), LetOpenRecord (t4, t5, t6) ->
      eq_term t1 t4 &&
      eq_term t2 t5 &&
      eq_term t3 t6
    | Seq (t1, t2), Seq (t3, t4) ->
      eq_term t1 t3 &&
      eq_term t2 t4
    | Bind (i1, t1, t2), Bind (i2, t3, t4) ->
      Ident.ident_equals i1 i2 &&
      eq_term t1 t3 &&
      eq_term t2 t4
    | If (t1, i1, mra1, t2, t3), If (t4, i2, mra2, t5, t6) ->
      eq_term t1 t4 &&
      eq_option eq_ident i1 i2 &&
      eq_option eq_match_returns_annotation mra1 mra2 &&
      eq_term t2 t5 &&
      eq_term t3 t6
    | Match (t1, i1, mra1, bs1), Match (t2, i2, mra2, bs2) ->
      eq_term t1 t2 &&
      eq_option eq_ident i1 i2 &&
      eq_option eq_match_returns_annotation mra1 mra2 &&
      eq_list eq_branch bs1 bs2
    | TryWith (t1, bs1), TryWith (t2, bs2) ->
      eq_term t1 t2 &&
      eq_list eq_branch bs1 bs2
    | Ascribed (t1, t2, topt1, b1), Ascribed (t3, t4, topt2, b2) ->
      eq_term t1 t3 &&
      eq_term t2 t4 &&
      eq_option eq_term topt1 topt2 &&
      b1 = b2
    | Record (topt1, fs1), Record (topt2, fs2) ->
      eq_option eq_term topt1 topt2 &&
      eq_list (fun (l1, t1) (l2, t2) ->
                 Ident.lid_equals l1 l2 &&
                 eq_term t1 t2)
              fs1 fs2
    | Project (t1, l1), Project (t2, l2) ->
      eq_term t1 t2 &&
      Ident.lid_equals l1 l2
    | Product (bs1, t1), Product (bs2, t2) ->
      eq_list eq_binder bs1 bs2 &&
      eq_term t1 t2
    | Sum (bs1, t1), Sum (bs2, t2) ->
      eq_list (fun b1 b2 ->
                 match b1, b2 with
                 | Inl b1, Inl b2 ->
                   eq_binder b1 b2
                 | Inr t1, Inr t2 ->
                   eq_term t1 t2
                 | Inl _, Inr _
                 | Inr _, Inl _ ->
                   false)
              bs1 bs2 &&
      eq_term t1 t2
    | QForall (bs1, ps1, t1), QForall (bs2, ps2, t2)
    | QExists (bs1, ps1, t1), QExists (bs2, ps2, t2) ->
      //ps1 and ps2 have type list ident * list (list term)
      // generate equality on ps1 p2
      let eq_ps (is1, ts1) (is2, ts2) =
        eq_list eq_ident is1 is2 &&
        eq_list (eq_list eq_term) ts1 ts2
      in
      eq_list eq_binder bs1 bs2 &&
      eq_ps ps1 ps2 &&
      eq_term t1 t2
    | QuantOp (i1, bs1, ps1, t1), QuantOp (i2, bs2, ps2, t2) ->
      let eq_ps (is1, ts1) (is2, ts2) =
        eq_list eq_ident is1 is2 &&
        eq_list (eq_list eq_term) ts1 ts2
      in
      Ident.ident_equals i1 i2 &&
      eq_list eq_binder bs1 bs2 &&
      eq_ps ps1 ps2 &&
      eq_term t1 t2
    // continue comparing all the remaining cases of terms, starting with Refine
    | Refine (t1, t2), Refine (t3, t4) ->
      eq_binder t1 t3 &&
      eq_term t2 t4
    // continue comparing all the remaining cases of terms, starting with NamedTyp
    | NamedTyp (i1, t1), NamedTyp (i2, t2) ->
      eq_ident i1 i2 &&
      eq_term t1 t2
    | Paren t1, Paren t2 ->
      eq_term t1 t2
    | Requires t1, Requires t2 ->
      eq_term t1 t2
    | Ensures t1, Ensures t2 ->
      eq_term t1 t2
    | LexList ts1, LexList ts2 ->
      eq_list eq_term ts1 ts2
    | WFOrder (t1, t2), WFOrder (t3, t4) ->
      eq_term t1 t3 &&
      eq_term t2 t4
    | Decreases t1, Decreases t2 ->
      eq_term t1 t2
    | Labeled (t1, s1, b1), Labeled (t2, s2, b2) ->
      eq_term t1 t2 &&
      s1 = s2 &&
      b1 = b2
    | Discrim l1, Discrim l2 ->
      Ident.lid_equals l1 l2
    | Attributes ts1, Attributes ts2 ->
      eq_list eq_term ts1 ts2
    | Antiquote t1, Antiquote t2 ->
      eq_term t1 t2
    | Quote (t1, k1), Quote (t2, k2) ->
      eq_term t1 t2 &&
      k1 = k2
    | VQuote t1, VQuote t2 ->
      eq_term t1 t2
    | CalcProof (t1, t2, cs1), CalcProof (t3, t4, cs2) ->
      eq_term t1 t3 &&
      eq_term t2 t4 &&
      eq_list eq_calc_step cs1 cs2
    | IntroForall (bs1, t1, t2), IntroForall (bs2, t3, t4) ->
      eq_list eq_binder bs1 bs2 &&
      eq_term t1 t3 &&
      eq_term t2 t4
    | IntroExists (bs1, t1, ts1, t2), IntroExists (bs2, t3, ts2, t4) ->
      eq_list eq_binder bs1 bs2 &&
      eq_term t1 t3 &&
      eq_list eq_term ts1 ts2 &&
      eq_term t2 t4
    | IntroImplies (t1, t2, b1, t3), IntroImplies (t4, t5, b2, t6) ->
      eq_term t1 t4 &&
      eq_term t2 t5 &&
      eq_binder b1 b2 &&
      eq_term t3 t6
    | IntroOr (b1, t1, t2, t3), IntroOr (b2, t4, t5, t6) ->
      b1 = b2 &&
      eq_term t1 t4 &&
      eq_term t2 t5 &&
      eq_term t3 t6
    | IntroAnd (t1, t2, t3, t4), IntroAnd (t5, t6, t7, t8) ->
      eq_term t1 t5 &&
      eq_term t2 t6 &&
      eq_term t3 t7 &&
      eq_term t4 t8
    | ElimForall (bs1, t1, ts1), ElimForall (bs2, t2, ts2) ->
      eq_list eq_binder bs1 bs2 &&
      eq_term t1 t2 &&
      eq_list eq_term ts1 ts2
    | ElimExists (bs1, t1, t2, b1, t3), ElimExists (bs2, t4, t5, b2, t6) ->
      eq_list eq_binder bs1 bs2 &&
      eq_term t1 t4 &&
      eq_term t2 t5 &&
      eq_binder b1 b2 &&
      eq_term t3 t6
    | ElimImplies (t1, t2, t3), ElimImplies (t4, t5, t6) ->
      eq_term t1 t4 &&
      eq_term t2 t5 &&
      eq_term t3 t6
    | ElimOr (t1, t2, t3, b1, t4, b2, t5), ElimOr (t6, t7, t8, b3, t9, b4, t10) ->
      eq_term t1 t6 &&
      eq_term t2 t7 &&
      eq_term t3 t8 &&
      eq_binder b1 b3 &&
      eq_term t4 t9 &&
      eq_binder b2 b4 &&
      eq_term t5 t10
    | ElimAnd (t1, t2, t3, b1, b2, t4), ElimAnd (t5, t6, t7, b3, b4, t8) ->
      eq_term t1 t5 &&
      eq_term t2 t6 &&
      eq_term t3 t7 &&
      eq_binder b1 b3 &&
      eq_binder b2 b4 &&
      eq_term t4 t8
    | ListLiteral ts1, ListLiteral ts2 ->
      eq_list eq_term ts1 ts2
    | SeqLiteral ts1, SeqLiteral ts2 ->
      eq_list eq_term ts1 ts2
    | _ -> false

and eq_calc_step (CalcStep (t1, t2, t3)) (CalcStep (t4, t5, t6)) =
    eq_term t1 t4 &&
    eq_term t2 t5 &&
    eq_term t3 t6

and eq_binder (b1 b2:binder) =
  eq_binder' b1.b b2.b &&
  eq_aqual b1.aqual b2.aqual &&
  eq_list eq_term b1.battributes b2.battributes

and eq_binder' (b1 b2:binder') =
  match b1, b2 with
  | Variable i1, Variable i2 -> eq_ident i1 i2
  | Annotated (i1, t1), Annotated (i2, t2) ->
      eq_ident i1 i2 &&
      eq_term t1 t2
  | NoName t1, NoName t2 ->
      eq_term t1 t2
  | _ -> false

and eq_match_returns_annotation (i1, t1, b1) (i2, t2, b2) =
    eq_option eq_ident i1 i2 &&
    eq_term t1 t2 &&
    b1 = b2

and eq_branch (p1, o1, t1) (p2, o2, t2) =
    eq_pattern p1 p2 &&
    eq_option eq_term o1 o2 &&
    eq_term t1 t2


let eq_tycon_record (t1 t2: tycon_record) =
  eq_list (fun (i1, a1, a2, t1) (i2, a3, a4, t2) ->
    eq_ident i1 i2 &&
    eq_aqual a1 a3 &&
    eq_list eq_term a2 a4 &&
    eq_term t1 t2) t1 t2

let eq_constructor_payload (t1 t2: constructor_payload) =
  match t1, t2 with
  | VpOfNotation t1, VpOfNotation t2 -> eq_term t1 t2
  | VpArbitrary t1, VpArbitrary t2 -> eq_term t1 t2
  | VpRecord (r1, k1), VpRecord (r2, k2) ->
    eq_tycon_record r1 r2 &&
    eq_option eq_term k1 k2
  | _ -> false

let eq_tycon (t1 t2: tycon) =
  match t1, t2 with
  | TyconAbstract (i1, bs1, k1), TyconAbstract (i2, bs2, k2) ->
    eq_ident i1 i2 &&
    eq_list eq_binder bs1 bs2 &&
    eq_option eq_term k1 k2
  | TyconAbbrev (i1, bs1, k1, t1), TyconAbbrev (i2, bs2, k2, t2) ->
    eq_ident i1 i2 &&
    eq_list eq_binder bs1 bs2 &&
    eq_option eq_term k1 k2 &&
    eq_term t1 t2
  | TyconRecord (i1, bs1, k1, a1, r1), TyconRecord (i2, bs2, k2, a2, r2) ->
    eq_ident i1 i2 &&
    eq_list eq_binder bs1 bs2 &&
    eq_option eq_term k1 k2 &&
    eq_list eq_term a1 a2 &&
    eq_tycon_record r1 r2
  | TyconVariant (i1, bs1, k1, cs1), TyconVariant (i2, bs2, k2, cs2) ->
    eq_ident i1 i2 &&
    eq_list eq_binder bs1 bs2 &&
    eq_option eq_term k1 k2 &&
    eq_list (fun (i1, o1, a1) (i2, o2, a2) ->
      eq_ident i1 i2 &&
      eq_option eq_constructor_payload o1 o2 &&
      eq_list eq_term a1 a2) cs1 cs2
  | _ -> false

let eq_lid = Ident.lid_equals

let eq_lift (t1 t2: lift) =
  eq_lid t1.msource t2.msource &&
  eq_lid t1.mdest t2.mdest &&
  (match t1.lift_op, t2.lift_op with
  | NonReifiableLift t1, NonReifiableLift t2 -> eq_term t1 t2
  | ReifiableLift (t1, t2), ReifiableLift (t3, t4) ->
    eq_term t1 t3 &&
    eq_term t2 t4
  | LiftForFree t1, LiftForFree t2 -> eq_term t1 t2
  | _ -> false)


let eq_pragma (t1 t2: pragma) =
  match t1, t2 with
  | ShowOptions, ShowOptions -> true
  | SetOptions s1, SetOptions s2 -> s1 = s2
  | ResetOptions s1, ResetOptions s2 -> eq_option (fun s1 s2 -> s1 = s2) s1 s2
  | PushOptions s1, PushOptions s2 -> eq_option (fun s1 s2 -> s1 = s2) s1 s2
  | PopOptions, PopOptions -> true
  | RestartSolver, RestartSolver -> true
  | PrintEffectsGraph, PrintEffectsGraph -> true
  | Check t1, Check t2 -> eq_term t1 t2
  | _ -> false


let eq_qualifier (t1 t2: qualifier) =
  match t1, t2 with
  | Private, Private -> true
  | Noeq, Noeq -> true
  | Unopteq, Unopteq -> true
  | Assumption, Assumption -> true
  | TotalEffect, TotalEffect -> true
  | Effect_qual, Effect_qual -> true
  | New, New -> true
  | Inline, Inline -> true
  | Visible, Visible -> true
  | Unfold_for_unification_and_vcgen, Unfold_for_unification_and_vcgen -> true
  | Inline_for_extraction, Inline_for_extraction -> true
  | Irreducible, Irreducible -> true
  | NoExtract, NoExtract -> true
  | Reifiable, Reifiable -> true
  | Reflectable, Reflectable -> true
  | Opaque, Opaque -> true
  | Logic, Logic -> true
  | _ -> false

let eq_qualifiers (t1 t2: qualifiers) =
  eq_list eq_qualifier t1 t2

let eq_restriction (restriction1 restriction2: FStarC.Syntax.Syntax.restriction) =
  let open FStarC.Syntax.Syntax in
  match restriction1, restriction2 with
  | (Unrestricted, Unrestricted) -> true
  | (AllowList l1, AllowList l2) ->
    let eq_tuple eq_fst eq_snd (a, b) (c, d) = eq_fst a c && eq_snd b d in
    eq_list (eq_tuple eq_ident (eq_option eq_ident)) l1 l2
  | _ -> false

let rec eq_decl' (d1 d2:decl') : bool =
  //generate the cases of this comparison starting with TopLevelModule
  match d1, d2 with
  | TopLevelModule lid1, TopLevelModule lid2 ->
    eq_lid lid1 lid2
  | Open (lid1, restriction1), Open (lid2, restriction2) ->
    eq_lid lid1 lid2 &&
    eq_restriction restriction1 restriction2
  | Friend lid1, Friend lid2 ->
    eq_lid lid1 lid2
  | Include (lid1, restriction1), Include (lid2, restriction2) ->
    eq_lid lid1 lid2 &&
    eq_restriction restriction1 restriction2
  | ModuleAbbrev (i1, lid1), ModuleAbbrev (i2, lid2) ->
    eq_ident i1 i2 &&
    eq_lid lid1 lid2
  | TopLevelLet (lq1, pats1), TopLevelLet (lq2, pats2) ->
    lq1=lq2 &&
    eq_list (fun (p1, t1) (p2, t2) -> eq_pattern p1 p2 && eq_term t1 t2) pats1 pats2
  | Tycon (b1, b2, tcs1), Tycon (b3, b4, tcs2) ->
    b1 = b3 &&
    b2 = b4 &&
    eq_list eq_tycon tcs1 tcs2
  | Val (i1, t1), Val (i2, t2) ->
    eq_ident i1 i2 &&
    eq_term t1 t2
  | Exception (i1, t1), Exception (i2, t2) ->
    eq_ident i1 i2 &&
    eq_option eq_term t1 t2
  | NewEffect ed1, NewEffect ed2 ->
    eq_effect_decl ed1 ed2
  | LayeredEffect ed1, LayeredEffect ed2 ->
    eq_effect_decl ed1 ed2
  | SubEffect l1, SubEffect l2 ->
    eq_lift l1 l2
  | Polymonadic_bind (lid1, lid2, lid3, t1), Polymonadic_bind (lid4, lid5, lid6, t2) ->
    eq_lid lid1 lid4 &&
    eq_lid lid2 lid5 &&
    eq_lid lid3 lid6 &&
    eq_term t1 t2
  | Polymonadic_subcomp (lid1, lid2, t1), Polymonadic_subcomp (lid3, lid4, t2) ->
    eq_lid lid1 lid3 &&
    eq_lid lid2 lid4 &&
    eq_term t1 t2
  | Pragma p1, Pragma p2 ->
    eq_pragma p1 p2
  | Assume (i1, t1), Assume (i2, t2) ->
    eq_ident i1 i2 &&
    eq_term t1 t2
  | Splice (is_typed1, is1, t1), Splice (is_typed2, is2, t2) ->
    is_typed1 = is_typed2 &&
    eq_list eq_ident is1 is2 &&
    eq_term t1 t2
  | DeclSyntaxExtension (s1, t1, _, _), DeclSyntaxExtension (s2, t2, _, _) ->
    s1 = s2 && t1 = t2
  | UseLangDecls p1, UseLangDecls p2 ->
    p1 = p2
  | DeclToBeDesugared tbs1, DeclToBeDesugared tbs2 ->
    tbs1.lang_name = tbs2.lang_name &&
    tbs1.eq tbs1.blob tbs2.blob
  | _ -> false

and eq_effect_decl (t1 t2: effect_decl) =
  match t1, t2 with
  | DefineEffect (i1, bs1, t1, ds1), DefineEffect (i2, bs2, t2, ds2) ->
    eq_ident i1 i2 &&
    eq_list eq_binder bs1 bs2 &&
    eq_term t1 t2 &&
    eq_list eq_decl ds1 ds2
  | RedefineEffect (i1, bs1, t1), RedefineEffect (i2, bs2, t2) ->
    eq_ident i1 i2 &&
    eq_list eq_binder bs1 bs2 &&
    eq_term t1 t2
  | _ -> false

and eq_decl (d1 d2:decl) : bool =
  eq_decl' d1.d d2.d &&
  eq_list eq_qualifier d1.quals d2.quals &&
  eq_list eq_term d1.attrs d2.attrs
