(*
   Copyright 2008-2015 Abhishek Anand, Nikhil Swamy and Microsoft Research

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
module FStar.Extraction.ML.Term
open FStar.ST
open FStar.Exn
open FStar.All
open FStar
open FStar.TypeChecker.Env
open FStar.Util
open FStar.Const
open FStar.Ident
open FStar.Extraction
open FStar.Extraction.ML
open FStar.Extraction.ML.Syntax
open FStar.Extraction.ML.UEnv
open FStar.Extraction.ML.Util
open FStar.Syntax.Syntax
open FStar.Errors

module Code = FStar.Extraction.ML.Code
module BU = FStar.Util
module S  = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module U  = FStar.Syntax.Util
module N  = FStar.TypeChecker.Normalize
module PC = FStar.Parser.Const
module TcEnv = FStar.TypeChecker.Env
module TcTerm = FStar.TypeChecker.TcTerm
module TcUtil = FStar.TypeChecker.Util
module R  = FStar.Reflection.Basic
module RD = FStar.Reflection.Data
module EMB = FStar.Syntax.Embeddings
module RE = FStar.Reflection.Embeddings
module Env = FStar.TypeChecker.Env

exception Un_extractable

(*
  Below, "the thesis" refers to:
    Letouzey, Pierre.
    Programmation Fonctionnelle Certifiée: L'extraction de Programmes Dans L'assistant Coq.
    Université Paris-Sud, 2004.

    English translation:
        Certified Functional Programming
            Program extraction within the Coq proof assistant
    http://www.pps.univ-paris-diderot.fr/~letouzey/download/these_letouzey_English.ps.gz
*)

let type_leq g t1 t2 = Util.type_leq (Util.udelta_unfold g) t1 t2
let type_leq_c g t1 t2 = Util.type_leq_c (Util.udelta_unfold g) t1 t2
let eraseTypeDeep g t = Util.eraseTypeDeep (Util.udelta_unfold g) t

module Print = FStar.Syntax.Print


(* taramana 2016-10-31: we redefine
FStar.Extraction.ML.BU.record_fields here because the desugaring
of field names has changed, but we cannot change the definition in
FStar.Extraction.ML.Util for now because it is used by legacy
extraction, which is still used in the bootstrapping process *)

let record_fields fs vs = List.map2 (fun (f:ident) e -> f.idText, e) fs vs

(********************************************************************************************)
(* Some basic error reporting; all are fatal errors at this stage                           *)
(********************************************************************************************)
let fail r err =
    Errors.raise_error err r

let err_uninst env (t:term) (vars, ty) (app:term) =
    fail t.pos (Fatal_Uninstantiated, (BU.format4 "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated, but got %s"
                    (Print.term_to_string t)
                    (vars |> String.concat ", ")
                    (Code.string_of_mlty env.currentModule ty)
                    (Print.term_to_string app)))

let err_ill_typed_application env (t : term) mlhead args (ty : mlty) =
    fail t.pos (Fatal_IllTyped, (BU.format4 "Ill-typed application: source application is %s \n translated prefix to %s at type %s\n remaining args are %s\n"
                (Print.term_to_string t)
                (Code.string_of_mlexpr env.currentModule mlhead)
                (Code.string_of_mlty env.currentModule ty)
                (args |> List.map (fun (x, _) -> Print.term_to_string x) |> String.concat " ")))

let err_ill_typed_erasure env pos (ty : mlty) =
    fail pos (Fatal_IllTyped, (BU.format1 "Erased value found where a value of type %s was expected"
                (Code.string_of_mlty env.currentModule ty)))

let err_value_restriction t =
    fail t.pos (Fatal_ValueRestriction, (BU.format2 "Refusing to generalize because of the value restriction: (%s) %s"
                    (Print.tag_of_term t) (Print.term_to_string t)))

let err_unexpected_eff env t ty f0 f1 =
    Errors.log_issue t.pos (Warning_ExtractionUnexpectedEffect,
                BU.format4 "for expression %s of type %s, Expected effect %s; got effect %s"
                        (Print.term_to_string t)
                        (Code.string_of_mlty env.currentModule ty)
                        (eff_to_string f0)
                        (eff_to_string f1))

(***********************************************************************)
(* Translating an effect lid to an e_tag = {E_PURE, E_GHOST, E_IMPURE} *)
(***********************************************************************)
let effect_as_etag =
    let cache = BU.smap_create 20 in
    let rec delta_norm_eff g (l:lident) =
        match BU.smap_try_find cache l.str with
            | Some l -> l
            | None ->
                let res = match TypeChecker.Env.lookup_effect_abbrev g.env_tcenv [S.U_zero] l with
                | None -> l
                | Some (_, c) -> delta_norm_eff g (U.comp_effect_name c) in
                BU.smap_add cache l.str res;
                res in
    fun g l ->
        let l = delta_norm_eff g l in
        if lid_equals l PC.effect_PURE_lid
        then E_PURE
        else if lid_equals l PC.effect_GHOST_lid
        then E_GHOST
        else
            // Reifiable effects should be pure. Added guard because some effect declarations
            // don't seem to be in the environment at this point, in particular FStar.All.ML
            // (maybe because it's primitive?)
            let ed_opt = TcEnv.effect_decl_opt g.env_tcenv l in
            match ed_opt with
            | Some (ed, qualifiers) ->
                if TcEnv.is_reifiable_effect g.env_tcenv ed.mname
                then E_PURE
                else E_IMPURE
            | None -> E_IMPURE

(********************************************************************************************)
(* Basic syntactic operations on a term                                                     *)
(********************************************************************************************)

(* is_arity t:
         t is a sort s, i.e., Type i
     or, t = x1:t1 -> ... -> xn:tn -> C
             where PC.result_type is an arity

 *)
let rec is_arity env t =
    let t = U.unmeta t in
    match (SS.compress t).n with
    | Tm_unknown
    | Tm_delayed _
    | Tm_ascribed _
    | Tm_meta _ -> failwith "Impossible"
    | Tm_lazy i -> is_arity env (U.unfold_lazy i)
    | Tm_uvar _
    | Tm_constant _
    | Tm_name _
    | Tm_quoted _
    | Tm_bvar _ -> false
    | Tm_type _ -> true
    | Tm_arrow(_, c) ->
      is_arity env (FStar.Syntax.Util.comp_result c)
    | Tm_fvar _ ->
      let t = N.normalize [Env.AllowUnboundUniverses; Env.EraseUniverses; Env.UnfoldUntil delta_constant] env.env_tcenv t in
      begin match (SS.compress t).n with
        | Tm_fvar _ -> false
        | _ -> is_arity env t
      end
    | Tm_app _ ->
      let head, _ = U.head_and_args t in
      is_arity env head
    | Tm_uinst(head, _) ->
      is_arity env head
    | Tm_refine(x, _) ->
      is_arity env x.sort
    | Tm_abs(_, body, _)
    | Tm_let(_, body) ->
      is_arity env body
    | Tm_match(_, branches) ->
      begin match branches with
        | (_, _, e)::_ -> is_arity env e
        | _ -> false
      end

//is_type_aux env t:
//     Determines whether or not t is a type
//     syntactic structure and type annotations
let rec is_type_aux env t =
    let t = SS.compress t in
    match t.n with
    | Tm_delayed _
    | Tm_unknown ->
        failwith (BU.format1 "Impossible: %s" (Print.tag_of_term t))

    | Tm_lazy i -> is_type_aux env (U.unfold_lazy i)

    | Tm_constant _ ->
      false

    | Tm_type _
    | Tm_refine _
    | Tm_arrow _ ->
      true

    | Tm_fvar fv when S.fv_eq_lid fv PC.failwith_lid ->
      false //special case this, since we emit it during extraction even in prims, before it is in the F* scope

    | Tm_fvar fv ->
      UEnv.is_type_name env fv

    | Tm_uvar ({ctx_uvar_typ=t}, s) ->
      is_arity env (SS.subst' s t)

    | Tm_bvar ({sort=t})
    | Tm_name ({sort=t}) ->
      is_arity env t

    | Tm_ascribed(t, _, _) ->
      is_type_aux env t

    | Tm_uinst(t, _) ->
      is_type_aux env t

    | Tm_abs(bs, body, _) ->
      let _, body = SS.open_term bs body in
      is_type_aux env body

    | Tm_let((false, [lb]), body) ->
      let x = BU.left lb.lbname in
      let _, body = SS.open_term [S.mk_binder x] body in
      is_type_aux env body

    | Tm_let((_, lbs), body) ->
      let _, body = SS.open_let_rec lbs body in
      is_type_aux env body

    | Tm_match(_, branches) ->
      begin match branches with
        | b::_ ->
          let _, _, e = SS.open_branch b in
          is_type_aux env e
        | _ -> false
      end

    | Tm_quoted _ -> false

    | Tm_meta(t, _) ->
      is_type_aux env t

    | Tm_app(head, _) ->
      is_type_aux env head

let is_type env t =
    debug env (fun () -> BU.print2 "checking is_type (%s) %s\n"
                                (Print.tag_of_term t)
                                (Print.term_to_string t)
                                );
    let b = is_type_aux env t in
    debug env (fun _ ->
        if b
        then BU.print2 "yes, is_type %s (%s)\n" (Print.term_to_string t) (Print.tag_of_term t)
        else BU.print2 "not a type %s (%s)\n" (Print.term_to_string t) (Print.tag_of_term t));
    b

let is_type_binder env x = is_arity env (fst x).sort

let is_constructor t = match (SS.compress t).n with
    | Tm_fvar ({fv_qual=Some Data_ctor})
    | Tm_fvar ({fv_qual=Some (Record_ctor _)}) -> true
    | _ -> false

(* something is a value iff it qualifies for the OCaml's "value restriction",
   which determines when a definition can be generalized *)
let rec is_fstar_value (t:term) =
    match (SS.compress t).n with
    | Tm_constant _
    | Tm_bvar _
    | Tm_fvar _
    | Tm_abs _  -> true
    | Tm_app(head, args) ->
        if is_constructor head
        then args |> List.for_all (fun (te, _) -> is_fstar_value te)
        else false
        (* Consider:
               let f (a:Type) (x:a) : Tot a = x
               let g = f int

           In principle, after erasure, g can be generalized.
           But, we don't distinguish type- from term applications right now
           and consider (f int) to be non-generalizable non-value.

           This may cause extraction to eta-expand g, which isn't terrible,
           but we should improve it.
        *)
    | Tm_meta(t, _)
    | Tm_ascribed(t, _, _) -> is_fstar_value t
    | _ -> false

let rec is_ml_value e =
    match e.expr with
    | MLE_Const _
    | MLE_Var   _
    | MLE_Name  _
    | MLE_Fun   _ -> true
    | MLE_CTor (_, exps)
    | MLE_Tuple exps -> BU.for_all is_ml_value exps
    | MLE_Record (_, fields) -> BU.for_all (fun (_, e) -> is_ml_value e) fields
    | MLE_TApp (h, _) -> is_ml_value h
    | _ -> false

(*copied from ocaml-asttrans.fs*)
let fresh = let c = mk_ref 0 in
            fun (x:string) -> (incr c; x ^ string_of_int (!c))

//pre-condition: SS.compress t = Tm_abs _
//Collapses adjacent abstractions into a single n-ary abstraction
let normalize_abs (t0:term) : term =
    let rec aux bs t copt =
        let t = SS.compress t in
        match t.n with
            | Tm_abs(bs', body, copt) -> aux (bs@bs') body copt
            | _ ->
              let e' = U.unascribe t in
              if U.is_fun e'
              then aux bs e' copt
              else U.abs bs e' copt in
   aux [] t0 None

let unit_binder = S.mk_binder <| S.new_bv None t_unit

//check_pats_for_ite l:
//    A helper to enable translating boolean matches back to if/then/else
let check_pats_for_ite (l:list<(pat * option<term> * term)>) : (bool   //if l is pair of boolean branches
                                                             * option<term>  //the 'then' case
                                                             * option<term>) = //the 'else' case
    let def = false, None, None in
    if List.length l <> 2 then def
    else
        let (p1, w1, e1) = List.hd l in
        let (p2, w2, e2) = List.hd (List.tl l) in
        match (w1, w2, p1.v, p2.v) with
            | (None, None, Pat_constant (Const_bool true), Pat_constant (Const_bool false)) -> true, Some e1, Some e2
            | (None, None, Pat_constant (Const_bool false), Pat_constant (Const_bool true)) -> true, Some e2, Some e1
//            | (None, None, Pat_constant (Const_bool false), Pat_wild _)
//            | (None, None, Pat_constant (Const_bool false), Pat_var _)
//            | (None, None, Pat_constant (Const_bool true), Pat_wild _)
//            | (None, None, Pat_constant (Const_bool true), Pat_var _)

            | _ -> def


(* INVARIANT: we MUST always perform deep erasure after extraction of types, even
 * when done indirectly e.g. translate_typ_of_arg below.
 * Otherwise, there will be Obj.magic because the types get erased at some places
 * and not at other places *)
//let translate_typ (g:env) (t:typ) : mlty = eraseTypeDeep g (TypeExtraction.ext g t)
//let translate_typ_of_arg (g:env) (a:arg) : mlty = eraseTypeDeep g (TypeExtraction.getTypeFromArg g a)
// erasing here is better because if we need to generate OCaml types for binders and return values, they will be accurate. By the time we reach maybe_coerce, we cant change those


(********************************************************************************************)
(* Operations on ml terms, types, and effect tags                                           *)
(*     1. Instantiation of type schemes                                                     *)
(*     2. Erasure of terms                                                                  *)
(*     3. Coercion (Obj.magic)                                                              *)
(********************************************************************************************)
//instantiate s args:
//      only handles fully applied types,
//      pre-condition: List.length (fst s) = List.length args
let instantiate (s:mltyscheme) (args:list<mlty>) : mlty = Util.subst s args

(* eta-expand `e` according to its type `t` *)
let eta_expand (t : mlty) (e : mlexpr) : mlexpr =
    let ts, r = doms_and_cod t in
    if ts = [] then e else // just quit if this is not a function type
    let vs = List.map (fun _ -> fresh "a") ts in
    let vs_ts = List.zip vs ts in
    let vs_es = List.map (fun (v, t) -> with_ty t (MLE_Var v)) (List.zip vs ts) in
    let body = with_ty r <| MLE_App (e, vs_es) in
    with_ty t <| MLE_Fun (vs_ts, body)

(* eta-expand `e` according to its type `t` *)
let default_value_for_ty (g:uenv) (t : mlty) : mlexpr =
    let ts, r = doms_and_cod t in
    let body r =
        let r =
            match udelta_unfold g r with
            | None -> r
            | Some r -> r
        in
        match r with
        | MLTY_Erased ->
          ml_unit
        | MLTY_Top ->
          apply_obj_repr ml_unit MLTY_Erased
        | _ ->
          with_ty r <| MLE_Coerce (ml_unit, MLTY_Erased, r)
    in
    if ts = []
    then body r
    else let vs = List.map (fun _ -> fresh "a") ts in
         let vs_ts = List.zip vs ts in
         with_ty t <| MLE_Fun (vs_ts, body r)

let maybe_eta_expand expect e =
    if Options.ml_no_eta_expand_coertions () ||
        Options.codegen () = Some Options.Kremlin // we need to stay first order for Kremlin
    then e
    else eta_expand expect e

(*
  A small optimization to push coercions into the structure of a term

  Otherwise, we often end up with coercions like (Obj.magic (fun x -> e) : a -> b) : a -> c
  Whereas with this optimization we produce (fun x -> Obj.magic (e : b) : c)  : a -> c
*)
let apply_coercion (g:uenv) (e:mlexpr) (ty:mlty) (expect:mlty) : mlexpr =
    let mk_fun binder body =
        match body.expr with
        | MLE_Fun(binders, body) ->
          MLE_Fun(binder::binders, body)
        | _ ->
          MLE_Fun([binder], body)
    in
    let rec aux (e:mlexpr) ty expect =
        let coerce_branch (pat, w, b) = pat, w, aux b ty expect in
        //printfn "apply_coercion: %s : %s ~> %s\n%A : %A ~> %A"
        //                   (Code.string_of_mlexpr g.currentModule e)
        //                   (Code.string_of_mlty g.currentModule ty)
        //                   (Code.string_of_mlty g.currentModule expect)
        //                   e ty expect;
        match e.expr, ty, expect with
        | MLE_Fun(arg::rest, body), MLTY_Fun(t0, _, t1), MLTY_Fun(s0, _, s1) ->
          let body =
                 match rest with
                 | [] -> body
                 | _ -> with_ty t1 (MLE_Fun(rest, body))
          in
          let body = aux body t1 s1 in
          if type_leq g s0 t0
          then with_ty expect (mk_fun arg body)
          else let lb =
                    { mllb_meta = [];
                      mllb_name = fst arg;
                      mllb_tysc = Some ([], t0);
                      mllb_add_unit = false;
                      mllb_def = with_ty t0 (MLE_Coerce(with_ty s0 <| MLE_Var (fst arg), s0, t0));
                      print_typ=false }
                in
                let body = with_ty s1 <| MLE_Let((NonRec, [lb]), body) in
                with_ty expect (mk_fun (fst arg, s0) body)

        | MLE_Let(lbs, body), _, _ ->
          with_ty expect <| (MLE_Let(lbs, aux body ty expect))

        | MLE_Match(s, branches), _, _ ->
          with_ty expect <| MLE_Match(s, List.map coerce_branch branches)

        | MLE_If(s, b1, b2_opt), _, _ ->
          with_ty expect <| MLE_If(s, aux b1 ty expect, BU.map_opt b2_opt (fun b2 -> aux b2 ty expect))

        | MLE_Seq es, _, _ ->
          let prefix, last = BU.prefix es in
          with_ty expect <| MLE_Seq(prefix @ [aux last ty expect])

        | MLE_Try(s, branches), _, _ ->
          with_ty expect <| MLE_Try(s, List.map coerce_branch branches)

        | _ ->
          with_ty expect (MLE_Coerce(e, ty, expect))
    in
    aux e ty expect

//maybe_coerce g e ty expect:
//     Inserts an Obj.magic around e if ty </: expect
let maybe_coerce pos (g:uenv) e ty (expect:mlty) : mlexpr  =
    let ty = eraseTypeDeep g ty in
    match type_leq_c g (Some e) ty expect with
    | true, Some e' -> e'
    | _ ->
        match ty with
        | MLTY_Erased ->
          //generate a default value suitable for the expected type
          default_value_for_ty g expect
        | _ ->
          if type_leq g (erase_effect_annotations ty) (erase_effect_annotations expect)
          then let _ = debug g (fun () ->
                BU.print2 "\n Effect mismatch on type of %s : %s\n"
                            (Code.string_of_mlexpr g.currentModule e)
                            (Code.string_of_mlty g.currentModule ty)) in
               e //types differ but only on effect labels, which ML/KreMLin don't care about; so no coercion needed
          else let _ = debug g (fun () ->
                BU.print3 "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n"
                            (Code.string_of_mlexpr g.currentModule e)
                            (Code.string_of_mlty g.currentModule ty)
                            (Code.string_of_mlty g.currentModule expect)) in
               maybe_eta_expand expect (apply_coercion g e ty expect)

(********************************************************************************************)
(* The main extraction of terms to ML types                                                 *)
(********************************************************************************************)
let bv_as_mlty (g:uenv) (bv:bv) =
    match UEnv.lookup_bv g bv with
        | Inl ty_b -> ty_b.ty_b_ty
        | _ -> MLTY_Top


(* term_as_mlty g t:
           Inspired by the \hat\epsilon function in the thesis (Sec. 3.3.5)

    pre-condition: is_type t

    First \beta, \iota and \zeta reduce ft.
    Since F* does not have SN, one has to be more careful for the termination argument.
    Because OCaml does not support computations in Type, unknownType is supposed to be used if they are really unaviodable.
    The classic example is the type : T b \def if b then nat else bool. If we dont compute, T true will extract to unknownType.
    Why not \delta? I guess the reason is that unfolding definitions will make the resultant OCaml code less readable.
    However in the Typ_app case,  \delta reduction is done as the second-last resort, just before giving up and returing unknownType;
        a bloated type is atleast as good as unknownType?
    An an F* specific example, unless we unfold Mem x pre post to StState x wp wlp, we have no idea that it should be translated to x
*)
let basic_norm_steps = [
                Env.Beta;
                Env.Eager_unfolding;
                Env.Iota;
                Env.Zeta;
                Env.Inlining;
                Env.EraseUniverses;
                Env.AllowUnboundUniverses
    ]

let comp_no_args c =
    match c.n with
    | Total _
    | GTotal _ -> c
    | Comp ct ->
       let effect_args = List.map (fun (_, aq) -> (S.t_unit, aq)) ct.effect_args in
       let ct = { ct with effect_args = effect_args } in
       let c = { c with n = Comp ct } in
       c

let rec translate_term_to_mlty (g:uenv) (t0:term) : mlty =
    let arg_as_mlty (g:uenv) (a, _) : mlty =
        if is_type g a //This is just an optimization; we could in principle always emit erasedContent, at the expense of more magics
        then translate_term_to_mlty g a
        else erasedContent
    in

    let fv_app_as_mlty (g:uenv) (fv:fv) (args : args) : mlty =
        if not (is_fv_type g fv)
        then MLTY_Top //it was translated as an expression or erased
        else
            let formals, _ =
                let (_, fvty), _ = FStar.TypeChecker.Env.lookup_lid g.env_tcenv fv.fv_name.v in
                let fvty = N.normalize [Env.UnfoldUntil delta_constant] g.env_tcenv fvty in
                U.arrow_formals fvty in
            let mlargs = List.map (arg_as_mlty g) args in
            let mlargs =
                let n_args = List.length args in
                if List.length formals > n_args //it's not fully applied; so apply the rest to unit
                then let _, rest = BU.first_N n_args formals in
                     mlargs @ (List.map (fun _ -> erasedContent) rest)
                else mlargs in
            let nm = match maybe_mangle_type_projector g fv with
                     | Some p ->
                       p
                     | None ->
                       mlpath_of_lident fv.fv_name.v in
            MLTY_Named (mlargs, nm)

    in

    let aux env t =
         let t = SS.compress t in
         match t.n with
          | Tm_type _ -> MLTY_Erased

          | Tm_bvar _
          | Tm_delayed _
          | Tm_unknown -> failwith (BU.format1 "Impossible: Unexpected term %s" (Print.term_to_string t))

          | Tm_lazy i -> translate_term_to_mlty env (U.unfold_lazy i)

          | Tm_constant _ -> unknownType
          | Tm_quoted _ -> unknownType

          | Tm_uvar _ -> unknownType //really shouldn't have any uvars left; TODO: fatal failure?

          | Tm_meta(t, _)
          | Tm_refine({sort=t}, _)
          | Tm_uinst(t, _)
          | Tm_ascribed(t, _, _) -> translate_term_to_mlty env t

          | Tm_name bv ->
            bv_as_mlty env bv

          | Tm_fvar fv ->
            (* it is not clear whether description in the thesis covers type applications with 0 args.
               However, this case is needed to translate types like nnat, and so far seems to work as expected*)
            fv_app_as_mlty env fv []

          | Tm_arrow(bs, c) ->
            let bs, c = SS.open_comp bs c in
            let mlbs, env = binders_as_ml_binders env bs in
            let t_ret =
                let eff = TcEnv.norm_eff_name env.env_tcenv (U.comp_effect_name c) in
                let c = comp_no_args c in
                let ed, qualifiers = must (TcEnv.effect_decl_opt env.env_tcenv eff) in
                if TcEnv.is_reifiable_effect g.env_tcenv ed.mname
                then let t = FStar.TypeChecker.Env.reify_comp env.env_tcenv c U_unknown in
                     debug env (fun () -> BU.print2 "Translating comp type %s as %s\n"
                            (Print.comp_to_string c) (Print.term_to_string t));
                     let res = translate_term_to_mlty env t in
                     debug env (fun () -> BU.print3 "Translated comp type %s as %s ... to %s\n"
                            (Print.comp_to_string c) (Print.term_to_string t) (Code.string_of_mlty env.currentModule res));
                     res
                else translate_term_to_mlty env (U.comp_result c) in
            let erase = effect_as_etag env (U.comp_effect_name c) in
            let _, t = List.fold_right (fun (_, t) (tag, t') -> (E_PURE, MLTY_Fun(t, tag, t'))) mlbs (erase, t_ret) in
            t

          (*can this be a partial type application? , i.e can the result of this application be something like Type -> Type, or nat -> Type? : Yes *)
          (* should we try to apply additional arguments here? if not, where? FIX!! *)
          | Tm_app (head, args) ->
            let res = match (U.un_uinst head).n with
                | Tm_name bv ->
                  (*the args are thrown away, because in OCaml, type variables have type Type and not something like -> .. -> .. Type *)
                  bv_as_mlty env bv

                | Tm_fvar fv ->
                  fv_app_as_mlty env fv args

                | Tm_app (head, args') ->
                  translate_term_to_mlty env (S.mk (Tm_app(head, args'@args)) None t.pos)

                | _ -> unknownType in
            res

          | Tm_abs(bs,ty,_) ->  (* (sch) rule in \hat{\epsilon} *)
            (* We just translate the body in an extended environment; the binders will just end up as units *)
            let bs, ty = SS.open_term bs ty in
            let bts, env = binders_as_ml_binders env bs in
            translate_term_to_mlty env ty

          | Tm_let _
          | Tm_match _ -> unknownType
    in

    let rec is_top_ty t = match t with
        | MLTY_Top -> true
        | MLTY_Named _ ->
          begin match Util.udelta_unfold g t with
                | None -> false
                | Some t -> is_top_ty t
          end
        | _ -> false
    in
    if TcUtil.must_erase_for_extraction g.env_tcenv t0 then MLTY_Erased
    else let mlt = aux g t0 in
         if is_top_ty mlt
         then //Try normalizing t fully, this time with Delta steps, and translate again, to see if we can get a better translation for it
              let t = N.normalize (Env.UnfoldUntil delta_constant::basic_norm_steps) g.env_tcenv t0 in
              aux g t
    else mlt


and binders_as_ml_binders (g:uenv) (bs:binders) : list<(mlident * mlty)> * uenv =
    let ml_bs, env = bs |> List.fold_left (fun (ml_bs, env) b ->
            if is_type_binder g b
            then //no first-class polymorphism; so type-binders get wiped out
                    let b = fst b in
                    let env = extend_ty env b (Some MLTY_Top) in
                    let ml_b = (bv_as_ml_termvar b (*name of the binder*),
                                ml_unit_ty (*type of the binder. correspondingly, this argument gets converted to the unit value in application *)) in
                    ml_b::ml_bs, env
            else let b = fst b in
                 let t = translate_term_to_mlty env b.sort in
                 let env, b, _ = extend_bv env b ([], t) false false false in
                 let ml_b = (removeTick b, t) in
                 ml_b::ml_bs, env)
    ([], g) in
    List.rev ml_bs,
    env

let term_as_mlty g t0 =
    let t = N.normalize basic_norm_steps g.env_tcenv t0 in
    translate_term_to_mlty g t


//////////////////////////////////////////////////////////////////////////////////////////////
(********************************************************************************************)
(* The main extraction of terms to ML expressions                                           *)
(********************************************************************************************)
//////////////////////////////////////////////////////////////////////////////////////////////

//A peephole optimizer for sequences
let mk_MLE_Seq e1 e2 = match e1.expr, e2.expr with
    | MLE_Seq es1, MLE_Seq es2 -> MLE_Seq (es1@es2)
    | MLE_Seq es1, _ -> MLE_Seq (es1@[e2])
    | _, MLE_Seq es2 -> MLE_Seq (e1::es2)
    | _ -> MLE_Seq [e1; e2]

//A peephole optimizer for let
(*
 1. Optimize (let x : unit = e in ()) to e
 2. Optimize (let x : unit = e in x) to e
 3. Optimize (let x : unit = () in e) to e
 4. Optimize (let x : unit = e in e') to e;e
*)
let mk_MLE_Let top_level (lbs:mlletbinding) (body:mlexpr) =
    match lbs with
       | (NonRec, [lb]) when not top_level ->
         (match lb.mllb_tysc with
          | Some ([], t) when (t=ml_unit_ty) ->
            if body.expr=ml_unit.expr
            then lb.mllb_def.expr //case 1
            else (match body.expr with
                  | MLE_Var x when (x=lb.mllb_name) -> lb.mllb_def.expr //case 2
                  | _ when (lb.mllb_def.expr=ml_unit.expr) -> body.expr //case 3
                  | _ -> mk_MLE_Seq lb.mllb_def body) //case 4
          | _ -> MLE_Let(lbs, body))
       | _ -> MLE_Let(lbs, body)

let resugar_pat q p = match p with
    | MLP_CTor(d, pats) ->
      begin
         if is_xtuple d
         then MLP_Tuple(pats)
         else match q with
              | Some (Record_ctor (ty, fns)) ->
                  let path = List.map text_of_id ty.ns in
                  let fs = record_fields fns pats in
                  MLP_Record(path, fs)
              | _ -> p
      end
    | _ -> p

//extract_pat g p expected_t
//     Translates an F* pattern to an ML pattern
//     The main work is erasing inaccessible (dot) patterns
//     And turning F*'s curried pattern style to ML's fully applied ones
let rec extract_one_pat (imp : bool)
                        (g:uenv)
                        (p:S.pat)
                        (expected_topt:option<mlty>)
                        (term_as_mlexpr:uenv -> S.term -> (mlexpr * e_tag * mlty))
    : uenv * option<(mlpattern * list<mlexpr>)> * bool =
    let ok t =
        match expected_topt with
        | None -> true
        | Some t' ->
            let ok = type_leq g t t' in
            if not ok then debug g (fun _ -> BU.print2 "Expected pattern type %s; got pattern type %s\n"
                                                (Code.string_of_mlty g.currentModule t')
                                                (Code.string_of_mlty g.currentModule t));
            ok
    in
    match p.v with
    | Pat_constant (Const_int (c, swopt))
      when Options.codegen() <> Some Options.Kremlin ->
      //Kremlin supports native integer constants in patterns
      //Don't convert them into `when` clauses
        let mlc, ml_ty =
            match swopt with
            | None ->
              with_ty ml_int_ty <| (MLE_Const (mlconst_of_const p.p (Const_int (c, None)))),
              ml_int_ty
            | Some sw ->
              let source_term =
                  FStar.ToSyntax.ToSyntax.desugar_machine_integer g.env_tcenv.dsenv c sw Range.dummyRange in
              let mlterm, _, mlty = term_as_mlexpr g source_term in
              mlterm, mlty
        in
        //these may be extracted to bigint, in which case, we need to emit a when clause
        let x = gensym() in // as_mlident (S.new_bv None Tm_bvar) in
        let when_clause = with_ty ml_bool_ty <|
            MLE_App(prims_op_equality, [with_ty ml_ty <| MLE_Var x;
                                        mlc]) in
        g, Some (MLP_Var x, [when_clause]), ok ml_ty

    | Pat_constant s     ->
        let t : term = TcTerm.tc_constant g.env_tcenv Range.dummyRange s in
        let mlty = term_as_mlty g t in
        g, Some (MLP_Const (mlconst_of_const p.p s), []), ok mlty

    | Pat_var x | Pat_wild x ->
        // JP,NS: Pat_wild turns into a binder in the internal syntax because
        // the types of other terms may depend on it
        let mlty = term_as_mlty g x.sort in
        let g, x, _ = extend_bv g x ([], mlty) false false imp in
        g, (if imp then None else Some (MLP_Var x, [])), ok mlty

    | Pat_dot_term _ ->
        g, None, true

    | Pat_cons (f, pats) ->
        let d, tys = match lookup_fv g f with
            | {exp_b_expr={expr=MLE_Name n}; exp_b_tscheme=ttys} -> n, ttys
            | _ -> failwith "Expected a constructor" in
        let nTyVars = List.length (fst tys) in
        let tysVarPats, restPats =  BU.first_N nTyVars pats in
        let f_ty_opt =
                try
                    let mlty_args = tysVarPats |> List.map (fun (p, _) ->
                        match p.v with
                        | Pat_dot_term (_, t) -> term_as_mlty g t
                        | _ ->
                            debug g (fun _ -> BU.print1 "Pattern %s is not extractable" (Print.pat_to_string p));
                            raise Un_extractable) in
                    let f_ty = subst tys mlty_args in
                    Some (Util.uncurry_mlty_fun f_ty)
                with Un_extractable -> None in

        let g, tyMLPats = BU.fold_map (fun g (p, imp) ->
            let g, p, _ = extract_one_pat true g p None term_as_mlexpr in
            g, p) g tysVarPats in (*not all of these were type vars in ML*)

        let (g, f_ty_opt), restMLPats = BU.fold_map (fun (g, f_ty_opt) (p, imp) ->
            let f_ty_opt, expected_ty = match f_ty_opt with
                | Some (hd::rest, res) -> Some (rest, res), Some hd
                | _ -> None, None in
            let g, p, _ = extract_one_pat false g p expected_ty term_as_mlexpr in
            (g, f_ty_opt), p) (g, f_ty_opt) restPats in

        let mlPats, when_clauses = List.append tyMLPats restMLPats |> List.collect (function (Some x) -> [x] | _ -> []) |> List.split in
        let pat_ty_compat = match f_ty_opt with
            | Some ([], t) -> ok t
            | _ -> false in
        g, Some (resugar_pat f.fv_qual (MLP_CTor (d, mlPats)), when_clauses |> List.flatten), pat_ty_compat

let extract_pat (g:uenv) (p:S.pat) (expected_t:mlty)
                (term_as_mlexpr: uenv -> S.term -> (mlexpr * e_tag * mlty))
    : (uenv * list<(mlpattern * option<mlexpr>)> * bool) =
    let extract_one_pat g p expected_t =
        match extract_one_pat false g p expected_t term_as_mlexpr with
        | g, Some (x, v), b -> g, (x, v), b
        | _ -> failwith "Impossible: Unable to translate pattern"
    in
    let mk_when_clause whens =
        match whens with
        | [] -> None
        | hd::tl -> Some (List.fold_left conjoin hd tl)
    in
    let g, (p, whens), b = extract_one_pat g p (Some expected_t) in
    let when_clause = mk_when_clause whens in
    g, [(p, when_clause)], b

(*
  maybe_lalloc_eta_data_and_project_record g qual residualType mlAppExpr:

      Preconditions:
       1) residualType is the type of mlAppExpr
       2) mlAppExpr is an MLE_Name or an MLE_App with its head a named fvar,
          and isDataCons is true iff it names a data constructor of a data type.

      Postconditions:
       1) the return value (say r) also has type residualType and its
          extraction-preimage is definitionally equal in F* to that of mlAppExpr
       2) meets the ML requirements that the args to datacons be tupled
          and that the datacons be fully applied
       3) In case qual is record projector and mlAppExpr is of the form (f e),
          emits e.f instead, since record projection is primitive in ML
*)
let maybe_eta_data_and_project_record (g:uenv) (qual : option<fv_qual>) (residualType : mlty)  (mlAppExpr : mlexpr) : mlexpr =
    let rec eta_args more_args t = match t with
        | MLTY_Fun (t0, _, t1) ->
          let x = gensym () in
          eta_args (((x, t0), with_ty t0 <| MLE_Var x)::more_args) t1
        | MLTY_Named (_, _) -> List.rev more_args, t
        | _ -> failwith (BU.format2 "Impossible: Head type is not an arrow: (%s : %s)"
                                (Code.string_of_mlexpr g.currentModule mlAppExpr)
                                (Code.string_of_mlty g.currentModule t))
                                in

   let as_record qual e =
        match e.expr, qual with
            | MLE_CTor(_, args), Some (Record_ctor(tyname, fields)) ->
               let path = List.map text_of_id tyname.ns in
               let fields = record_fields fields args in
               with_ty e.mlty <| MLE_Record(path, fields)
            | _ -> e in

    let resugar_and_maybe_eta qual e =
        let eargs, tres = eta_args [] residualType in
        match eargs with
            | [] -> Util.resugar_exp (as_record qual e)
            | _ ->
                let binders, eargs = List.unzip eargs in
                match e.expr with
                    | MLE_CTor(head, args) ->
                      let body = Util.resugar_exp <| (as_record qual <| (with_ty tres <| MLE_CTor(head, args@eargs))) in
                      with_ty e.mlty <| MLE_Fun(binders, body)
                    | _ -> failwith "Impossible: Not a constructor" in

    match mlAppExpr.expr, qual with
        | _, None -> mlAppExpr

        | MLE_App({expr=MLE_Name mlp}, mle::args), Some (Record_projector (constrname, f))
        | MLE_App({expr=MLE_TApp({expr=MLE_Name mlp}, _)}, mle::args), Some (Record_projector (constrname, f))->
          let f = lid_of_ids (constrname.ns @ [f]) in
          let fn = Util.mlpath_of_lid f in
          let proj = MLE_Proj(mle, fn) in
          let e = match args with
            | [] -> proj
            | _ -> MLE_App(with_ty MLTY_Top <| proj, args) in //TODO: Fix imprecise with_ty on the projector
          with_ty mlAppExpr.mlty e

        | MLE_App ({expr=MLE_Name mlp}, mlargs), Some Data_ctor
        | MLE_App ({expr=MLE_Name mlp}, mlargs), Some (Record_ctor _)
        | MLE_App ({expr=MLE_TApp({expr=MLE_Name mlp}, _)}, mlargs), Some Data_ctor
        | MLE_App ({expr=MLE_TApp({expr=MLE_Name mlp}, _)}, mlargs), Some (Record_ctor _) ->
          resugar_and_maybe_eta qual <| (with_ty mlAppExpr.mlty <| MLE_CTor (mlp,mlargs))

        | MLE_Name mlp, Some Data_ctor
        | MLE_Name mlp, Some (Record_ctor _)
        | MLE_TApp({expr=MLE_Name mlp}, _), Some Data_ctor
        | MLE_TApp({expr=MLE_Name mlp}, _), Some (Record_ctor _) ->
          resugar_and_maybe_eta qual <| (with_ty mlAppExpr.mlty <| MLE_CTor (mlp, []))

        | _ -> mlAppExpr

let maybe_promote_effect ml_e tag t =
    match tag, t with
    | E_GHOST, MLTY_Erased
    | E_PURE, MLTY_Erased -> ml_unit, E_PURE
    | _ -> ml_e, tag


let extract_lb_sig (g:uenv) (lbs:letbindings) =
    let maybe_generalize {lbname=lbname_; lbeff=lbeff; lbtyp=lbtyp; lbdef=lbdef}
            : lbname //just lbname returned back
            * e_tag  //the ML version of the effect label lbeff
            * (typ   //just the source type lbtyp=t, after compression
               * (S.binders //the erased type binders
                  * mltyscheme)) //translation of the source type t as a ML type scheme
            * bool   //whether or not to add a unit argument
            * term   //the term e, maybe after some type binders have been erased
            =
              let f_e = effect_as_etag g lbeff in
              let lbtyp = SS.compress lbtyp in
              let no_gen () =
                  let expected_t = term_as_mlty g lbtyp in
                  (lbname_, f_e, (lbtyp, ([], ([],expected_t))), false, lbdef)
              in
              if TcUtil.must_erase_for_extraction g.env_tcenv lbtyp
              then (lbname_, f_e, (lbtyp, ([], ([], MLTY_Erased))), false, lbdef)
              else  //              debug g (fun () -> printfn "Let %s at type %s; expected effect is %A\n" (Print.lbname_to_string lbname) (Print.typ_to_string t) f_e);
                match lbtyp.n with
                | Tm_arrow(bs, c) when (List.hd bs |> is_type_binder g) ->
                   let bs, c = SS.open_comp bs c in
                  //need to generalize, but will erase all the type abstractions;
                  //If, after erasure, what remains is not a value, then add an extra unit arg. to preserve order of evaluation/generativity
                  //and to circumvent the value restriction

                  //TODO: ERASE ONLY THOSE THAT ABSTRACT OVER PURE FUNCTIONS in Type(i),
                  //      NOT, e.g., (x:int -> St Type)
                   let tbinders, tbody =
                        match BU.prefix_until (fun x -> not (is_type_binder g x)) bs with
                            | None -> bs, U.comp_result c
                            | Some (bs, b, rest) -> bs, U.arrow (b::rest) c in

                   let n_tbinders = List.length tbinders in
                   let lbdef = normalize_abs lbdef |> U.unmeta in
                   begin match lbdef.n with
                      | Tm_abs(bs, body, copt) ->
                        let bs, body = SS.open_term bs body in
                        if n_tbinders <= List.length bs
                        then let targs, rest_args = BU.first_N n_tbinders bs in
                             let expected_source_ty =
                                let s = List.map2 (fun (x, _) (y, _) -> S.NT(x, S.bv_to_name y)) tbinders targs in
                                SS.subst s tbody in
                             let env = List.fold_left (fun env (a, _) -> UEnv.extend_ty env a None) g targs in
                             let expected_t = term_as_mlty env expected_source_ty in
                             let polytype = targs |> List.map (fun (x, _) -> bv_as_ml_tyvar x), expected_t in
                             let add_unit =
                                match rest_args with
                                | [] ->
                                  not (is_fstar_value body) //if it's a pure type app, then it will be extracted to a value in ML; so don't add a unit
                                  || not (U.is_pure_comp c)
                                | _ -> false in
                             let rest_args = if add_unit then (unit_binder::rest_args) else rest_args in
                             let polytype = if add_unit then push_unit polytype else polytype in
                             let body = U.abs rest_args body copt in
                             (lbname_, f_e, (lbtyp, (targs, polytype)), add_unit, body)

                        else (* fails to handle:
                                let f : a:Type -> b:Type -> a -> b -> Tot (nat * a * b) =
                                    fun (a:Type) ->
                                      let x = 0 in
                                      fun (b:Type) (y:a) (z:b) -> (x, y, z)

                                Could eta-expand; but with effects this is problem; see ETA-EXPANSION and NO GENERALIZATION below
                             *)
                             failwith "Not enough type binders" //TODO: better error message

                     | Tm_uinst _
                     | Tm_fvar _
                     | Tm_name _ ->
                       let env = List.fold_left (fun env (a, _) -> UEnv.extend_ty env a None) g tbinders in
                       let expected_t = term_as_mlty env tbody in
                       let polytype = tbinders |> List.map (fun (x, _) -> bv_as_ml_tyvar x), expected_t in
                       //In this case, an eta expansion is safe
                       let args = tbinders |> List.map (fun (bv, _) -> S.bv_to_name bv |> as_arg) in
                       let e = mk (Tm_app(lbdef, args)) None lbdef.pos in
                       (lbname_, f_e, (lbtyp, (tbinders, polytype)), false, e)

                     | _ ->
                        //ETA-EXPANSION?
                        //An alternative here could be to eta expand the body, but with effects, that's quite dodgy
                        // Consider:
                        //    let f : ML ((a:Type) -> a -> Tot a) = x := 17; (fun (a:Type) (x:a) -> x)
                        // Eta-expanding this would break the assignment; so, unless we hoist the assignment, we must reject this program
                        // One possibility is to restrict F* so that the effect of f must be Pure
                        // In that case, an eta-expansion would be semantically ok, but consider this:
                        //    let g : Tot ((a:Type) -> a -> Tot (a * nat)) = let z = expensive_pure_comp x in fun (a:Type) (x:a) -> (x,z))
                        // The eta expansion would cause the expensive_pure_comp to be run each time g is instantiated (this is what Coq does, FYI)
                        // It may be better to hoist expensive_pure_comp again.
                        //NO GENERALIZATION:
                        //Another alternative could be to not generalize the type t, inserting MLTY_Top for the type variables
                        err_value_restriction lbdef
                   end

                | _ ->  no_gen()
    in
    snd lbs |> List.map maybe_generalize

let extract_lb_iface (g:uenv) (lbs:letbindings)
    : uenv * list<(fv * exp_binding)> =
    let is_top = FStar.Syntax.Syntax.is_top_level (snd lbs) in
    let is_rec = not is_top && fst lbs in
    let lbs = extract_lb_sig g lbs in
    BU.fold_map (fun env
                     (lbname, e_tag, (typ, (binders, mltyscheme)), add_unit, _body) ->
                  let env, _, exp_binding =
                      UEnv.extend_lb env lbname typ mltyscheme add_unit is_rec in
                  env, (BU.right lbname, exp_binding))
                g
                lbs

//The main extraction function
let rec check_term_as_mlexpr (g:uenv) (e:term) (f:e_tag) (ty:mlty) :  (mlexpr * mlty) =
    debug g (fun () -> BU.print2 "Checking %s at type %s\n" (Print.term_to_string e) (Code.string_of_mlty g.currentModule ty));
    match f, ty with
    | E_GHOST, _
    | E_PURE, MLTY_Erased -> ml_unit, MLTY_Erased
    | _ ->
      let ml_e, tag, t = term_as_mlexpr g e in
      let ml_e, tag = maybe_promote_effect ml_e tag t in
      if eff_leq tag f
      then maybe_coerce e.pos g ml_e t ty, ty
      else match tag, f, ty with
           | E_GHOST, E_PURE, MLTY_Erased -> //effect downgrading for erased results
             maybe_coerce e.pos g ml_e t ty, ty
           | _ ->
             err_unexpected_eff g e ty f tag;
             maybe_coerce e.pos g ml_e t ty, ty

and term_as_mlexpr g e =
    let e, f, t = term_as_mlexpr' g e in
    let e, f = maybe_promote_effect e f t in
    e, f, t


and term_as_mlexpr' (g:uenv) (top:term) : (mlexpr * e_tag * mlty) =
    (debug g (fun u -> BU.print_string (BU.format3 "%s: term_as_mlexpr' (%s) :  %s \n"
        (Range.string_of_range top.pos)
        (Print.tag_of_term top)
        (Print.term_to_string top))));
    let t = SS.compress top in
    match t.n with
        | Tm_unknown
        | Tm_delayed _
        | Tm_uvar _
        | Tm_bvar _ -> failwith (BU.format1 "Impossible: Unexpected term: %s" (Print.tag_of_term t))

        | Tm_lazy i -> term_as_mlexpr g (U.unfold_lazy i)

        | Tm_type _
        | Tm_refine _
        | Tm_arrow _ ->
          ml_unit, E_PURE, ml_unit_ty

        | Tm_quoted (qt, { qkind = Quote_dynamic }) ->
          let ({exp_b_expr=fw}) = UEnv.lookup_fv g (S.lid_as_fv PC.failwith_lid delta_constant None) in
          with_ty ml_int_ty <| MLE_App(fw, [with_ty ml_string_ty <| MLE_Const (MLC_String "Cannot evaluate open quotation at runtime")]),
          E_PURE,
          ml_int_ty

        | Tm_quoted (qt, { qkind = Quote_static; antiquotes = aqs }) ->
          begin match R.inspect_ln qt with
          | RD.Tv_Var bv ->
            begin match S.lookup_aq bv aqs with
            | Some tm ->
              term_as_mlexpr g tm

            | None ->
              let tv = EMB.embed (RE.e_term_view_aq aqs) (RD.Tv_Var bv) t.pos None EMB.id_norm_cb in
              let t = U.mk_app (RD.refl_constant_term RD.fstar_refl_pack_ln) [S.as_arg tv] in
              term_as_mlexpr g t
            end
          | tv ->
              let tv = EMB.embed (RE.e_term_view_aq aqs) tv t.pos None EMB.id_norm_cb in
              let t = U.mk_app (RD.refl_constant_term RD.fstar_refl_pack_ln) [S.as_arg tv] in
              term_as_mlexpr g t
          end

        | Tm_meta(t, Meta_monadic (m, _)) ->
          let t = SS.compress t in
          begin match t.n with
            | Tm_let((false, [lb]), body) when (BU.is_left lb.lbname) ->
              let ed, qualifiers = must (TypeChecker.Env.effect_decl_opt g.env_tcenv m) in
              if not (TcEnv.is_reifiable_effect g.env_tcenv ed.mname)
              then term_as_mlexpr g t
              else
                failwith "This should not happen (should have been handled at Tm_abs level)"
            | _ -> term_as_mlexpr g t
         end

        | Tm_meta(t, _) //TODO: handle the resugaring in case it's a 'Meta_desugared' ... for more readable output
        | Tm_uinst(t, _) ->
          term_as_mlexpr g t

        | Tm_constant c ->
          let _, ty, _ = TcTerm.type_of_tot_term g.env_tcenv t in
          let ml_ty = term_as_mlty g ty in
          with_ty ml_ty (mlexpr_of_const t.pos c), E_PURE, ml_ty

        | Tm_name _ -> //lookup in g; decide if its in left or right; tag is Pure because it's just a variable
          if is_type g t //Here, we really need to be certain that g is a type; unclear if level ensures it
          then ml_unit, E_PURE, ml_unit_ty //Erase type argument
          else begin match lookup_term g t with
                | Inl _, _ ->
                  ml_unit, E_PURE, ml_unit_ty

                | Inr ({exp_b_expr=x; exp_b_tscheme=mltys}), qual ->
                  //let _ = printfn "\n (*looked up tyscheme of \n %A \n as \n %A *) \n" x s in
                  begin match mltys with
                    | ([], t) when (t=ml_unit_ty) -> ml_unit, E_PURE, t //optimize (x:unit) to ()
                    | ([], t) -> maybe_eta_data_and_project_record g qual t x, E_PURE, t
                    | _ -> err_uninst g t mltys t
                  end
               end

        | Tm_fvar fv -> //Nearly identical to Tm_name, except the fv may have been erased altogether; if so return Erased
          if is_type g t //Here, we really need to be certain that g is a type; unclear if level ensures it
          then ml_unit, E_PURE, ml_unit_ty //Erase type argument
          else
          begin
               match try_lookup_fv g fv with
               | None -> //it's been erased
                 ml_unit, E_PURE, MLTY_Erased

               | Some {exp_b_expr=x; exp_b_tscheme=mltys} ->
                 let _ = debug g (fun () ->
                          BU.print3 "looked up %s: got %s at %s \n"
                              (Print.fv_to_string fv)
                              (Code.string_of_mlexpr g.currentModule x)
                              (Code.string_of_mlty g.currentModule (snd mltys))) in
                 begin match mltys with
                    | ([], t) when (t=ml_unit_ty) -> ml_unit, E_PURE, t //optimize (x:unit) to ()
                    | ([], t) -> maybe_eta_data_and_project_record g fv.fv_qual t x, E_PURE, t
                    | _ -> err_uninst g t mltys t
                 end
          end

        | Tm_abs(bs, body, rcopt (* the annotated computation type of the body *)) ->
          let bs, body = SS.open_term bs body in
          let ml_bs, env = binders_as_ml_binders g bs in
          let body =
            match rcopt with
            | Some rc ->
                if TcEnv.is_reifiable_rc env.env_tcenv rc
                then TcUtil.reify_body env.env_tcenv body
                else body
            | None -> debug g (fun () -> BU.print1 "No computation type for: %s\n" (Print.term_to_string body)); body in
          let ml_body, f, t = term_as_mlexpr env body in
          let f, tfun = List.fold_right
            (fun (_, targ) (f, t) -> E_PURE, MLTY_Fun (targ, f, t))
            ml_bs (f, t) in
          with_ty tfun <| MLE_Fun(ml_bs, ml_body), f, tfun

        | Tm_app({n=Tm_constant Const_range_of}, [(a1, _)]) ->
          let ty = term_as_mlty g (tabbrev PC.range_lid) in
          with_ty ty <| mlexpr_of_range a1.pos, E_PURE, ty

        | Tm_app({n=Tm_constant Const_set_range_of}, [(t, _); (r, _)]) ->
          term_as_mlexpr g t

        | Tm_app({n=Tm_constant (Const_reflect _)}, _) -> failwith "Unreachable? Tm_app Const_reflect"

        | Tm_app(head, args) ->
          let is_total rc =
              Ident.lid_equals rc.residual_effect PC.effect_Tot_lid
              || rc.residual_flags |> List.existsb (function TOTAL -> true | _ -> false)
          in
          begin match head.n, (SS.compress head).n with
            | Tm_uvar _, _ -> //This should be a resolved uvar --- so reduce it before extraction
              let t = N.normalize [Env.Beta; Env.Iota; Env.Zeta; Env.EraseUniverses; Env.AllowUnboundUniverses] g.env_tcenv t in
              term_as_mlexpr g t

            | _, Tm_abs(bs, _, Some rc) when is_total rc -> //this is a beta_redex --- also reduce it before extraction
              let t = N.normalize [Env.Beta; Env.Iota; Env.Zeta; Env.EraseUniverses; Env.AllowUnboundUniverses] g.env_tcenv t in
              term_as_mlexpr g t

            | _, Tm_constant Const_reify ->
              let e = TcUtil.reify_body_with_arg g.env_tcenv head (List.hd args) in
              let tm = S.mk_Tm_app (TcUtil.remove_reify e) (List.tl args) None t.pos in
              term_as_mlexpr g tm

            | _ ->

              let rec extract_app is_data (mlhead, mlargs_f) (f(*:e_tag*), t (* the type of (mlhead mlargs) *)) restArgs =
                let mk_head () =
                    let mlargs = List.rev mlargs_f |> List.map fst in
                    with_ty t <| MLE_App(mlhead, mlargs)
                in
                debug g (fun () -> BU.print3 "extract_app ml_head=%s type of head = %s, next arg = %s\n"
                                (Code.string_of_mlexpr g.currentModule (mk_head()))
                                (Code.string_of_mlty g.currentModule t)
                                (match restArgs with [] -> "none" | (hd, _)::_ -> Print.term_to_string hd));
                                        //            Printf.printf "synth_app restArgs=%d, t=%A\n" (List.length restArgs) t;
                match restArgs, t with
                    | [], _ ->
                        //1. If partially applied and head is a datacon, it needs to be eta-expanded
                        //Note, the evaluation order for impure arguments has already been
                        //enforced in the main type-checker, that already let-binds any
                        //impure arguments
                        let app = maybe_eta_data_and_project_record g is_data t (mk_head()) in
                        app, f, t

                    | (arg, _)::rest, MLTY_Fun (formal_t, f', t)
                            when (is_type g arg
                                  && type_leq g formal_t ml_unit_ty) ->
                      //non-prefix type app; this type argument gets erased to unit
                      extract_app is_data (mlhead, (ml_unit, E_PURE)::mlargs_f) (join arg.pos f f', t) rest

                    | (e0, _)::rest, MLTY_Fun(tExpected, f', t) ->
                      //This is the main case of an actualy argument e0 provided to a function
                      //that expects an argument of type tExpected
                      let r = e0.pos in
                      let expected_effect =
                            if Options.lax()
                            && FStar.TypeChecker.Util.short_circuit_head head
                            then E_IMPURE
                            else E_PURE in
                      let e0, tInferred =
                          check_term_as_mlexpr g e0 expected_effect tExpected in
                      extract_app is_data (mlhead, (e0, expected_effect)::mlargs_f) (join_l r [f;f'], t) rest

                    | _ ->
                      begin match Util.udelta_unfold g t with
                        | Some t -> extract_app is_data (mlhead, mlargs_f) (f, t) restArgs
                        | None ->
                          match t with
                          | MLTY_Erased -> //the head of the application has been erased; so the whole application should be too
                            ml_unit, E_PURE, t

                          | MLTY_Top -> //cf. issue #734
                            //Coerce to a function of the arity of restArgs
                            let t = List.fold_right (fun t out -> MLTY_Fun(MLTY_Top, E_PURE, out)) restArgs MLTY_Top in
                            let mlhead =
                              let mlargs = List.rev mlargs_f |> List.map fst in
                              let head = with_ty MLTY_Top <| MLE_App(mlhead, mlargs) in
                              maybe_coerce top.pos g head MLTY_Top t
                            in
                            extract_app is_data (mlhead, []) (f, t) restArgs

                          | _ ->
                            let mlhead =
                              let mlargs = List.rev mlargs_f |> List.map fst in
                              let head = with_ty MLTY_Top <| MLE_App(mlhead, mlargs) in
                              maybe_coerce top.pos g head MLTY_Top t
                            in
                            err_ill_typed_application g top mlhead restArgs t
                      end
              in

              let extract_app_maybe_projector is_data mlhead (f, t) args =
                    match is_data with
                    | Some (Record_projector _) ->
                      let rec remove_implicits args f t = match args, t with
                        | (a0, Some (Implicit _))::args, MLTY_Fun(_, f', t) ->
                          remove_implicits args (join a0.pos f f') t

                        | _ -> args, f, t in
                      let args, f, t = remove_implicits args f t in
                      extract_app is_data (mlhead, []) (f, t) args

                    | _ -> extract_app is_data (mlhead, []) (f, t) args in

              let extract_app_with_instantiations () =
                   let head = U.un_uinst head in
                   begin match head.n with
                    | Tm_name _
                    | Tm_fvar _ ->
                       //             debug g (fun () -> printfn "head of app is %s\n" (Print.exp_to_string head));
                      let (head_ml, (vars, t), inst_ok), qual =
                        match lookup_term g head with
                        | Inr exp_b, q ->
                          debug g (fun () ->
                              BU.print4 "@@@looked up %s: got %s at %s (inst_ok=%s)\n"
                                  (Print.term_to_string head)
                                  (Code.string_of_mlexpr g.currentModule exp_b.exp_b_expr)
                                  (Code.string_of_mlty g.currentModule (snd exp_b.exp_b_tscheme))
                                  (BU.string_of_bool exp_b.exp_b_inst_ok));
                          (exp_b.exp_b_expr, exp_b.exp_b_tscheme, exp_b.exp_b_inst_ok), q
                        | _ -> failwith "FIXME Ty" in

                      let has_typ_apps = match args with
                        | (a, _)::_ -> is_type g a
                        | _ -> false in
                      //              debug g (fun () -> printfn "\n (*looked up tyscheme \n %A *) \n" (vars,t));
                      let head_ml, head_t, args = match vars with
                        | _::_ when ((not has_typ_apps) && inst_ok) ->
                          (* no explicit type applications although some were expected; but instantiation is permissible *)
                          //              debug g (fun () -> printfn "Taking the type of %A to be %A\n" head_ml t);
                          head_ml, t, args

                        | _ ->
                          let n = List.length vars in
                          if n <= List.length args
                          then let prefix, rest = BU.first_N n args in
        //                       let _ = (if n=1 then printfn "\n (*prefix was  \n %A \n  *) \n" prefix) in
                               let prefixAsMLTypes = List.map (fun (x, _) -> term_as_mlty g x) prefix in
        //                        let _ = printfn "\n (*about to instantiate  \n %A \n with \n %A \n \n *) \n" (vars,t) prefixAsMLTypes in
                               let t = instantiate (vars, t) prefixAsMLTypes in
                               debug g (fun () ->
                                  BU.print4 "@@@looked up %s, instantiated with [%s] translated to [%s], got %s\n"
                                      (Print.term_to_string head)
                                      (Print.args_to_string prefix)
                                      (List.map (Code.string_of_mlty g.currentModule) prefixAsMLTypes |> String.concat ", ")
                                      (Code.string_of_mlty g.currentModule t));
                               // If I understand this code correctly when we reach this branch we are observing an
                               // application of the form:
                               //
                               // (f u_1 .. u_n) e_1 .. e_2
                               //
                               // where f : forall (t_1 ... t_n : Type), t1 -> ... t_n
                               //
                               // The old code was converting `f u_1 ... u_n`, to a term with a type `u_1 -> ... -> u_n`.
                               //
                               // We now preserve these type applications, by wrapping the head in type applications,
                               // instantiating the type assigning it to this new type application expression,
                               // and continuing with the rest of the pipeline.
                               //
                               // @jroesch
                               //
                               // This helper ensures we don't generate empty type applications, which will cause
                               // problems in FStar.Extraction.Kremlin when trying match aganist head symbols which
                               // are now wrapped with empty type applications.
                               let mk_tapp e ty_args =
                                    match ty_args with
                                    | [] -> e
                                    | _ -> { e with expr=MLE_TApp(e, ty_args)} in
                               let head = match head_ml.expr with
                                 | MLE_Name _
                                 | MLE_Var _ -> { mk_tapp head_ml prefixAsMLTypes with mlty=t }
                                 | MLE_App(head, [{expr=MLE_Const MLC_Unit}]) ->
                                    MLE_App({ mk_tapp head prefixAsMLTypes with mlty=MLTY_Fun(ml_unit_ty, E_PURE, t)}, [ml_unit]) |> with_ty t
                                 | _ -> failwith "Impossible: Unexpected head term" in
                               head, t, rest
                          else err_uninst g head (vars, t) top in
                        //debug g (fun () -> printfn "\n (*instantiating  \n %A \n with \n %A \n produced \n %A \n *) \n" (vars,t0) prefixAsMLTypes t);
                       begin match args with
                            | [] -> maybe_eta_data_and_project_record g qual head_t head_ml, E_PURE, head_t
                            | _  -> extract_app_maybe_projector qual head_ml (E_PURE, head_t) args
                       end

                    | _ ->
                      let head, f, t = term_as_mlexpr g head in // t is the type inferred for head, the head of the app
                      extract_app_maybe_projector None head (f, t) args
                 end
              in

              if is_type g t
              then ml_unit, E_PURE, ml_unit_ty //Erase type argument: TODO: FIXME, this could be effectful
              else match (U.un_uinst head).n with
                   | Tm_fvar fv ->
                     (match try_lookup_fv g fv with
                      | None -> //erased head
                        ml_unit, E_PURE, MLTY_Erased
                      | _ ->
                        extract_app_with_instantiations ())

                   | _ ->
                     extract_app_with_instantiations ()
            end

        | Tm_ascribed(e0, (tc, _), f) ->
          let t = match tc with
            | Inl t -> term_as_mlty g t
            | Inr c -> term_as_mlty g (U.comp_result c) in
          let f = match f with
            | None -> failwith "Ascription node with an empty effect label"
            | Some l -> effect_as_etag g l in
          let e, t = check_term_as_mlexpr g e0 f t in
          e, f, t

        | Tm_let((is_rec, lbs), e') ->
          let top_level = is_top_level lbs in
          let lbs, e' =
            if is_rec
            then SS.open_let_rec lbs e'
            else if is_top_level lbs
                 then lbs, e'
                 else let lb = List.hd lbs in
                      let x = S.freshen_bv (left lb.lbname) in
                      let lb = {lb with lbname=Inl x} in
                      let e' = SS.subst [DB(0, x)] e' in
                      [lb], e' in
          let lbs =
            if top_level
            then lbs |> List.map (fun lb ->
                    let tcenv = TcEnv.set_current_module g.env_tcenv
                                (Ident.lid_of_path ((fst g.currentModule) @ [snd g.currentModule]) Range.dummyRange) in
                    // debug g (fun () ->
                    //            BU.print1 "!!!!!!!About to normalize: %s\n" (Print.term_to_string lb.lbdef);
                    //            Options.set_option "debug_level" (Options.List [Options.String "Norm"; Options.String "Extraction"]));
                    let lbdef =
                        if Options.ml_ish()
                        then lb.lbdef
                        else let norm_call () =
                                 N.normalize ([Env.AllowUnboundUniverses; Env.EraseUniverses;
                                               Env.Inlining; Env.Eager_unfolding;
                                               Env.Exclude Env.Zeta; Env.PureSubtermsWithinComputations;
                                               Env.Primops; Env.Unascribe; Env.ForExtraction])
                                              tcenv lb.lbdef
                             in
                             if TcEnv.debug tcenv <| Options.Other "Extraction"
                             || TcEnv.debug tcenv <| Options.Other "ExtractNorm"
                             then let _ = BU.print2 "Starting to normalize top-level let %s)\n\tlbdef=%s"
                                            (Print.lbname_to_string lb.lbname)
                                            (Print.term_to_string lb.lbdef) in
                                  // Options.set_option "debug_level"
                                  //   (Options.List [Options.String "Norm"; Options.String "Extraction"]);
                                  let a = FStar.Util.measure_execution_time
                                          (BU.format1 "###(Time to normalize top-level let %s)"
                                            (Print.lbname_to_string lb.lbname))
                                          norm_call in
                                  BU.print1 "Normalized to %s\n" (Print.term_to_string a);
                                  a
                             else norm_call ()
                    in
                    {lb with lbdef=lbdef})
            else lbs in

          let check_lb env (nm, (_lbname, f, (_t, (targs, polytype)), add_unit, e)) =
              let env = List.fold_left (fun env (a, _) -> UEnv.extend_ty env a None) env targs in
              let expected_t = snd polytype in
              let e, ty = check_term_as_mlexpr env e f expected_t in
              let e, f = maybe_promote_effect e f expected_t in
              let meta =
                  match f, ty with
                  | E_PURE, MLTY_Erased
                  | E_GHOST, MLTY_Erased -> [Erased]
                  | _ -> []
              in
              f, {mllb_meta = meta; mllb_name=nm; mllb_tysc=Some polytype; mllb_add_unit=add_unit; mllb_def=e; print_typ=true}
          in

          let lbs = extract_lb_sig g (is_rec, lbs) in

          let env_body, lbs = List.fold_right (fun lb (env, lbs) ->
              let (lbname, _, (t, (_, polytype)), add_unit, _) = lb in
              let env, nm, _ = UEnv.extend_lb env lbname t polytype add_unit true in
              env, (nm,lb)::lbs) lbs (g, []) in

          let env_def = if is_rec then env_body else g in

          let lbs = lbs |> List.map (check_lb env_def)  in

          let e'_rng = e'.pos in

          let e', f', t' = term_as_mlexpr env_body e' in

          let f = join_l e'_rng (f'::List.map fst lbs) in

          let is_rec = if is_rec = true then Rec else NonRec in

          with_ty_loc t' (mk_MLE_Let top_level (is_rec, List.map snd lbs) e') (Util.mlloc_of_range t.pos), f, t'

      | Tm_match(scrutinee, pats) ->
        let e, f_e, t_e = term_as_mlexpr g scrutinee in
        let b, then_e, else_e = check_pats_for_ite pats in
        let no_lift : mlexpr -> mlty -> mlexpr = fun x t -> x in
        if b then
            match then_e, else_e with
                | Some then_e, Some else_e ->
                    let then_mle, f_then, t_then = term_as_mlexpr g then_e in
                    let else_mle, f_else, t_else = term_as_mlexpr g else_e in
                    let t_branch, maybe_lift =
                        if type_leq g t_then t_else  //the types agree except for effect labels
                        then t_else, no_lift
                        else if type_leq g t_else t_then
                        then t_then, no_lift
                        else MLTY_Top, apply_obj_repr in
                    with_ty t_branch <| MLE_If (e, maybe_lift then_mle t_then, Some (maybe_lift else_mle t_else)),
                    join then_e.pos f_then f_else,
                    t_branch
                | _ -> failwith "ITE pats matched but then and else expressions not found?"
        else
            let pat_t_compat, mlbranches = pats |> BU.fold_map (fun compat br ->
                let pat, when_opt, branch = SS.open_branch br in
                let env, p, pat_t_compat = extract_pat g pat t_e term_as_mlexpr in
                let when_opt, f_when = match when_opt with
                    | None -> None, E_PURE
                    | Some w ->
                        let w_pos = w.pos in
                        let w, f_w, t_w = term_as_mlexpr env w in
                        let w = maybe_coerce w_pos env w t_w ml_bool_ty in
                        Some w, f_w in
                let mlbranch, f_branch, t_branch = term_as_mlexpr env branch in
                //Printf.printf "Extracted %s to %A\n" (Print.exp_to_string branch) mlbranch;
                compat&&pat_t_compat,
                p |> List.map (fun (p, wopt) ->
                    let when_clause = conjoin_opt wopt when_opt in
                    p, (when_clause, f_when), (mlbranch, f_branch, t_branch)))
                true in
             let mlbranches : list<(mlpattern * (option<mlexpr> * e_tag) * (mlexpr * e_tag * mlty))>
               = List.flatten mlbranches in
             //if the type of the pattern isn't compatible with the type of the scrutinee
             //    insert a magic around the scrutinee
             let e = if pat_t_compat
                     then e
                     else (debug g (fun _ -> BU.print2 "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                                (Code.string_of_mlexpr g.currentModule e)
                                                (Code.string_of_mlty g.currentModule t_e));
                           with_ty t_e <| MLE_Coerce (e, t_e, MLTY_Top)) in
             begin match mlbranches with
                | [] ->
                    let ({exp_b_expr=fw}) = UEnv.lookup_fv g (S.lid_as_fv PC.failwith_lid delta_constant None) in
                    with_ty ml_int_ty <| MLE_App(fw, [with_ty ml_string_ty <| MLE_Const (MLC_String "unreachable")]),
                    E_PURE,
                    ml_int_ty


                | (_, _, (_, f_first, t_first))::rest ->
                   let topt, f_match = List.fold_left (fun (topt, f) (_, _, (_, f_branch, t_branch)) ->
                        //WARNING WARNING WARNING
                        //We're explicitly excluding the effect of the when clause in the net effect computation
                        //TODO: fix this when we handle when clauses fully!
                        let f = join top.pos f f_branch in
                        let topt = match topt with
                            | None -> None
                            | Some t ->
                              //we just use the environment g here, since it is only needed for delta unfolding
                              //which is invariant across the branches
                              if type_leq g t t_branch
                              then Some t_branch
                              else if type_leq g t_branch t
                              then Some t
                              else None in
                        topt, f)
                     (Some t_first, f_first)
                     rest in
                   let mlbranches = mlbranches |> List.map (fun (p, (wopt, _), (b, _, t)) ->
                        let b = match topt with
                            | None ->
//                              Printf.printf "Apply obj repr to %A and %A\n" b t;
                              apply_obj_repr b t
                            | Some _ -> b in
                        (p, wopt, b)) in
                   let t_match = match topt with
                        | None -> MLTY_Top
                        | Some t -> t in
                   with_ty t_match <| MLE_Match(e, mlbranches), f_match, t_match
            end

let ind_discriminator_body env (discName:lident) (constrName:lident) : mlmodule1 =
    // First, lookup the original (F*) type to figure out how many implicit arguments there are.
    let _, fstar_disc_type = fst <| TypeChecker.Env.lookup_lid env.env_tcenv discName in
    let wildcards = match (SS.compress fstar_disc_type).n with
        | Tm_arrow (binders, _) ->
            binders
            |> List.filter (function (_, (Some (Implicit _))) -> true | _ -> false)
            |> List.map (fun _ -> fresh "_", MLTY_Top)
        | _ ->
            failwith "Discriminator must be a function"
    in
    // Unfortunately, looking up the constructor name in the environment would give us a _curried_ type.
    // So, we don't bother popping arrows until we find the return type of the constructor.
    // We just use Top.
    let mlid = fresh "_discr_" in
    let targ = MLTY_Top in
    // Ugly hack: we don't know what to put in there, so we just write a dummy
    // polymorphic value to make sure that the type is not printed.
    let disc_ty = MLTY_Top in
    let discrBody =
        with_ty disc_ty <|
            MLE_Fun(wildcards @ [(mlid, targ)],
                    with_ty ml_bool_ty <|
                        (MLE_Match(with_ty targ <| MLE_Name([], mlid),
                                    // Note: it is legal in OCaml to write [Foo _] for a constructor with zero arguments, so don't bother.
                                   [MLP_CTor(mlpath_of_lident constrName, [MLP_Wild]), None, with_ty ml_bool_ty <| MLE_Const(MLC_Bool true);
                                    MLP_Wild, None, with_ty ml_bool_ty <| MLE_Const(MLC_Bool false)]))) in
    MLM_Let (NonRec,[{mllb_meta=[]; mllb_name=convIdent discName.ident; mllb_tysc=None; mllb_add_unit=false; mllb_def=discrBody; print_typ=false}] )
