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
module FStarC.Extraction.ML.Term
open FStarC.Effect
open FStarC.List
open FStarC
open FStarC.TypeChecker.Env
open FStarC.Const
open FStarC.Ident
open FStarC.Extraction
open FStarC.Extraction.ML
open FStarC.Extraction.ML.Syntax
open FStarC.Extraction.ML.UEnv
open FStarC.Extraction.ML.Util
open FStarC.Syntax.Syntax
open FStarC.Errors

module BU     = FStarC.Util
module Code   = FStarC.Extraction.ML.Code
module EMB    = FStarC.Syntax.Embeddings
module Env    = FStarC.TypeChecker.Env
module N      = FStarC.TypeChecker.Normalize
module PC     = FStarC.Parser.Const
module RC     = FStarC.Reflection.V2.Constants
module RD     = FStarC.Reflection.V2.Data
module RE     = FStarC.Reflection.V2.Embeddings
module R      = FStarC.Reflection.V2.Builtins
module S      = FStarC.Syntax.Syntax
module SS     = FStarC.Syntax.Subst
module TcEnv  = FStarC.TypeChecker.Env
module TcTerm = FStarC.TypeChecker.TcTerm
module TcUtil = FStarC.TypeChecker.Util
module U      = FStarC.Syntax.Util

let dbg_Extraction     = Debug.get_toggle "Extraction"
let dbg_ExtractionNorm = Debug.get_toggle "ExtractionNorm"

exception Un_extractable

open FStarC.Class.Show
open FStarC.Class.Tagged
open FStarC.Class.PP


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

module Print = FStarC.Syntax.Print

(********************************************************************************************)
(* Some basic error reporting; all are fatal errors at this stage                           *)
(********************************************************************************************)
let err_ill_typed_application env (t : term) mlhead (args : args) (ty : mlty) =
    Errors.raise_error t Fatal_IllTyped
       (Format.fmt4 "Ill-typed application: source application is %s \n translated prefix to %s at type %s\n remaining args are %s\n"
                (show t)
                (Code.string_of_mlexpr (current_module_of_uenv env) mlhead)
                (Code.string_of_mlty (current_module_of_uenv env) ty)
                (show args))

let err_ill_typed_erasure env (pos:Range.t) (ty : mlty) =
    Errors.raise_error pos Fatal_IllTyped
       (Format.fmt1 "Erased value found where a value of type %s was expected"
                  (Code.string_of_mlty (current_module_of_uenv env) ty))

let err_value_restriction (t:term) =
    Errors.raise_error t Fatal_ValueRestriction
       (Format.fmt2 "Refusing to generalize because of the value restriction: (%s) %s"
                    (tag_of t) (show t))

let err_unexpected_eff env (t:term) ty f0 f1 =
    let open FStarC.Errors.Msg in
    let open FStarC.Pprint in
    Errors.log_issue t Warning_ExtractionUnexpectedEffect [
        prefix 4 1 (text "For expression") (pp t) ^/^
        prefix 4 1 (text "of type") (arbitrary_string (Code.string_of_mlty (current_module_of_uenv env) ty));
        prefix 4 1 (text "Expected effect") (arbitrary_string (eff_to_string f0)) ^/^
        prefix 4 1 (text "got effect") (arbitrary_string (eff_to_string f1))]

let err_cannot_extract_effect (l:lident) (r:Range.t) (reason:string) (ctxt:string) =
  Errors.raise_error r Errors.Fatal_UnexpectedEffect [
    Errors.text <|
     Format.fmt3 "Cannot extract effect %s because %s (when extracting %s)"
       (string_of_lid l) reason ctxt
  ]

let get_extraction_mode env (m:Ident.lident) =
  let norm_m = Env.norm_eff_name env m in
  (Env.get_effect_decl env norm_m).extraction_mode

(***********************************************************************)
(* Translating an effect lid to an e_tag = {E_PURE, E_ERASABLE, E_IMPURE} *)
(***********************************************************************)
let effect_as_etag =
    let cache = SMap.create 20 in
    let rec delta_norm_eff g (l:lident) =
        match SMap.try_find cache (string_of_lid l) with
            | Some l -> l
            | None ->
                let res = match TypeChecker.Env.lookup_effect_abbrev (tcenv_of_uenv g) [S.U_zero] l with
                | None -> l
                | Some (_, c) -> delta_norm_eff g (U.comp_effect_name c) in
                SMap.add cache (string_of_lid l) res;
                res in
    fun g l ->
    let l = delta_norm_eff g l in
    if lid_equals l PC.effect_PURE_lid
    then E_PURE
    else if TcEnv.is_erasable_effect (tcenv_of_uenv g) l
    then E_ERASABLE
    else
         let ed_opt = TcEnv.effect_decl_opt (tcenv_of_uenv g) l in
         match ed_opt with
         | Some (ed, qualifiers) ->
           if TcEnv.is_reifiable_effect (tcenv_of_uenv g) ed.mname
           then
             (* Some reifiable effects are extracted natively. In that case,
                the tag must be IMPURE. *)
             if get_extraction_mode (tcenv_of_uenv g) ed.mname = S.Extract_reify
             then E_PURE
             else E_IMPURE
           else E_IMPURE
         | None ->
           E_IMPURE

(********************************************************************************************)
(* Basic syntactic operations on a term                                                     *)
(********************************************************************************************)

(* is_arity t:
         t is a sort s, i.e., Type i
     or, t = x1:t1 -> ... -> xn:tn -> C
             where PC.result_type is an arity

 *)
let rec is_arity_aux tcenv t =
    let t = U.unmeta t in
    match (SS.compress t).n with
    | Tm_unknown
    | Tm_delayed _
    | Tm_ascribed _
    | Tm_meta _ -> failwith (Format.fmt1 "Impossible: is_arity (%s)" (tag_of t))
    | Tm_lazy i -> is_arity_aux tcenv (U.unfold_lazy i)
    | Tm_uvar _
    | Tm_constant _
    | Tm_name _
    | Tm_quoted _
    | Tm_bvar _ -> false
    | Tm_type _ -> true
    | Tm_arrow  {comp=c} ->
      is_arity_aux tcenv (FStarC.Syntax.Util.comp_result c)
    | Tm_fvar fv ->
      let topt =
        FStarC.TypeChecker.Env.lookup_definition
          [Env.Unfold delta_constant]
          tcenv
          fv.fv_name
      in
      begin
      match topt with
      | None -> false
      | Some (_, t) -> is_arity_aux tcenv t
      end
    | Tm_app _ ->
      let head, _ = U.head_and_args t in
      is_arity_aux tcenv head
    | Tm_uinst(head, _) ->
      is_arity_aux tcenv head
    | Tm_refine {b=x} ->
      is_arity_aux tcenv x.sort
    | Tm_abs {body}
    | Tm_let {body} ->
      is_arity_aux tcenv body
    | Tm_match {brs=branches} ->
      begin match branches with
        | (_, _, e)::_ -> is_arity_aux tcenv e
        | _ -> false
      end

let is_arity env t = is_arity_aux (tcenv_of_uenv env) t

let push_tcenv_binders (u:uenv) (bs:binders) =
  let tcenv = tcenv_of_uenv u in
  let tcenv = TcEnv.push_binders tcenv bs in
  set_tcenv u tcenv

//is_type_aux env t:
//     Determines whether or not t is a type
//     syntactic structure and type annotations
let rec is_type_aux env t =
    let t = SS.compress t in
    match t.n with
    | Tm_delayed _
    | Tm_unknown ->
        failwith (Format.fmt1 "Impossible: %s" (tag_of t))

    | Tm_lazy i -> is_type_aux env (U.unfold_lazy i)

    | Tm_constant _ ->
      false

    | Tm_type _
    | Tm_refine _
    | Tm_arrow _ ->
      true

    | Tm_fvar fv when S.fv_eq_lid fv (PC.failwith_lid()) ->
      false //special case this, since we emit it during extraction even in prims, before it is in the F* scope

    | Tm_fvar fv ->
      UEnv.is_type_name env fv

    | Tm_uvar (u, s) ->
      let t= U.ctx_uvar_typ u in
      is_arity env (SS.subst' s t)

    | Tm_bvar ({sort=t}) ->
      is_arity env t

    | Tm_name x -> (
      let g = UEnv.tcenv_of_uenv env in
      match try_lookup_bv g x with
      | Some (t, _) ->
        is_arity env t
      | _ -> (
        failwith (Format.fmt1 "Extraction: variable not found: %s" (show x))
      )
    )

    | Tm_ascribed {tm=t} ->
      is_type_aux env t

    | Tm_uinst(t, _) ->
      is_type_aux env t

    | Tm_abs {bs; body} ->
      let bs, body = SS.open_term bs body in
      let env = push_tcenv_binders env bs in
      is_type_aux env body

    | Tm_let {lbs=(false, [lb]); body} ->
      let x = Inl?.v lb.lbname in
      let bs, body = SS.open_term [S.mk_binder x] body in
      let env = push_tcenv_binders env bs in
      is_type_aux env body

    | Tm_let {lbs=(_, lbs); body} ->
      let lbs, body = SS.open_let_rec lbs body in
      let env = push_tcenv_binders env (List.map (fun lb -> S.mk_binder (Inl?.v lb.lbname)) lbs) in
      is_type_aux env body

    | Tm_match {brs=branches} ->
      begin match branches with
        | b::_ -> (
          let pat, _, e = SS.open_branch b in
          match FStarC.TypeChecker.PatternUtils.raw_pat_as_exp (tcenv_of_uenv env) pat with
          | None -> false
          | Some (_, bvs) ->
            let binders = List.map (fun bv -> S.mk_binder bv) bvs in
            let env = push_tcenv_binders env binders in
            is_type_aux env e
        )
        | _ -> false
      end

    | Tm_quoted _ -> false

    | Tm_meta {tm=t} ->
      is_type_aux env t

    | Tm_app {hd=head} ->
      is_type_aux env head

let is_type env t =
    debug env (fun () -> Format.print2 "checking is_type (%s) %s\n"
                                (tag_of t)
                                (show t)
                                );
    let b = is_type_aux env t in
    debug env (fun _ ->
        Format.print3 "is_type(%s) (tag %s) = %s\n" (show t) (tag_of (SS.compress t)) (show b));
    b

let is_type_binder env x = is_arity env x.binder_bv.sort

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
    | Tm_app {hd=head; args} ->
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
    | Tm_meta {tm=t}
    | Tm_ascribed {tm=t} -> is_fstar_value t
    | _ -> false

let rec is_ml_value e =
    match e.expr with
    | MLE_Const _
    | MLE_Var   _
    | MLE_Name  _
    | MLE_Fun   _ -> true
    | MLE_CTor (_, exps)
    | MLE_Tuple exps -> BU.for_all is_ml_value exps
    | MLE_Record (_, _, fields) -> BU.for_all (fun (_, e) -> is_ml_value e) fields
    | MLE_TApp (h, _) -> is_ml_value h
    | _ -> false

(*copied from ocaml-asttrans.fs*)

//pre-condition: SS.compress t = Tm_abs _
//Collapses adjacent abstractions into a single n-ary abstraction
let normalize_abs (t0:term) : term =
    let rec aux bs t copt =
        let t = SS.compress t in
        match t.n with
            | Tm_abs {bs=bs'; body; rc_opt=copt} -> aux (bs@bs') body copt
            | _ ->
              let e' = U.unascribe t in
              if U.is_fun e'
              then aux bs e' copt
              else U.abs bs e' copt in
   aux [] t0 None

let unit_binder () = S.mk_binder <| S.new_bv None t_unit

//check_pats_for_ite l:
//    A helper to enable translating boolean matches back to if/then/else
let check_pats_for_ite (l:list (pat & option term & term)) : (bool   //if l is pair of boolean branches
                                                             & option term  //the 'then' case
                                                             & option term) = //the 'else' case
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

//instantiate_tyscheme s args:
//      only handles fully applied types,
//      pre-condition: List.length (fst s) = List.length args
let instantiate_tyscheme (s:mltyscheme) (args:list mlty) : mlty = Util.subst s args

let fresh_mlidents (ts:list mlty) (g:uenv) : list (mlident & mlty) & uenv =
   let g, vs_ts =
     List.fold_right
        (fun t (uenv, vs) ->
          let uenv, v = UEnv.new_mlident uenv in
          uenv, (v, t)::vs)
     ts (g, [])
   in
   vs_ts, g

let fresh_binders (ts:list mlty) (g:uenv) : list mlbinder & uenv =
  let vs_ts, g = fresh_mlidents ts g in
  List.map (fun (v, t) -> {mlbinder_name=v; mlbinder_ty=t; mlbinder_attrs=[]}) vs_ts,
  g

//instantiate_maybe_partial:
//  When `e` has polymorphic type `s`
//  and isn't instantiated in F* (e.g., because of first-class polymorphism)
//  we extract e to a type application in ML by instantiating all its
//  type arguments to MLTY_Erased (later, perhaps, being forced to insert magics)
let instantiate_maybe_partial (g:uenv) (e:mlexpr) (eff:e_tag) (s:mltyscheme) (tyargs:list mlty) : (mlexpr & e_tag & mlty) =
    let vars, t = s in
    let n_vars = List.length vars in
    let n_args = List.length tyargs in
    if n_args = n_vars
    then //easy, just make a type application node
      if n_args = 0
      then (e, eff, t)
      else
        let ts = instantiate_tyscheme (vars, t) tyargs in
        let tapp = {
          e with
            expr=MLE_TApp(e, tyargs);
            mlty=ts
        } in
        (tapp, eff, ts)
    else if n_args < n_vars
    then //We have a partial type-application in F*
         //So, make a full type application node in ML,
         //by generating dummy instantiations.
         //And then expand it out by adding as many unit
         //arguments as dummy instantiations, since these
         //will be applied later to F* types that get erased to ()
      let extra_tyargs =
        let _, rest_vars = BU.first_N n_args vars in
        rest_vars |> List.map (fun _ -> MLTY_Erased)
      in
      let tyargs = tyargs@extra_tyargs in
      let ts = instantiate_tyscheme (vars, t) tyargs in
      let tapp = {
        e with
          expr=MLE_TApp(e, tyargs);
          mlty=ts
      } in
      let t =
        List.fold_left
          (fun out t -> MLTY_Fun(t, E_PURE, out))
          ts
          extra_tyargs
      in
      let vs_ts, g = fresh_binders extra_tyargs g in
      let f = with_ty t <| MLE_Fun (vs_ts, tapp) in
      (f, eff, t)
    else failwith "Impossible: instantiate_maybe_partial called with too many arguments"

(* eta-expand `e` according to its type `t` *)
let eta_expand (g:uenv) (t : mlty) (e : mlexpr) : mlexpr =
    let ts, r = doms_and_cod t in
    if ts = []
    then e
    else // just quit if this is not a function type
      let vs_ts, g = fresh_binders ts g in
      let vs_es = List.map (fun {mlbinder_name=v; mlbinder_ty=t} -> with_ty t (MLE_Var v)) vs_ts in
      let body = with_ty r <| MLE_App (e, vs_es) in
      with_ty t <| MLE_Fun (vs_ts, body)

let default_value_for_ty (g:uenv) (t : mlty) : mlexpr  =
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
    else let vs_ts, g = fresh_binders ts g in
         with_ty t <| MLE_Fun (vs_ts, body r)

let maybe_eta_expand_coercion g expect e =
    if Options.codegen () = Some Options.Krml // we need to stay first order for Karamel
    then e
    else eta_expand g expect e

(*
  A small optimization to push coercions into the structure of a term

  Otherwise, we often end up with coercions like (Obj.magic (fun x -> e) : a -> b) : a -> c
  Whereas with this optimization we produce (fun x -> Obj.magic (e : b) : c)  : a -> c
*)
let apply_coercion (pos:Range.t) (g:uenv) (e:mlexpr) (ty:mlty) (expect:mlty) : mlexpr =
    if Util.codegen_fsharp()
    then //magics are not always sound in F#; warn
      FStarC.Errors.log_issue pos Errors.Warning_NoMagicInFSharp [
         text <| Format.fmt2 "Inserted an unsafe type coercion in generated code from %s to %s."
             (Code.string_of_mlty (current_module_of_uenv g) ty)
             (Code.string_of_mlty (current_module_of_uenv g) expect);
         text "This may be unsound in F#.";
      ];
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
        //                   (Code.string_of_mlexpr (current_module_of_uenv g) e)
        //                   (Code.string_of_mlty (current_module_of_uenv g) ty)
        //                   (Code.string_of_mlty (current_module_of_uenv g) expect)
        //                   e ty expect;
        (* The expected type may be an abbreviation and not a literal
        arrow. Try to unfold it. *)
        let rec undelta mlty =
          match Util.udelta_unfold g mlty with
          | Some t -> undelta t
          | None -> mlty
        in
        match e.expr, ty, undelta expect with
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
                      mllb_attrs = [];
                      mllb_name = arg.mlbinder_name;
                      mllb_tysc = Some ([], t0);
                      mllb_add_unit = false;
                      mllb_def = with_ty t0 (MLE_Coerce(with_ty s0 <| MLE_Var arg.mlbinder_name, s0, t0));
                      print_typ=false }
                in
                let body = with_ty s1 <| MLE_Let((NonRec, [lb]), body) in
                with_ty expect (mk_fun {mlbinder_name=arg.mlbinder_name;mlbinder_ty=s0;mlbinder_attrs=[]} body)

        | MLE_Let(lbs, body), _, _ ->
          with_ty expect <| (MLE_Let(lbs, aux body ty expect))

        | MLE_Match(s, branches), _, _ ->
          with_ty expect <| MLE_Match(s, List.map coerce_branch branches)

        | MLE_If(s, b1, b2_opt), _, _ ->
          with_ty expect <| MLE_If(s, aux b1 ty expect, Option.map (fun b2 -> aux b2 ty expect) b2_opt)

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
let maybe_coerce pos (g:uenv) e ty (expect:mlty) : mlexpr =
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
                Format.print2 "\n Effect mismatch on type of %s : %s\n"
                            (Code.string_of_mlexpr (current_module_of_uenv g) e)
                            (Code.string_of_mlty (current_module_of_uenv g) ty)) in
               e //types differ but only on effect labels, which ML/KaRaMeL don't care about; so no coercion needed
          else let _ = debug g (fun () ->
                Format.print3 "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n"
                            (Code.string_of_mlexpr (current_module_of_uenv g) e)
                            (Code.string_of_mlty (current_module_of_uenv g) ty)
                            (Code.string_of_mlty (current_module_of_uenv g) expect)) in
               maybe_eta_expand_coercion g expect (apply_coercion pos g e ty expect)

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
    Because OCaml does not support computations in Type, MLTY_Top is supposed to be used if they are really unaviodable.
    The classic example is the type : T b \def if b then nat else bool. If we dont compute, T true will extract to MLTY_Top.
    Why not \delta? I guess the reason is that unfolding definitions will make the resultant OCaml code less readable.
    However in the Typ_app case,  \delta reduction is done as the second-last resort, just before giving up and returing MLTY_Top;
        a bloated type is atleast as good as MLTY_Top?
    An an F* specific example, unless we unfold Mem x pre post to StState x wp wlp, we have no idea that it should be translated to x
*)
let extraction_norm_steps =
  let extraction_norm_steps_core =
    [Env.AllowUnboundUniverses;
     Env.EraseUniverses;
     Env.Inlining;
     Env.Eager_unfolding;
     Env.Exclude Env.Zeta;
     Env.Primops;
     Env.Unascribe;
     Env.ForExtraction] in

  let extraction_norm_steps_nbe =
    Env.NBE::extraction_norm_steps_core in

  if Options.use_nbe_for_extraction()
  then extraction_norm_steps_nbe
  else extraction_norm_steps_core

let normalize_for_extraction (env:uenv) (e:S.term) =
  N.normalize extraction_norm_steps (tcenv_of_uenv env) e

let maybe_reify_comp g (env:TcEnv.env) (c:S.comp) : S.term =
  match c |> U.comp_effect_name
          |> TcUtil.effect_extraction_mode env with
  | S.Extract_reify ->
    TcEnv.reify_comp env c S.U_unknown
    |> N.normalize extraction_norm_steps env
  | S.Extract_primitive -> U.comp_result c
  | S.Extract_none s ->
    err_cannot_extract_effect (c |> U.comp_effect_name) c.pos s (show c)

let maybe_reify_term (env:TcEnv.env) (t:S.term) (l:lident) : S.term  =
  match TcUtil.effect_extraction_mode env l with
  | S.Extract_reify ->
    TcUtil.norm_reify env
      [TcEnv.Inlining; TcEnv.ForExtraction; TcEnv.Unascribe]
      (U.mk_reify t (Some l))
  | S.Extract_primitive -> t
  | S.Extract_none s ->
    err_cannot_extract_effect l t.pos s (show t)

let has_extract_as_impure_effect (g:uenv) (fv:S.fv) =
  TcEnv.fv_has_attr (tcenv_of_uenv g) fv FStarC.Parser.Const.extract_as_impure_effect_lid

let head_of_type_is_extract_as_impure_effect g t =
  let hd, _ = U.head_and_args t in
  match (U.un_uinst hd).n with
  | Tm_fvar fv -> has_extract_as_impure_effect g fv
  | _ -> false

exception NotSupportedByExtension
let translate_typ_t = g:uenv -> t:term -> mlty

(* See below for register_pre_translate_typ *)
let ref_translate_term_to_mlty : ref translate_typ_t =
  mk_ref (fun _ _ -> raise NotSupportedByExtension)

let translate_term_to_mlty (g:uenv) (t0:term) : mlty =
  !ref_translate_term_to_mlty g t0

let register_pre_translate_typ (f : translate_typ_t) : unit =
  let before = !ref_translate_term_to_mlty in
  let after g t =
    try
      f g t
    with NotSupportedByExtension -> before g t
  in
  ref_translate_term_to_mlty := after

let rec translate_term_to_mlty' (g:uenv) (t0:term) : mlty =
    let arg_as_mlty (g:uenv) (a, _) : mlty =
      (* Translate an argument to a type constructor. Usually, just
      call translate_term_to_mlty. For karamel extraction, try to extract
      what we cannot detect as a type into unit instead of Obj.t, to remain
      in the Low* subset. We should revisit this and make it consistent. *)
      if Options.codegen () <> Some Options.Krml then
        translate_term_to_mlty g a
      else
        if is_type g a
        then translate_term_to_mlty g a
        else MLTY_Erased
    in
    let fv_app_as_mlty (g:uenv) (fv:fv) (args : args) : mlty =
        if not (is_fv_type g fv)
        then MLTY_Top //it was translated as an expression or erased
        else (
            if has_extract_as_impure_effect g fv
            then let (a, _)::_ = args in
                 translate_term_to_mlty g a
            else (
              let formals, _ =
                let (_, fvty), _ = FStarC.TypeChecker.Env.lookup_lid (tcenv_of_uenv g) fv.fv_name in
                let fvty = N.normalize [Env.UnfoldUntil delta_constant; Env.ForExtraction] (tcenv_of_uenv g) fvty in
                U.arrow_formals fvty in
              let mlargs = List.map (arg_as_mlty g) args in
              let mlargs =
                let n_args = List.length args in
                if List.length formals > n_args //it's not fully applied; so apply the rest to unit
                then let _, rest = BU.first_N n_args formals in
                     mlargs @ (List.map (fun _ -> MLTY_Erased) rest)
                else mlargs in
              let nm = UEnv.mlpath_of_lident g fv.fv_name in
              MLTY_Named (mlargs, nm)
            )
        )
    in
    let aux env t =
         let t = SS.compress t in
         match t.n with
          | Tm_type _ -> MLTY_Erased

          | Tm_bvar _
          | Tm_delayed _
          | Tm_unknown -> failwith (Format.fmt1 "Impossible: Unexpected term %s" (show t))

          | Tm_lazy i -> translate_term_to_mlty env (U.unfold_lazy i)

          | Tm_constant _ -> MLTY_Top
          | Tm_quoted _ -> MLTY_Top

          | Tm_uvar _ -> MLTY_Top //really shouldn't have any uvars left; TODO: fatal failure?

          | Tm_meta {tm=t}
          | Tm_refine {b={sort=t}}
          | Tm_uinst(t, _)
          | Tm_ascribed {tm=t} -> translate_term_to_mlty env t

          | Tm_name bv ->
            bv_as_mlty env bv

          | Tm_fvar fv ->
            (* it is not clear whether description in the thesis covers type applications with 0 args.
               However, this case is needed to translate types like nnat, and so far seems to work as expected*)
            fv_app_as_mlty env fv []

          | Tm_arrow {bs; comp=c} ->
            let bs, c = SS.open_comp bs c in
            let mlbs, env = binders_as_ml_binders env bs in
            let codom = maybe_reify_comp env (tcenv_of_uenv env) c in
            let t_ret = translate_term_to_mlty env codom in
            let etag = effect_as_etag env (U.comp_effect_name c) in
            let etag =
              if etag = E_IMPURE then etag
              else if head_of_type_is_extract_as_impure_effect env codom
              then E_IMPURE
              else etag
            in
            let _, t = List.fold_right (fun (_, t) (tag, t') -> (E_PURE, MLTY_Fun(t, tag, t'))) mlbs (etag, t_ret) in
            t

          (*can this be a partial type application? , i.e can the result of this application be something like Type -> Type, or nat -> Type? : Yes *)
          (* should we try to apply additional arguments here? if not, where? FIX!! *)
          | Tm_app _ ->
            let head, args = U.head_and_args_full t in
            let res = match (U.un_uinst head).n, args with
                | Tm_name bv, _ ->
                  (*the args are thrown away, because in OCaml, type variables have type Type and not something like -> .. -> .. Type *)
                  bv_as_mlty env bv

                | Tm_fvar fv, [_]
                  when S.fv_eq_lid fv PC.steel_memory_inv_lid ->
                  translate_term_to_mlty env S.t_unit

                | Tm_fvar fv, _ ->
                  fv_app_as_mlty env fv args

                | _ -> MLTY_Top in
            res

          | Tm_abs {bs;body=ty} ->  (* (sch) rule in \hat{\epsilon} *)
            (* We just translate the body in an extended environment; the binders will just end up as units *)
            let bs, ty = SS.open_term bs ty in
            let bts, env = binders_as_ml_binders env bs in
            translate_term_to_mlty env ty

          | Tm_let _
          | Tm_match _ -> MLTY_Top
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
    if TcUtil.must_erase_for_extraction (tcenv_of_uenv g) t0
    then MLTY_Erased
    else let mlt = aux g t0 in
         if is_top_ty mlt
         then MLTY_Top
         else mlt


and binders_as_ml_binders (g:uenv) (bs:binders) : list (mlident & mlty) & uenv =
    let ml_bs, env = bs |> List.fold_left (fun (ml_bs, env) b ->
            if is_type_binder g b
            then //no first-class polymorphism; so type-binders get wiped out
                 let b = b.binder_bv in
                 let env = extend_ty env b true in
                 let ml_b = (lookup_ty env b).ty_b_name in
                 let ml_b = (ml_b (*name of the binder*),
                             ml_unit_ty (*type of the binder. correspondingly, this argument gets converted to the unit value in application *)) in
                 ml_b::ml_bs, env
            else let b = b.binder_bv in
                 let t = translate_term_to_mlty env b.sort in
                 let env, b, _ = extend_bv env b ([], t) false false in
                 let ml_b = b, t in
                 ml_b::ml_bs, env)
    ([], g) in
    List.rev ml_bs,
    env

let term_as_mlty g t0 =
    let t = N.normalize extraction_norm_steps (tcenv_of_uenv g) t0 in
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

let record_fields (g:uenv) (ty:lident) (fns:list ident) (xs:list 'a) =
  let fns = List.map (fun x -> UEnv.lookup_record_field_name g (ty, x)) fns in
  List.map2 (fun (p, s) x -> (s, x)) fns xs

let resugar_pat g q p = match p with
    | MLP_CTor(d, pats) ->
      begin match is_xtuple d with
        | Some n -> MLP_Tuple(pats)
        | _ ->
          match q with
          | Some (Record_ctor (ty, fns)) ->
              let path = List.map string_of_id (ns_of_lid ty) in
              let fs = record_fields g ty fns pats in
              let path = no_fstar_stubs_ns path in
              MLP_Record(path, fs)
          | _ -> p
      end
    | _ -> p

//extract_pat g p expected_t
//     Translates an F* pattern to an ML pattern
//     The main work is erasing inaccessible (dot) patterns
//     And turning F*'s curried pattern style to ML's fully applied ones
//
//Also, as seen in Bug2595, we need to make sure that the pattern bound
//variables are introduced into the environment at their expected ML type
//rather than their computed F* type, which may be more precise than what
//is typeble in ML.
//E.g.,  Consider
// v: (b:bool & (if b then bool else nat))
// and
// match v with
// | (| true, b |) -> ...
//
// In F*, the sort of b is computed to be bool, since the conditional
// can be eliminated
// But, in OCaml, this should be typed as Obj.t, since the type of v itself is
// (bool, Obj.t) dtuple2
//
let rec extract_one_pat (imp : bool)
                        (g:uenv)
                        (p:S.pat)
                        (expected_ty:mlty)
                        (term_as_mlexpr:uenv -> S.term -> (mlexpr & e_tag & mlty))
    : uenv
    & option (mlpattern & list mlexpr)
    & bool =  //the bool indicates whether or not a magic should be inserted around the scrutinee
    let ok t =
      match expected_ty with
      | MLTY_Top ->
        false
      | _ ->
        let ok = type_leq g t expected_ty in
        if not ok then debug g (fun _ -> Format.print2 "Expected pattern type %s; got pattern type %s\n"
                                                (Code.string_of_mlty (current_module_of_uenv g) expected_ty)
                                                (Code.string_of_mlty (current_module_of_uenv g) t));
        ok
    in
    match p.v with
    | Pat_constant (Const_int (c, swopt))
      when Options.codegen() <> Some Options.Krml ->
      //Karamel supports native integer constants in patterns
      //Don't convert them into `when` clauses
        let mlc, ml_ty =
            match swopt with
            | None ->
              with_ty ml_int_ty <| (MLE_Const (mlconst_of_const p.p (Const_int (c, None)))),
              ml_int_ty
            | Some sw ->
              let source_term =
                  FStarC.ToSyntax.ToSyntax.desugar_machine_integer (tcenv_of_uenv g).dsenv c sw Range.dummyRange in
              let mlterm, _, mlty = term_as_mlexpr g source_term in
              mlterm, mlty
        in
        //these may be extracted to bigint, in which case, we need to emit a when clause
        let g, x = UEnv.new_mlident g in
        let x_exp =
          let x_exp = with_ty expected_ty <| MLE_Var x in
          let coerce x = with_ty ml_ty <| (MLE_Coerce(x, ml_ty, expected_ty)) in
          match expected_ty with
          | MLTY_Top -> coerce x_exp
          | _ ->
            if ok ml_ty
            then x_exp
            else coerce x_exp
        in
        let when_clause = with_ty ml_bool_ty <|
            MLE_App(prims_op_equality, [x_exp;
                                        mlc]) in
        g, Some (MLP_Var x, [when_clause]), ok ml_ty

    | Pat_constant s     ->
        let t : term = TcTerm.tc_constant (tcenv_of_uenv g) Range.dummyRange s in
        let mlty = term_as_mlty g t in
        g, Some (MLP_Const (mlconst_of_const p.p s), []), ok mlty

    | Pat_var x ->
        //In some cases, the computed_mlty based on the F* computed sort x.sort
        //can be more precise than the type in ML. see e.g., Bug2595
        //So, prefer to extend the environment with the expected ML type of the
        //binder rather than the computed_mlty, so that we do not forget to put
        //magics around the uses of the bound variable at use sites
        let g, x, _ = extend_bv g x ([], expected_ty) false imp in
        g,
        (if imp then None else Some (MLP_Var x, [])),
        true //variables are always ok as patterns, no need to insert a magic on the scrutinee when matching a variable

    | Pat_dot_term _ ->
        g, None, true

    | Pat_cons (f, _, pats) ->
        // The main subtlety here, relative to Bug2595, is to propapate the
        // expected type properly

        //1. Lookup the ML name of the constructor d
        //   and the type scheme of the constructor tys
        //   parameterized by the parameters of the inductive it constructs
        let d, tys =
          match try_lookup_fv p.p g f with
          | Some ({exp_b_expr={expr=MLE_Name n}; exp_b_tscheme=ttys}) -> n, ttys
          | Some _ -> failwith "Expected a constructor"
          | None ->
            Errors.raise_error f Errors.Error_ErasedCtor
              (Format.fmt1 "Cannot extract this pattern, the %s constructor was erased" (show f))
        in
        // The prefix of the pattern are dot patterns matching the type parameters
        let nTyVars = List.length (fst tys) in
        let tysVarPats, restPats =  BU.first_N nTyVars pats in
        // f_ty is the instantiated type of the constructor
        let f_ty =
            let mlty_args =
                tysVarPats |>
                List.map
                  (fun (p, _) ->
                    match expected_ty with
                    | MLTY_Top ->
                      //if the expected_ty of the pattern is MLTY_Top
                      //then treat all its parameters as MLTY_Top too
                      MLTY_Top
                    | _ ->
                      //Otherwise, if it has a dot pattern for matching the type parameters
                      match p.v with
                      | Pat_dot_term (Some t) ->
                        //use the type that the dot patterns is instantiated to
                        term_as_mlty g t
                      | _ ->
                        //otherwise, we're back to useing MLTY_Top for this argument
                        MLTY_Top)
            in
            //The instantiated type is of the form t1 -> .. -> tn -> T
            let f_ty = subst tys mlty_args in
            //collect the arguments and result ([t1;...;tn], T)
            Util.uncurry_mlty_fun f_ty
        in
        debug g (fun () -> Format.print2 "@@@Expected type of pattern with head = %s is %s\n"
                          (show f)
                          (let args, t = f_ty in
                           let args =
                               List.map
                                 (Code.string_of_mlty (current_module_of_uenv g))
                                 args
                               |> String.concat " -> "
                           in
                           let res = Code.string_of_mlty (current_module_of_uenv g) t in
                           Format.fmt2 "%s -> %s" args res));
        // Now extract all the type patterns
        // These should all come out as None, if they are dot patterns
        // Their expected type does not matter
        let g, tyMLPats =
          BU.fold_map
            (fun g (p, imp) ->
              let g, p, _ = extract_one_pat true g p MLTY_Top term_as_mlexpr in
              g, p)
            g
            tysVarPats
        in (*not all of these were type vars in ML*)

        // Extract the actual pattern arguments
        let (g, f_ty, sub_pats_ok), restMLPats =
          BU.fold_map
            (fun (g, f_ty, ok) (p, imp) ->
              //The ecpected argument type is the type of the i'th field
              let f_ty, expected_arg_ty =
                match f_ty with
                | (hd::rest, res) -> (rest, res), hd
                | _ -> ([], MLTY_Top), MLTY_Top
              in
              let g, p, ok' = extract_one_pat false g p expected_arg_ty term_as_mlexpr in
              (g, f_ty, ok && ok'), p)
            (g, f_ty, true)
            restPats
        in

        let mlPats, when_clauses =
          List.append tyMLPats restMLPats
          |> List.collect (function (Some x) -> [x] | _ -> [])
          |> List.split
        in

        let pat_ty_compat =
          match f_ty with
          | ([], t) -> ok t
          | _ -> false //arity mismatch, should be impossible
        in
        g,
        Some (resugar_pat g f.fv_qual (MLP_CTor (d, mlPats)),
              when_clauses |> List.flatten),
        sub_pats_ok &&
        pat_ty_compat

let extract_pat (g:uenv) (p:S.pat) (expected_t:mlty)
                (term_as_mlexpr: uenv -> S.term -> (mlexpr & e_tag & mlty))
    : (uenv & list (mlpattern & option mlexpr) & bool) =
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
    let g, (p, whens), b = extract_one_pat g p expected_t in
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
let maybe_eta_data_and_project_record (g:uenv) (qual : option fv_qual) (residualType : mlty)  (mlAppExpr : mlexpr) : mlexpr =
    let rec eta_args g more_args t = match t with
      | MLTY_Fun (t0, _, t1) ->
        let g, x = UEnv.new_mlident g in
        eta_args g (((x, t0), with_ty t0 <| MLE_Var x)::more_args) t1
      | MLTY_Named (_, _) -> List.rev more_args, t
      | _ -> failwith (Format.fmt2 "Impossible: Head type is not an arrow: (%s : %s)"
                                (Code.string_of_mlexpr (current_module_of_uenv g) mlAppExpr)
                                (Code.string_of_mlty (current_module_of_uenv g) t))
    in
    let as_record qual e =
      match e.expr, qual with
      | MLE_CTor(_, args), Some (Record_ctor(tyname, fields)) ->
        let path = List.map string_of_id (ns_of_lid tyname) in
        let fields = record_fields g tyname fields args in
        let path = no_fstar_stubs_ns path in
        with_ty e.mlty <| MLE_Record (path, tyname |> ident_of_lid |> string_of_id, fields)
      | _ -> e
     in
    let resugar_and_maybe_eta qual e =
        let eargs, tres = eta_args g [] residualType in
        match eargs with
        | [] -> Util.resugar_exp (as_record qual e)
        | _ ->
          let binders, eargs = List.unzip eargs in
          match e.expr with
          | MLE_CTor(head, args) ->
            let body = Util.resugar_exp <| (as_record qual <| (with_ty tres <| MLE_CTor(head, args@eargs))) in
            with_ty e.mlty <| MLE_Fun(List.map (fun (x,t) -> {mlbinder_name=x;mlbinder_ty=t;mlbinder_attrs=[]}) binders, body)
          | _ -> failwith "Impossible: Not a constructor"
    in
    match mlAppExpr.expr, qual with
        | _, None -> mlAppExpr

        | MLE_App({expr=MLE_Name mlp}, mle::args), Some (Record_projector (constrname, f))
        | MLE_App({expr=MLE_TApp({expr=MLE_Name mlp}, _)}, mle::args), Some (Record_projector (constrname, f))->
          let fn = UEnv.lookup_record_field_name g (TcEnv.typ_of_datacon (tcenv_of_uenv g) constrname, f) in
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
    | E_ERASABLE, MLTY_Erased
    | E_PURE, MLTY_Erased -> ml_unit, E_PURE
    | _ -> ml_e, tag

let translate_t = g:uenv -> t:term -> mlexpr & e_tag & mlty
let ref_term_as_mlexpr : ref translate_t =
  mk_ref (fun _ _ -> raise NotSupportedByExtension)

// An "after" pass does not make much sense... since term_as_mlexpr' here
// (the default one) catches everything.
let register_pre_translate (f : translate_t) : unit =
  let before = !ref_term_as_mlexpr in
  let after g t =
    try
      f g t
    with NotSupportedByExtension -> before g t
  in
  ref_term_as_mlexpr := after

type lb_sig =
    lbname //just lbname returned back
  & e_tag  //the ML version of the effect label lbeff
  & (typ   //just the source type lbtyp=t, after compression
     & (S.binders //the erased type binders
        & mltyscheme)) //translation of the source type t as a ML type scheme
  & bool   //whether or not to add a unit argument
  & bool   //whether this was marked CInline
  & term   //the term e, maybe after some type binders have been erased

let rec extract_lb_sig (g:uenv) (lbs:letbindings) : list lb_sig =
    let maybe_generalize {lbname=lbname_; lbeff=lbeff; lbtyp=lbtyp; lbdef=lbdef; lbattrs=lbattrs} : lb_sig =
              let has_c_inline = U.has_attribute lbattrs PC.c_inline_attr in
              // begin match lbattrs with
              // | [] -> ()
              // | _ ->
              //   // Format.print1 "Testing whether term has any rename_let %s..." "";
              //   begin match U.get_attribute PC.rename_let_attr lbattrs with
              //   | Some ((arg, _) :: _) ->
              //     begin match arg.n with
              //     | Tm_constant (Const_string (arg, _)) ->
              //       Format.print1 "Term has rename_let %s\n" arg
              //     | _ -> Format.print1 "Term has some rename_let %s\n" ""
              //     end
              //   | _ -> Format.print1 "no rename_let found %s\n" ""
              //   end
              // end;
              let f_e = effect_as_etag g lbeff in
              let lbtyp = SS.compress lbtyp in
              let no_gen () =
                  let expected_t = term_as_mlty g lbtyp in
                  (lbname_, f_e, (lbtyp, ([], ([],expected_t))), false, has_c_inline, lbdef)
              in
              if TcUtil.must_erase_for_extraction (tcenv_of_uenv g) lbtyp
              then (lbname_, f_e, (lbtyp, ([], ([], MLTY_Erased))), false, has_c_inline, lbdef)
              else  //              debug g (fun () -> printfn "Let %s at type %s; expected effect is %A\n" (show lbname) (Print.typ_to_string t) f_e);
                match lbtyp.n with
                | Tm_arrow {bs; comp=c} when (List.hd bs |> is_type_binder g) ->
                   let bs, c = SS.open_comp bs c in
                  //need to generalize, but will erase all the type abstractions;
                  //If, after erasure, what remains is not a value, then add an extra unit arg. to preserve order of evaluation/generativity
                  //and to circumvent the value restriction

                  //We also erase type arguments that abstract over impure functions,
                  //replacing the type arguments with a single unit.
                  //For example, `a:Type -> Dv a` is extracted to `unit -Impure-> 'a`
                  //The important thing is that we retain an effect tag on the arrow to note
                  //that the type application is impure.
                  //See Issue #3473
                   let etag_of_comp c = effect_as_etag g (U.comp_effect_name c) in
                   let tbinders, eff_body, tbody =
                        match BU.prefix_until (fun x -> not (is_type_binder g x)) bs with
                        | None -> bs, etag_of_comp c, U.comp_result c
                        | Some (bs, b, rest) -> bs, E_PURE, U.arrow (b::rest) c
                  in
                   let n_tbinders = List.length tbinders in
                   let lbdef = normalize_abs lbdef |> U.unmeta in
                   let tbinders_as_ty_params env = List.map (fun ({binder_bv=x; binder_attrs}) -> {
                     ty_param_name = (UEnv.lookup_ty env x).ty_b_name;
                     ty_param_attrs = List.map (fun attr -> let e, _, _ = term_as_mlexpr g attr in e) binder_attrs}) in
                   begin match lbdef.n with
                      | Tm_abs {bs; body; rc_opt=copt} ->
                        let bs, body = SS.open_term bs body in
                        if n_tbinders <= List.length bs
                        then let targs, rest_args = BU.first_N n_tbinders bs in
                             let expected_source_ty =
                                let s = List.map2 (fun ({binder_bv=x}) ({binder_bv=y}) -> S.NT(x, S.bv_to_name y)) tbinders targs in
                                SS.subst s tbody in
                             let env = List.fold_left (fun env ({binder_bv=a}) -> UEnv.extend_ty env a false) g targs in
                             let expected_t = term_as_mlty env expected_source_ty in
                             let polytype = tbinders_as_ty_params env targs, expected_t in
                             let add_unit =
                                match rest_args with
                                | [] ->
                                  not (is_fstar_value body) //if it's a pure type app, then it will be extracted to a value in ML; so don't add a unit
                                  || not (U.is_pure_comp c)
                                | _ -> false in
                             let rest_args = if add_unit then (unit_binder()::rest_args) else rest_args in
                             let polytype =
                                if add_unit
                                then (* record the effect of type application, eff_body *)
                                      push_unit eff_body polytype
                                else polytype
                             in
                             let body = U.abs rest_args body copt in
                             (lbname_, f_e, (lbtyp, (targs, polytype)), add_unit, has_c_inline, body)

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
                       let env = List.fold_left (fun env ({binder_bv=a}) -> UEnv.extend_ty env a false) g tbinders in
                       let expected_t = term_as_mlty env tbody in
                       let polytype = tbinders_as_ty_params env tbinders, expected_t in
                       //In this case, an eta expansion is safe
                       let args = tbinders |> List.map (fun ({binder_bv=bv}) -> S.bv_to_name bv |> as_arg) in
                       let e = mk (Tm_app {hd=lbdef; args}) lbdef.pos in
                       (lbname_, f_e, (lbtyp, (tbinders, polytype)), false, has_c_inline, e)

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

and extract_lb_iface (g:uenv) (lbs:letbindings)
    : uenv & list (fv & exp_binding) =
    let is_top = FStarC.Syntax.Syntax.is_top_level (snd lbs) in
    let is_rec = not is_top && fst lbs in
    let lbs = extract_lb_sig g lbs in
    BU.fold_map #_ #(Syntax.Syntax.lbname & _ & _ & _ & _ & _) (fun env
                     (lbname, _e_tag, (typ, (_binders, mltyscheme)), add_unit, _has_c_inline, _body) ->
                  let env, _, exp_binding =
                      UEnv.extend_lb env lbname typ mltyscheme add_unit in
                  env, (Inr?.v lbname, exp_binding))
                g
                lbs

//The main extraction function
and check_term_as_mlexpr (g:uenv) (e:term) (f:e_tag) (ty:mlty) :  (mlexpr & mlty) =
    debug g
      (fun () -> Format.print3 "Checking %s at type %s and eff %s\n"
                        (show e)
                        (Code.string_of_mlty (current_module_of_uenv g) ty)
                        (Util.eff_to_string f));
    match f, ty with
    | E_ERASABLE, _
    | E_PURE, MLTY_Erased -> ml_unit, MLTY_Erased
    | _ ->
      let ml_e, tag, t = term_as_mlexpr g e in
      debug g (fun _ ->
        Format.print4 "Extracted %s to %s at eff %s and type %s\n"
          (show e)
          (Code.string_of_mlexpr (current_module_of_uenv g) ml_e)
          (Util.eff_to_string tag)
          (Code.string_of_mlty (current_module_of_uenv g) t));
      if eff_leq tag f
      then maybe_coerce e.pos g ml_e t ty, ty
      else match tag, f, ty with
           | E_ERASABLE, E_PURE, MLTY_Erased -> //effect downgrading for erased results
             maybe_coerce e.pos g ml_e t ty, ty
           | _ ->
             err_unexpected_eff g e ty f tag;
             maybe_coerce e.pos g ml_e t ty, ty

and term_as_mlexpr (g:uenv) (e:term) : (mlexpr & e_tag & mlty) =
    let e, f, t = !ref_term_as_mlexpr g e in
    let e, f = maybe_promote_effect e f t in
    e, f, t


and term_as_mlexpr' (g:uenv) (top:term) : (mlexpr & e_tag & mlty) =
    let top = SS.compress top in
    (debug g (fun u -> Format.print_string (Format.fmt3 "%s: term_as_mlexpr' (%s) :  %s \n"
        (Range.string_of_range top.pos)
        (tag_of top)
        (show top))));

    (*
     * AR: Following util functions are to implement the following rule:
     *     (match e with | P_i -> body_i) args ~~>
     *     (match e with | P_i -> body_i args)
     *
     *     This opens up more opportunities for reduction,
     *       especially when using layered effects where reification leads to
     *       some lambdas introduced and applied this way
     *
     *     Doing it naively results in code blowup (if args are big terms)
     *       so controlling it specifically
     *)
    let is_match t =
      match (t |> SS.compress |> U.unascribe).n with
      | Tm_match _ -> true
      | _ -> false in

    let should_apply_to_match_branches : S.args -> bool =
      List.for_all (fun (t, _) ->
        match (t |> SS.compress).n with
        | Tm_name _ | Tm_fvar _ | Tm_constant _ -> true | _ -> false) in

    //precondition: is_match head = true
    let apply_to_match_branches head args =
      match (head |> SS.compress |> U.unascribe).n with
      | Tm_match {scrutinee; brs=branches} ->
        let branches =
          branches |> List.map (fun (pat, when_opt, body) ->
            pat, when_opt, { body with n = Tm_app {hd=body; args} }
          ) in
        { head with n = Tm_match {scrutinee; ret_opt=None; brs=branches; rc_opt=None} }  //AR: dropping the return annotation and rc
      | _ -> failwith "Impossible! cannot apply args to match branches if head is not a match" in

    let t = SS.compress top in
    match t.n with
        | Tm_unknown
        | Tm_delayed _
        | Tm_uvar _
        | Tm_bvar _ -> failwith (Format.fmt1 "Impossible: Unexpected term: %s" (tag_of t))

        | Tm_lazy i -> term_as_mlexpr g (U.unfold_lazy i)

        | Tm_type _
        | Tm_refine _
        | Tm_arrow _ ->
          ml_unit, E_PURE, ml_unit_ty

        | Tm_quoted (qt, { qkind = Quote_dynamic }) ->
          let ({exp_b_expr=fw}) = UEnv.lookup_fv t.pos g (S.lid_as_fv (PC.failwith_lid()) None) in
          with_ty ml_int_ty <| MLE_App(fw, [with_ty ml_string_ty <| MLE_Const (MLC_String "Cannot evaluate open quotation at runtime")]),
          E_PURE,
          ml_int_ty

        | Tm_quoted (qt, { qkind = Quote_static; antiquotations = (shift, aqs) }) ->
          begin match R.inspect_ln qt with
          | RD.Tv_BVar bv ->
            (* If it's a variable, check whether it's an antiquotation or just a bvar node *)
            if bv.index < shift then
              (* just a local bvar *)
              let tv' = RD.Tv_BVar bv in
              let tv = EMB.embed tv' t.pos None EMB.id_norm_cb in
              let t = U.mk_app (RC.refl_constant_term RC.fstar_refl_pack_ln) [S.as_arg tv] in
              term_as_mlexpr g t
            else
              let tm = S.lookup_aq bv (shift, aqs) in
              term_as_mlexpr g tm

          | tv ->
            (* Else, just embed recursively. *)
            let tv = EMB.embed #_ #(RE.e_term_view_aq (shift, aqs)) tv t.pos None EMB.id_norm_cb in
            let t = U.mk_app (RC.refl_constant_term RC.fstar_refl_pack_ln) [S.as_arg tv] in
            term_as_mlexpr g t
          end

        | Tm_meta {tm=t; meta=Meta_monadic (m, _)} ->
          //
          // A meta monadic node
          // We should have taken care of it when we were reifying the Tm_abs
          // But it is ok, if the effect is primitive
          //
          let t = SS.compress t in
          begin match t.n with
            | Tm_let {lbs=(false, [lb]); body} when Inl? lb.lbname ->
              let tcenv = tcenv_of_uenv g in
              let ed, qualifiers = Option.must (TypeChecker.Env.effect_decl_opt tcenv m) in
              if TcUtil.effect_extraction_mode tcenv ed.mname = S.Extract_primitive
              then term_as_mlexpr g t
              else
                failwith
                  (Format.fmt1
                     "This should not happen (should have been handled at Tm_abs level for effect %s)"
                     (string_of_lid ed.mname))
            | _ -> term_as_mlexpr g t
         end

        | Tm_meta {tm=t; meta=Meta_monadic_lift (m1, _m2, _ty)}
          when effect_as_etag g m1 = E_ERASABLE ->
          (*
           * We would come here if m2 is not erasable,
           *   because if it is, we would not have descended into the outer expression
           *
           * So if m2 is not erasable, how is erasing this lift justified?
           *
           * A: The typechecker ensures that _ty is non-informative
           *)
          ml_unit, E_ERASABLE, MLTY_Erased

        | Tm_meta {tm=t; meta=Meta_desugared (Machine_integer (signedness, width))} ->

            let t = SS.compress t in
            let t = U.unascribe t in
            (match t.n with
             (* Should we check if hd here is [__][u]int_to_t? *)
            | Tm_app {hd; args=[x, _]} ->
              (let x = SS.compress x in
               let x = U.unascribe x in
               match x.n with
               | Tm_constant (Const_int (repr, _)) ->
                 (let _, ty, _ =
                   TcTerm.typeof_tot_or_gtot_term (tcenv_of_uenv g) t true in
                 let ml_ty = term_as_mlty g ty in
                 let ml_const = Const_int (repr, Some (signedness, width)) in
                 with_ty ml_ty (mlexpr_of_const t.pos ml_const), E_PURE, ml_ty)
               |_ -> term_as_mlexpr g t)
            | _ -> term_as_mlexpr g t)

        | Tm_meta {tm=t}  //TODO: handle the resugaring in case it's a 'Meta_desugared' ... for more readable output
        | Tm_uinst(t, _) ->
          term_as_mlexpr g t

        | Tm_constant c ->
          let tcenv = tcenv_of_uenv g in
          let _, ty, _ = TcTerm.typeof_tot_or_gtot_term tcenv t true in  //AR: TODO: type_of_well_typed?
          if TcUtil.must_erase_for_extraction tcenv ty
          then ml_unit, E_PURE, MLTY_Erased
          else let ml_ty = term_as_mlty g ty in
               with_ty ml_ty (mlexpr_of_const t.pos c), E_PURE, ml_ty

        | Tm_name _ -> //lookup in g; decide if its in left or right; tag is Pure because it's just a variable
          if is_type g t //Here, we really need to be certain that g is a type; unclear if level ensures it
          then ml_unit, E_PURE, ml_unit_ty //Erase type argument
          else begin match lookup_term g t with
                | Inl _, _ ->
                  ml_unit, E_PURE, ml_unit_ty

                | Inr ({exp_b_expr=x; exp_b_tscheme=mltys; exp_b_eff=etag}), qual ->
                  //etag is the effect associated with simply using t, since it may
                  //be an effectful type application in F*
                  //in the common case, etag is E_PURE
                  begin match mltys with
                    | ([], t) when t=ml_unit_ty ->
                      ml_unit, etag, t //optimize (x:unit) to ()

                    | ([], t) ->
                      maybe_eta_data_and_project_record g qual t x, etag, t

                    | _ ->
                      (* We have a first-class polymorphic value;
                         Extract it to ML by instantiating its type arguments to MLTY_Erased *)
                      instantiate_maybe_partial g x etag mltys []
                  end
               end

        | Tm_fvar fv -> //Nearly identical to Tm_name, except the fv may have been erased altogether; if so return Erased
          if is_type g t //Here, we really need to be certain that g is a type
          then ml_unit, E_PURE, ml_unit_ty //Erase type argument
          else
          begin
               match try_lookup_fv t.pos g fv with
               | None -> //it's been erased
                 // Errors.log_issue t (Errors.Error_CallToErased,
                 //                         Format.fmt1 "Attempting to extract a call into erased function %s" (show fv));
                 ml_unit, E_PURE, MLTY_Erased

               | Some {exp_b_expr=x; exp_b_tscheme=mltys} ->
                 let _ = debug g (fun () ->
                          Format.print3 "looked up %s: got %s at %s \n"
                              (show fv)
                              (show x)
                              (show (snd mltys))) in
                 begin match mltys with
                    | ([], t) when (t=ml_unit_ty) -> ml_unit, E_PURE, t //optimize (x:unit) to ()
                    | ([], t) -> maybe_eta_data_and_project_record g fv.fv_qual t x, E_PURE, t
                    | _ -> instantiate_maybe_partial g x E_PURE mltys []
                 end
          end

        | Tm_abs {bs;body;rc_opt=rcopt} (* the annotated computation type of the body *) ->
          let bs, body = SS.open_term bs body in
          let ml_bs, env = binders_as_ml_binders g bs in
          let ml_bs = List.map2 (fun (x,t) b -> {
            mlbinder_name=x;
            mlbinder_ty=t;
            mlbinder_attrs=List.map (fun attr -> let e, _, _ = term_as_mlexpr env attr in e) b.binder_attrs;
          }) ml_bs bs in
          let body =
            match rcopt with
            | Some rc ->
              maybe_reify_term (tcenv_of_uenv env) body rc.residual_effect
            | None -> debug g (fun () -> Format.print1 "No computation type for: %s\n" (show body)); body in
          let ml_body, f, t = term_as_mlexpr env body in
          let f, tfun = List.fold_right
            (fun {mlbinder_ty=targ} (f, t) -> E_PURE, MLTY_Fun (targ, f, t))
            ml_bs (f, t) in
          with_ty tfun <| MLE_Fun(ml_bs, ml_body), f, tfun

        (* Extract `range_of x` to a literal range. *)
        | Tm_app {hd={n=Tm_constant Const_range_of}; args=[(a1, _)]} ->
          let ty = term_as_mlty g (tabbrev PC.range_lid) in
          with_ty ty <| mlexpr_of_range a1.pos, E_PURE, ty

        (* Ignore `set_range_of` *)
        | Tm_app {hd={n=Tm_constant Const_set_range_of}; args=[(t, _); (r, _)]} ->
          term_as_mlexpr g t

        (* Cannot extract a reflect (aborts at runtime). *)
        | Tm_app {hd={n=Tm_constant (Const_reflect _)}} ->
            let ({exp_b_expr=fw}) = UEnv.lookup_fv t.pos g (S.lid_as_fv (PC.failwith_lid()) None) in
            with_ty ml_int_ty <| MLE_App(fw, [with_ty ml_string_ty <| MLE_Const (MLC_String "Extraction of reflect is not supported")]),
            E_PURE,
            ml_int_ty

        (* Push applications into match branches *)
        | Tm_app {hd=head; args}
          when is_match head &&
               args |> should_apply_to_match_branches ->
          args |> apply_to_match_branches head |> term_as_mlexpr g

        (* A regular application. *)
        | Tm_app {hd=head; args} ->
          let is_total rc =
              Ident.lid_equals rc.residual_effect PC.effect_Tot_lid
              || rc.residual_flags |> List.existsb (function TOTAL -> true | _ -> false)
          in

          begin match (head |> SS.compress |> U.unascribe).n with  //AR: unascribe, gives more opportunities for beta
            (*
             * AR: do we need is_total rc here?
             *)
            | Tm_abs {bs; rc_opt=rc} (* when is_total _rc *) -> //this is a beta_redex --- also reduce it before extraction
              t
              |> N.normalize [Env.Beta; Env.Iota; Env.Zeta; Env.EraseUniverses; Env.AllowUnboundUniverses; Env.ForExtraction] (tcenv_of_uenv g)
              |> term_as_mlexpr g

            | Tm_constant (Const_reify lopt) ->
              (match lopt with
               | Some l ->
                 let e = maybe_reify_term (tcenv_of_uenv g) (args |> List.hd |> fst) l in
                 let tm = S.mk_Tm_app (TcUtil.remove_reify e) (List.tl args) t.pos in
                 term_as_mlexpr g tm
               | None ->
                 raise_error top Errors.Fatal_ExtractionUnsupported
                   (Format.fmt1 "Cannot extract %s (reify effect is not set)" (show top))
              )

            | _ ->

              let rec extract_app is_data (mlhead, mlargs_f) (f(*:e_tag*), t (* the type of (mlhead mlargs) *)) restArgs =
                let mk_head () =
                    let mlargs = List.rev mlargs_f |> List.map fst in
                    with_ty t <| MLE_App(mlhead, mlargs)
                in
                debug g (fun () -> Format.print3 "extract_app ml_head=%s type of head = %s, next arg = %s\n"
                                (Code.string_of_mlexpr (current_module_of_uenv g) (mk_head()))
                                (Code.string_of_mlty (current_module_of_uenv g) t)
                                (match restArgs with [] -> "none" | (hd, _)::_ -> show hd));
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
                            && FStarC.TypeChecker.Util.short_circuit_head head
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
                        | (a0, Some ({ aqual_implicit = true }))::args, MLTY_Fun(_, f', t) ->
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
                      let (head_ml, (vars, t), head_eff), qual =
                        match lookup_term g head with
                        | Inr exp_b, q ->
                          debug g (fun () ->
                              Format.print4 "@@@looked up %s: got %s at %s with eff <%s>\n"
                                  (show head)
                                  (show exp_b.exp_b_expr)
                                  (show (snd exp_b.exp_b_tscheme))
                                  (show exp_b.exp_b_eff));
                          (exp_b.exp_b_expr, exp_b.exp_b_tscheme, exp_b.exp_b_eff), q
                        | _ -> failwith "FIXME Ty" in

                      let has_typ_apps = match args with
                        | (a, _)::_ -> is_type g a
                        | _ -> false in
                      let head_ml, head_eff, head_t, args =
                          (* Here, we have, say, f extracted to head_ml, with a polymorphic ML type with n type-args
                             If, in F*, `f` is applied to exactly `n` type args, then things are easy:
                               We extract those n arguments to ML types
                               Instantiate the type scheme of head_ml
                               Generate a type application node, and continue
                             If `f` is only partially applied, i.e., to less than `n` args then
                               we follow a strategy similar to the case of Tm_name and Tm_fvar
                               when we deal with higher rank polymorphism.
                               i.e., we use instantiate_maybe_partial to "complete" the type application
                               with additional MLTY_Erased type arguments.

                             Note, in both cases, we preserve type application in the ML AST
                             since KaRaMeL requires it.

                             See e.g., bug #1694.
                           *)
                          let n = List.length vars in
                          let provided_type_args, rest =
                            if List.length args <= n
                            then List.map (fun (x, _) -> term_as_mlty g x) args,
                                 []
                            else let prefix, rest = BU.first_N n args in
                                 List.map (fun (x, _) -> term_as_mlty g x) prefix,
                                 rest
                          in
                          let head, head_eff, t =
                              match head_ml.expr with
                              | MLE_Name _
                              | MLE_Var _ ->
                                let head, eff, t =
                                  instantiate_maybe_partial g head_ml head_eff (vars, t) provided_type_args
                                in
                                head, eff, t

                              | MLE_App(head, [{expr=MLE_Const MLC_Unit}]) ->
                                //this happens when the extraction inserted an extra
                                //unit argument to circumvent ML's value restriction
                                let head, eff, t =
                                  instantiate_maybe_partial g head head_eff (vars, t) provided_type_args
                                in
                                MLE_App(head, [ ml_unit ]) |> with_ty t,
                                eff,
                                t

                              | _ -> failwith "Impossible: Unexpected head term"
                          in
                          head, head_eff, t, rest
                       in
                       begin
                       match args with
                       | [] -> maybe_eta_data_and_project_record g qual head_t head_ml, head_eff, head_t
                       | _  -> extract_app_maybe_projector qual head_ml (head_eff, head_t) args
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
                     (match try_lookup_fv t.pos g fv with
                      | None -> //erased head
                        // Errors.log_issue t
                        //   (Errors.Error_CallToErased,
                        //    Format.fmt1 "Attempting to extract a call into erased function %s" (show fv));
                        ml_unit, E_PURE, MLTY_Erased
                      | _ ->
                        extract_app_with_instantiations ())

                   | _ ->
                     extract_app_with_instantiations ()
            end

        | Tm_ascribed {tm=e0; asc=(tc, _, _); eff_opt=f} ->
          let t = match tc with
            | Inl t -> term_as_mlty g t
            | Inr c -> term_as_mlty g (maybe_reify_comp g (tcenv_of_uenv g) c) in
          let f = match f with
            | None -> failwith "Ascription node with an empty effect label"
            | Some l -> effect_as_etag g l in
          let e, t = check_term_as_mlexpr g e0 f t in
          e, f, t

        | Tm_let {lbs=(false, [lb]); body=e'}
          when not (is_top_level [lb])
          && Some? (U.get_attribute FStarC.Parser.Const.rename_let_attr lb.lbattrs) ->
          let b = S.mk_binder (Inl?.v lb.lbname) in
          let ({binder_bv=x}), body = SS.open_term_1 b e' in
          // Format.print_string "Reached let with rename_let attribute\n";
          let suggested_name =
              let attr = U.get_attribute FStarC.Parser.Const.rename_let_attr lb.lbattrs in
              match attr with
              | Some ([(str, _)]) ->
                begin
                match (SS.compress str).n with
                | Tm_constant (Const_string (s, _))
                  when s <> "" ->
                  // Format.print1 "Found suggested name %s\n" s;
                  let id = Ident.mk_ident (s, range_of_bv x) in
                  let bv = { ppname = id; index = 0; sort = x.sort } in
                  let bv = freshen_bv bv in
                  Some bv
                | _ ->
                  Errors.log_issue top Errors.Warning_UnrecognizedAttribute
                    "Ignoring ill-formed application of `rename_let`";
                  None
                end

              | Some _ ->
                  Errors.log_issue top Errors.Warning_UnrecognizedAttribute
                    "Ignoring ill-formed application of `rename_let`";
                None

              | None ->
                None
          in
          let remove_attr attrs =
            let _, other_attrs =
              List.partition
                (fun attr -> Some? (U.get_attribute PC.rename_let_attr [attr]))
                lb.lbattrs
            in
            other_attrs
          in
          let maybe_rewritten_let =
            match suggested_name with
            | None ->
              let other_attrs = remove_attr lb.lbattrs in
              Tm_let {lbs=(false, [{lb with lbattrs=other_attrs}]); body=e'}

            | Some y ->
              let other_attrs = remove_attr lb.lbattrs in
              let rename = [NT(x, S.bv_to_name y)] in
              let body = SS.close ([S.mk_binder y]) (SS.subst rename body) in
              let lb = { lb with lbname=Inl y; lbattrs=other_attrs } in
              Tm_let {lbs=(false, [lb]); body}
           in
           let top = {top with n = maybe_rewritten_let } in
           term_as_mlexpr g top

        | Tm_let {lbs=(is_rec, lbs); body=e'} ->
          let top_level = is_top_level lbs in
          let lbs, e' =
            if is_rec
            then SS.open_let_rec lbs e'
            else if is_top_level lbs
                 then lbs, e'
                 else let lb = List.hd lbs in
                      let x = S.freshen_bv (Inl?.v lb.lbname) in
                      let lb = {lb with lbname=Inl x} in
                      let e' = SS.subst [DB(0, x)] e' in
                      [lb], e' in
          let lbs =
            if top_level
            then
            let tcenv = TcEnv.set_current_module (tcenv_of_uenv g)
                                (Ident.lid_of_path ((fst (current_module_of_uenv g)) @ [snd (current_module_of_uenv g)]) Range.dummyRange) in
            lbs |> List.map (fun lb ->
                    // let tcenv = TcEnv.set_current_module (tcenv_of_uenv g)
                    //             (Ident.lid_of_path ((fst (current_module_of_uenv g)) @ [snd (current_module_of_uenv g)]) Range.dummyRange) in
                    // debug g (fun () ->
                    //            Format.print1 "!!!!!!!About to normalize: %s\n" (show lb.lbdef);
                    //            Options.set_option "debug" (Options.List [Options.String "Norm"; Options.String "Extraction"]));
                    let lbdef =
                        let norm_call () =
                            Profiling.profile
                              (fun () ->
                                N.normalize (Env.PureSubtermsWithinComputations::Env.Reify::extraction_norm_steps) tcenv lb.lbdef)
                              (Some (Ident.string_of_lid (Env.current_module tcenv)))
                              "FStarC.Extraction.ML.Term.normalize_lb_def"
                        in
                        if !dbg_Extraction || !dbg_ExtractionNorm
                        then let _ = Format.print2 "Starting to normalize top-level let %s = %s\n"
                                       (show lb.lbname)
                                       (show lb.lbdef)
                             in
                             let a = norm_call() in
                             Format.print1 "Normalized to %s\n" (show a);
                             a
                        else norm_call ()
                    in
                    {lb with lbdef=lbdef})
            else lbs
          in

          let check_lb env (nm_sig : mlident & lb_sig) =
              let (nm, (_lbname, f, (_t, (targs, polytype)), add_unit, has_c_inline, e)) = nm_sig in
              let env = List.fold_left (fun env ({binder_bv=a}) -> UEnv.extend_ty env a false) env targs in
              let expected_t = snd polytype in
              let e, ty = check_term_as_mlexpr env e f expected_t in
              let e, f = maybe_promote_effect e f expected_t in
              let meta =
                  match f, ty with
                  | E_PURE, MLTY_Erased
                  | E_ERASABLE, MLTY_Erased -> [Erased]
                  | _ -> []
              in
              let meta = if has_c_inline || Options.Ext.get "extraction_inline_all" <> "" then CInline :: meta else meta in
              f, {mllb_meta = meta; mllb_attrs = []; mllb_name=nm; mllb_tysc=Some polytype; mllb_add_unit=add_unit; mllb_def=e; print_typ=true}
          in
          let lbs = extract_lb_sig g (is_rec, lbs) in

          (* env_burn only matters for non-recursive lets and simply burns
           * the let bound variable in its own definition to generate
           * code that is more understandable. We only do it for OCaml,
           * to not affect Karamel naming. *)
          let env_body, lbs, env_burn = List.fold_right (fun lb (env, lbs, env_burn) ->
              let (lbname, _, (t, (_, polytype)), add_unit, _has_c_inline, _) = lb in
              let env, nm, _ = UEnv.extend_lb env lbname t polytype add_unit in
              let env_burn =
                if Options.codegen () <> Some Options.Krml
                then UEnv.burn_name env_burn nm
                else env_burn
              in
              env, (nm,lb)::lbs, env_burn) lbs (g, [], g)
          in

          let env_def = if is_rec then env_body else env_burn in

          let lbs = lbs |> List.map (check_lb env_def)  in

          let e'_rng = e'.pos in

          let e', f', t' = term_as_mlexpr env_body e' in

          let f = join_l e'_rng (f'::List.map fst lbs) in

          let is_rec = if is_rec = true then Rec else NonRec in

          with_ty_loc t' (mk_MLE_Let top_level (is_rec, List.map snd lbs) e') (Util.mlloc_of_range t.pos), f, t'

      | Tm_match {scrutinee;brs=pats} ->
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
             let mlbranches : list (mlpattern & (option mlexpr & e_tag) & (mlexpr & e_tag & mlty))
               = List.flatten mlbranches in
             //if the type of the pattern isn't compatible with the type of the scrutinee
             //    insert a magic around the scrutinee
             let e = if pat_t_compat
                     then e
                     else (debug g (fun _ -> Format.print2 "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                                (Code.string_of_mlexpr (current_module_of_uenv g) e)
                                                (Code.string_of_mlty (current_module_of_uenv g) t_e));
                           with_ty t_e <| MLE_Coerce (e, t_e, MLTY_Top)) in
             begin match mlbranches with
                | [] ->
                    let ({exp_b_expr=fw}) = UEnv.lookup_fv t.pos g (S.lid_as_fv (PC.failwith_lid()) None) in
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
    let _, fstar_disc_type = fst <| TypeChecker.Env.lookup_lid (tcenv_of_uenv env) discName in
    let g, wildcards = match (SS.compress fstar_disc_type).n with
        | Tm_arrow {bs=binders} ->
          let binders =
              binders
              |> List.filter (function ({binder_qual=Some (Implicit _)}) -> true | _ -> false)
          in
          List.fold_right
            (fun _ (g, vs) ->
              let g, v = UEnv.new_mlident g in
              g, ((v, MLTY_Top) :: vs))
             binders
             (env, [])
        | _ ->
            failwith "Discriminator must be a function"
    in
    // Unfortunately, looking up the constructor name in the environment would give us a _curried_ type.
    // So, we don't bother popping arrows until we find the return type of the constructor.
    // We just use Top.
    let g, mlid = UEnv.new_mlident g in
    let targ = MLTY_Top in
    // Ugly hack: we don't know what to put in there, so we just write a dummy
    // polymorphic value to make sure that the type is not printed.
    let disc_ty = MLTY_Top in
    let discrBody =
        let bs =
          wildcards @ [(mlid, targ)]
          |> List.map (fun (x,t) -> {mlbinder_name=x;mlbinder_ty=t;mlbinder_attrs=[]}) in
        with_ty disc_ty <|
            MLE_Fun(bs,
                    with_ty ml_bool_ty <|
                        (MLE_Match(with_ty targ <| MLE_Name([], mlid),
                                    // Note: it is legal in OCaml to write [Foo _] for a constructor with zero arguments, so don't bother.
                                   [MLP_CTor(mlpath_of_lident g constrName, [MLP_Wild]),
                                    None,
                                    with_ty ml_bool_ty <| MLE_Const(MLC_Bool true);

                                    MLP_Wild,
                                    None,
                                    with_ty ml_bool_ty <| MLE_Const(MLC_Bool false)])))
    in
    let _, name = mlpath_of_lident env discName in
    MLM_Let (NonRec,
            [{ mllb_meta=[];
               mllb_attrs=[];
               mllb_name=name;
               mllb_tysc=None;
               mllb_add_unit=false;
               mllb_def=discrBody;
               print_typ=false}] ) |> mk_mlmodule1

let _ = register_pre_translate term_as_mlexpr'
let _ = register_pre_translate_typ translate_term_to_mlty'
