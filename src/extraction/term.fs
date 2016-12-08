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
open FStar
open FStar.Util
open FStar.Const
open FStar.Ident
open FStar.Extraction
open FStar.Extraction.ML
open FStar.Extraction.ML.Syntax
open FStar.Extraction.ML.UEnv
open FStar.Extraction.ML.Util
open FStar.Syntax.Syntax

module S  = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module U  = FStar.Syntax.Util
module TC = FStar.TypeChecker.Tc
module N  = FStar.TypeChecker.Normalize
module C  = FStar.Syntax.Const
module TcEnv = FStar.TypeChecker.Env
module TcTerm = FStar.TypeChecker.TcTerm

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
let erasableType g t = Util.erasableType (Util.udelta_unfold g) t
let eraseTypeDeep g t = Util.eraseTypeDeep (Util.udelta_unfold g) t

module Print = FStar.Syntax.Print


(* taramana 2016-10-31: we redefine
FStar.Extraction.ML.Util.record_fields here because the desugaring
of field names has changed, but we cannot change the definition in
FStar.Extraction.ML.Util for now because it is used by legacy
extraction, which is still used in the bootstrapping process *)

let record_fields fs vs = List.map2 (fun (f:ident) e -> f.idText, e) fs vs

(********************************************************************************************)
(* Some basic error reporting; all are fatal errors at this stage                           *)
(********************************************************************************************)
let fail r msg =
    Util.print_string <| format2 "%s: %s\n" (Range.string_of_range r) msg;
    failwith msg

let err_uninst env (t:term) (vars, ty) =
    fail t.pos (Util.format3 "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated"
                    (Print.term_to_string t)
                    (vars |> List.map fst |> String.concat ", ")
                    (ML.Code.string_of_mlty env.currentModule ty))

let err_ill_typed_application env (t : term) args (ty : mlty) =
    fail t.pos (Util.format3 "Ill-typed application: application is %s \n remaining args are %s\nml type of head is %s\n"
                (Print.term_to_string t)
                (args |> List.map (fun (x, _) -> Print.term_to_string x) |> String.concat " ")
                (ML.Code.string_of_mlty env.currentModule ty))


let err_value_restriction t =
    fail t.pos (Util.format2 "Refusing to generalize because of the value restriction: (%s) %s"
                    (Print.tag_of_term t) (Print.term_to_string t))

let err_unexpected_eff t f0 f1 =
    fail t.pos (Util.format3 "for expression %s, Expected effect %s; got effect %s" (Print.term_to_string t) (eff_to_string f0) (eff_to_string f1))

(********************************************************************)
(* Translating an effect lid to an e_tag = {E_PURE, E_GHOST, E_ANY} *)
(********************************************************************)
let effect_as_etag =
    let cache = Util.smap_create 20 in
    let rec delta_norm_eff g (l:lident) =
        match Util.smap_try_find cache l.str with
            | Some l -> l
            | None ->
                let res = match TypeChecker.Env.lookup_effect_abbrev g.tcenv [S.U_zero] l with
                | None -> l
                | Some (_, c) -> delta_norm_eff g (U.comp_effect_name c) in
                Util.smap_add cache l.str res;
                res in
    fun g l ->
        let l = delta_norm_eff g l in
        if lid_equals l C.effect_PURE_lid
        then E_PURE
        else if lid_equals l C.effect_GHOST_lid
        then E_GHOST
        else E_IMPURE
(********************************************************************************************)
(* Basic syntactic operations on a term                                                     *)
(********************************************************************************************)

(* Deciding which stratum a term belongs to, i.e., is it going to be an ML expression or type? *)
type level_t =
    | Term_level
    | Type_level
    | Kind_level

let predecessor t = function
    | Term_level -> Term_level
    | Type_level -> Term_level
    | Kind_level -> Type_level

//level t:
//     Determines the level of a term from its
//     syntactic structure and type annotations
let rec level env t =
    let predecessor l = predecessor t l in
    let t = SS.compress t in
    debug env (fun _ -> Util.print2 "level %s (%s)\n" (Print.term_to_string t) (Print.tag_of_term t));
//    printfn "%s\n" (Print.term_to_string t);
    match t.n with
    | Tm_delayed _ ->
        failwith (Util.format1 "Impossible: %s" (Print.tag_of_term t))

    | Tm_unknown -> //usually a placeholder for Type TODO: FIXME!
        Kind_level

    | Tm_constant _ ->
        Term_level

    | Tm_fvar ({fv_delta=Delta_defined_at_level _}) ->
      let t' = N.normalize [N.Beta; N.UnfoldUntil Delta_constant; N.EraseUniverses; N.AllowUnboundUniverses; N.Exclude N.Zeta; N.Exclude N.Iota] env.tcenv t in
      debug env (fun () -> Util.print2 "Normalized %s to %s\n" (Print.term_to_string t) (Print.term_to_string t'));
      level env t'

    | Tm_fvar fv ->
      if TypeChecker.Env.is_type_constructor env.tcenv fv.fv_name.v
      then Type_level
      else predecessor <| level env fv.fv_name.ty //lose precision

    | Tm_uvar (_, t)
    | Tm_bvar ({sort=t})
    | Tm_name ({sort=t}) -> //lose precision
        predecessor <| level env t

    | Tm_ascribed(t, _, _) ->
        level env t

    | Tm_type _ ->
        Kind_level

    | Tm_uinst(t, _) ->
        level env t

    | Tm_refine(x, _) ->
        begin match level env x.sort with
            | Term_level -> Type_level
            | l -> l
        end

    | Tm_arrow(bs, c) ->
        begin match level env (U.comp_result c) with
            | Term_level -> Type_level
            | l -> l
        end

    | Tm_abs(bs, body, _) ->
        level env body

    | Tm_let(_, body) ->
        level env body

    | Tm_match(_, branches) ->
        begin match branches with
        | (_, _, e)::_ -> level env e
        | _ -> failwith "Empty branches"
        end

    | Tm_meta(t, _) ->
        level env t

    | Tm_app(head, _) ->
        level env head

//is_type env t:
//   The main predicate to determine the stratum
let is_type env t = match level env t with
    | Term_level -> false
    | _ -> true

let is_type_binder env x =
    match level env (fst x).sort with
    | Term_level -> failwith "Impossible: Binder is a term"
    | Type_level -> false
    | Kind_level -> true

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
    | MLE_Tuple exps -> Util.for_all is_ml_value exps
    | MLE_Record (_, fields) -> Util.for_all (fun (_, e) -> is_ml_value e) fields
    | _ -> false

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

let unit_binder = S.mk_binder <| S.new_bv None TypeChecker.Common.t_unit

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

//erasable g f t:
//     Ghost terms are erasable
//     As are pure terms that return uninformative types, e.g., unit
let erasable (g:env) (f:e_tag) (t:mlty) =
    f = E_GHOST || (f = E_PURE && erasableType g t)

//erase g t f:
//     if t is an expression, replaces t with () if it is erasable
let erase (g:env) e ty (f:e_tag) : (mlexpr * e_tag * mlty) =
    let e = if erasable g f ty
            then if type_leq g ty ml_unit_ty then ml_unit
                else with_ty ty <| MLE_Coerce(ml_unit, ml_unit_ty, ty)
            else e in
    (e, f, ty)

//maybe_coerce g e ty expect:
//     Inserts an Obj.magic around e if ty </: expect
let maybe_coerce (g:env) e ty (expect:mlty) : mlexpr  =
    let ty = eraseTypeDeep g ty in
    match type_leq_c g (Some e) ty expect with
        | true, Some e' -> e'
        | _ ->
          debug g (fun () -> Util.print3 "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n"
                             (Code.string_of_mlexpr g.currentModule e)
                             (Code.string_of_mlty g.currentModule ty)
                             (Code.string_of_mlty g.currentModule expect));
          with_ty expect <| MLE_Coerce (e, ty, expect)

(********************************************************************************************)
(* The main extraction of terms to ML types                                                 *)
(********************************************************************************************)
let bv_as_mlty (g:env) (bv:bv) =
    match UEnv.lookup_bv g bv with
        | Inl (_, t) -> t
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
let rec term_as_mlty (g:env) (t0:term) : mlty =
    let rec is_top_ty t = match t with
        | MLTY_Top -> true
        | MLTY_Named _ ->
          begin match Util.udelta_unfold g t with
                | None -> false
                | Some t -> is_top_ty t
          end
        | _ -> false
    in
    let t = N.normalize [N.Beta; N.Eager_unfolding; N.Iota; N.Zeta; N.EraseUniverses; N.AllowUnboundUniverses] g.tcenv t0 in
    let mlt = term_as_mlty' g t in
    if is_top_ty mlt
    then //Try normalizing t fully, this time with Delta steps, and translate again, to see if we can get a better translation for it
         let t = N.normalize [N.Beta; N.Eager_unfolding; N.UnfoldUntil Delta_constant; N.Iota; N.Zeta; N.EraseUniverses; N.AllowUnboundUniverses] g.tcenv t0 in
         term_as_mlty' g t
    else mlt

and term_as_mlty' env t =
     let t = SS.compress t in
     match t.n with
      | Tm_bvar _
      | Tm_delayed _
      | Tm_unknown -> failwith (Util.format1 "Impossible: Unexpected term %s" (Print.term_to_string t))

      | Tm_constant _ -> unknownType

      | Tm_uvar _ -> unknownType //really shouldn't have any uvars left; TODO: fatal failure?

      | Tm_meta(t, _)
      | Tm_refine({sort=t}, _)
      | Tm_uinst(t, _)
      | Tm_ascribed(t, _, _) -> term_as_mlty' env t

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
            let eff = TcEnv.norm_eff_name env.tcenv (U.comp_effect_name c) in
            let ed = TcEnv.get_effect_decl env.tcenv eff in
            if ed.qualifiers |> List.contains Reifiable
            then let t = FStar.TypeChecker.Util.reify_comp env.tcenv (U.lcomp_of_comp c) U_unknown in
                 (* let _ = printfn "Translating comp type %s as %s\n" *)
                 (*        (Print.comp_to_string c) (Print.term_to_string t) in *)
                 let res = term_as_mlty' env t in
                 (* let _ = printfn "Translated comp type %s as %s ... to %s\n" *)
                 (*        (Print.comp_to_string c) (Print.term_to_string t) (ML.Code.string_of_mlty env.currentModule res) in *)
                 res
            else term_as_mlty' env (U.comp_result c) in
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
              term_as_mlty' env (S.mk (Tm_app(head, args'@args)) None t.pos)

            | _ -> unknownType in
        res

      | Tm_abs(bs,ty,_) ->  (* (sch) rule in \hat{\epsilon} *)
        (* We just translate the body in an extended environment; the binders will just end up as units *)
        let bs, ty = SS.open_term bs ty in
        let bts, env = binders_as_ml_binders env bs in
        term_as_mlty' env ty

      | Tm_type _
      | Tm_let _
      | Tm_match _ -> unknownType

and arg_as_mlty (g:env) (a, _) : mlty =
    if is_type g a
    then term_as_mlty' g a
    else erasedContent

and fv_app_as_mlty (g:env) (fv:fv) (args : args) : mlty =
    let formals, t = U.arrow_formals fv.fv_name.ty in
    let mlargs = List.map (arg_as_mlty g) args in
    let mlargs =
        let n_args = List.length args in
        if List.length formals > n_args //it's not fully applied; so apply the rest to unit
        then let _, rest = Util.first_N n_args formals in
             mlargs @ (List.map (fun _ -> erasedContent) rest)
        else mlargs in
    let nm = match maybe_mangle_type_projector g fv with 
             | Some p -> 
               p
             | None -> 
               mlpath_of_lident fv.fv_name.v in
    MLTY_Named (mlargs, nm)

and binders_as_ml_binders (g:env) (bs:binders) : list<(mlident * mlty)> * env =
    let ml_bs, env = bs |> List.fold_left (fun (ml_bs, env) b ->
            if is_type_binder g b
            then //no first-class polymorphism; so type-binders get wiped out
                    let b = fst b in
                    let env = extend_ty env b (Some MLTY_Top) in
                    let ml_b = (bv_as_ml_termvar b (*name of the binder*),
                                ml_unit_ty (*type of the binder. correspondingly, this argument gets converted to the unit value in application *)) in
                    ml_b::ml_bs, env
            else let b = fst b in
                    let t = term_as_mlty env b.sort in
                    let env = extend_bv env b ([], t) false false false in
                    let ml_b = (bv_as_ml_termvar b, t) in
                    ml_b::ml_bs, env)
    ([], g) in
    List.rev ml_bs,
    env

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
       | (NonRec, quals, [lb]) when not top_level ->
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
      begin match is_xtuple d with
        | Some n -> MLP_Tuple(pats)
        | _ ->
          match q with
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
let extract_pat (g:env) p (expected_t:mlty) : (env * list<(mlpattern * option<mlexpr>)> * bool) =
    let rec extract_one_pat (disjunctive_pat : bool) (imp : bool) g p expected_topt : env * option<(mlpattern * list<mlexpr>)> * bool =
        let ok t =
            match expected_topt with
            | None -> true
            | Some t' ->
              let ok = type_leq g t t' in
              if not ok then debug g (fun _ -> Util.print2 "Expected pattern type %s; got pattern type %s\n"
                                                    (Code.string_of_mlty g.currentModule t')
                                                    (Code.string_of_mlty g.currentModule t));
              ok
        in
        match p.v with
          | Pat_disj _ -> failwith "Impossible: Nested disjunctive pattern"

          | Pat_constant (Const_int (c, None))  ->
            // note: as-patterns are not valid F* and "let Pat_constant i = p.v"
            // is not valid F# ?!!
            let i = Const_int (c, None) in
            //these may be extracted to bigint, in which case, we need to emit a when clause
            let x = gensym() in // as_mlident (S.new_bv None Tm_bvar) in
            let when_clause = with_ty ml_bool_ty <|
              MLE_App(prims_op_equality, [with_ty ml_int_ty <| MLE_Var x;
                                        with_ty ml_int_ty <| (MLE_Const <| mlconst_of_const' p.p i)]) in
            g, Some (MLP_Var x, [when_clause]), ok ml_int_ty

          | Pat_constant s     ->
            let t : term = TcTerm.tc_constant Range.dummyRange s in
            let mlty = term_as_mlty g t in
            g, Some (MLP_Const (mlconst_of_const' p.p s), []), ok mlty

          | Pat_var x ->
            let mlty = term_as_mlty g x.sort in
            let g = extend_bv g x ([], mlty) false false imp in
            g, (if imp then None else Some (MLP_Var (bv_as_mlident x), [])), ok mlty

          | Pat_wild x when disjunctive_pat ->
            g, Some (MLP_Wild, []), true

          | Pat_wild x -> (*how is this different from Pat_var? For extTest.naryTree.Node, the first projector uses Pat_var and the other one uses Pat_wild*)
            let mlty = term_as_mlty g x.sort in
            let g = UEnv.extend_bv g x ([], mlty) false false imp in
            g, (if imp then None else Some (MLP_Var (bv_as_mlident x), [])), ok mlty

          | Pat_dot_term _ ->
            g, None, true

          | Pat_cons (f, pats) ->
            let d, tys = match lookup_fv g f with
                | Inr({expr=MLE_Name n}, ttys, _) -> n, ttys
                | _ -> failwith "Expected a constructor" in
            let nTyVars = List.length (fst tys) in
            let tysVarPats, restPats =  Util.first_N nTyVars pats in
            let f_ty_opt =
                    try
                        let mlty_args = tysVarPats |> List.map (fun (p, _) ->
                            match p.v with
                            | Pat_dot_term (_, t) -> term_as_mlty g t
                            | _ ->
                              debug g (fun _ -> Util.print1 "Pattern %s is not extractable" (Print.pat_to_string p));
                              raise Un_extractable) in
                        let f_ty = subst tys mlty_args in
                        Some (Util.uncurry_mlty_fun f_ty)
                    with Un_extractable -> None in

            let g, tyMLPats = Util.fold_map (fun g (p, imp) ->
                let g, p, _ = extract_one_pat disjunctive_pat true g p None in
                g, p) g tysVarPats in (*not all of these were type vars in ML*)

            let (g, f_ty_opt), restMLPats = Util.fold_map (fun (g, f_ty_opt) (p, imp) ->
                let f_ty_opt, expected_ty = match f_ty_opt with
                    | Some (hd::rest, res) -> Some (rest, res), Some hd
                    | _ -> None, None in
                let g, p, _ = extract_one_pat disjunctive_pat false g p expected_ty in
                (g, f_ty_opt), p) (g, f_ty_opt) restPats in

            let mlPats, when_clauses = List.append tyMLPats restMLPats |> List.collect (function (Some x) -> [x] | _ -> []) |> List.split in
            let pat_ty_compat = match f_ty_opt with
                | Some ([], t) -> ok t
                | _ -> false in
            g, Some (resugar_pat f.fv_qual (MLP_CTor (d, mlPats)), when_clauses |> List.flatten), pat_ty_compat in


    let extract_one_pat disj g p expected_t =
        match extract_one_pat disj false g p expected_t with
            | g, Some (x, v), b -> g, (x, v), b
            | _ -> failwith "Impossible: Unable to translate pattern" in

    let mk_when_clause whens =
        match whens with
            | [] -> None
            | hd::tl -> Some (List.fold_left conjoin hd tl) in

    match p.v with
      | Pat_disj [] -> failwith "Impossible: Empty disjunctive pattern"

      | Pat_disj (p::pats)      ->
        let g, p, b = extract_one_pat true g p (Some expected_t) in
        let b, ps = Util.fold_map (fun b p ->
                    let _, p, b' = extract_one_pat true g p (Some expected_t) in
                    b && b', p) b pats in
        let ps = p :: ps in
        let ps_when, rest = ps |> List.partition (function (_, _::_) -> true | _ -> false) in
        let ps = ps_when |> List.map (fun (x, whens) -> (x, mk_when_clause whens)) in
        //branches that contains a new when clause need to be split out
        let res = match rest with
            | [] -> g, ps, b
            | rest -> g,  (MLP_Branch(List.map fst rest), None) :: ps, b in
        res

      | _ ->
        let g, (p, whens), b = extract_one_pat false g p (Some expected_t) in
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
let maybe_eta_data_and_project_record (g:env) (qual : option<fv_qual>) (residualType : mlty)  (mlAppExpr : mlexpr) : mlexpr =
    let rec eta_args more_args t = match t with
        | MLTY_Fun (t0, _, t1) ->
          let x = gensym () in
          eta_args (((x, t0), with_ty t0 <| MLE_Var x)::more_args) t1
        | MLTY_Named (_, _) -> List.rev more_args, t
        | _ -> failwith "Impossible: Head type is not an arrow" in

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

        | MLE_App({expr=MLE_Name mlp}, mle::args), Some (Record_projector (constrname, f)) ->
          let f = lid_of_ids (constrname.ns @ [f]) in
          let fn = Util.mlpath_of_lid f in
          let proj = MLE_Proj(mle, fn) in
          let e = match args with
            | [] -> proj
            | _ -> MLE_App(with_ty MLTY_Top <| proj, args) in //TODO: Fix imprecise with_ty on the projector
          with_ty mlAppExpr.mlty e

        | MLE_App ({expr=MLE_Name mlp}, mlargs), Some Data_ctor
        | MLE_App ({expr=MLE_Name mlp}, mlargs), Some (Record_ctor _) ->
          resugar_and_maybe_eta qual <| (with_ty mlAppExpr.mlty <| MLE_CTor (mlp,mlargs))

        | MLE_Name mlp, Some Data_ctor
        | MLE_Name mlp, Some (Record_ctor _) ->
          resugar_and_maybe_eta qual <| (with_ty mlAppExpr.mlty <| MLE_CTor (mlp, []))

        | _ -> mlAppExpr

let maybe_downgrade_eff g f t =
    if f = E_GHOST
    && type_leq g t ml_unit_ty
    then E_PURE
    else f

//The main extraction function
let rec term_as_mlexpr (g:env) (t:term) : (mlexpr * e_tag * mlty) =
    let e, tag, ty = term_as_mlexpr' g t in
    let tag = maybe_downgrade_eff g tag ty in
    (debug g (fun u -> Util.print_string (Util.format4 "term_as_mlexpr (%s) :  %s has ML type %s and effect %s\n"
        (Print.tag_of_term t)
        (Print.term_to_string t)
        (Code.string_of_mlty g.currentModule ty)
        (Util.eff_to_string tag))));
    erase g e ty tag

and check_term_as_mlexpr (g:env) (t:term) (f:e_tag) (ty:mlty) :  (mlexpr * mlty) =
    // debug g (fun () -> printfn "Checking %s at type %A\n" (Print.exp_to_string e) t);
    let e, t = check_term_as_mlexpr' g t f ty in
    let r, _, t = erase g e t f in
    r, t

and check_term_as_mlexpr' (g:env) (e0:term) (f:e_tag) (ty:mlty) : (mlexpr * mlty) =
    let e, tag, t = term_as_mlexpr g e0 in
    let tag = maybe_downgrade_eff g tag t in
    if eff_leq tag f
    then maybe_coerce g e t ty, ty
    else err_unexpected_eff e0 f tag

and term_as_mlexpr' (g:env) (top:term) : (mlexpr * e_tag * mlty) =
    (debug g (fun u -> Util.print_string (Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n"
        (Range.string_of_range top.pos)
        (Print.tag_of_term top)
        (Print.term_to_string top))));
    let t = SS.compress top in
    match t.n with
        | Tm_unknown
        | Tm_delayed _
        | Tm_uvar _
        | Tm_bvar _ -> failwith (Util.format1 "Impossible: Unexpected term: %s" (Print.tag_of_term t))

        | Tm_type _
        | Tm_refine _
        | Tm_arrow _ ->
          ml_unit, E_PURE, ml_unit_ty

        | Tm_meta (t, Meta_desugared Mutable_alloc) ->
            // the lack of as-patterns makes this a little bit heavy
            begin match term_as_mlexpr' g t with
            | { expr = MLE_Let ((NonRec, flags, bodies), continuation);
                mlty = mlty;
                loc = loc
              }, tag, typ ->
                {
                  expr = MLE_Let ((NonRec, Mutable :: flags, bodies), continuation);
                  mlty = mlty;
                  loc = loc
                }, tag, typ
            | _ ->
                failwith "impossible"
            end

        | Tm_meta(t, Meta_monadic (m, _)) ->
          let t = SS.compress t in
          begin match t.n with
            | Tm_let((false, [lb]), body) when (Util.is_left lb.lbname) ->
              let ed = TypeChecker.Env.get_effect_decl g.tcenv m in
              if ed.qualifiers |> List.contains Reifiable |> not
              then term_as_mlexpr' g t
              else //this should be interpreted as a bind
                   let ml_result_ty_1 = term_as_mlty g lb.lbtyp in
                   let comp_1, _, _ = term_as_mlexpr g lb.lbdef in
                   let ml_k, ty =
                        let k = U.abs [left (lb.lbname) |> S.mk_binder] body None in
                        let ml_k, _, t_k = term_as_mlexpr g k in
                        let m_2 = match t_k with
                            | MLTY_Fun(_, _, m_2) -> m_2
                            | _ -> failwith "Impossible" in
                        ml_k, m_2 in
                   let bind = with_ty MLTY_Top <| MLE_Name (monad_op_name ed "bind" |> fst) in
                   with_ty ty <| MLE_App(bind, [comp_1; ml_k]), E_IMPURE, ty
            | _ -> term_as_mlexpr' g t
         end



        | Tm_meta(t, _) //TODO: handle the resugaring in case it's a 'Meta_desugared' ... for more readable output
        | Tm_uinst(t, _) ->
          term_as_mlexpr' g t

        | Tm_constant c ->
          let _, ty, _ = TcTerm.type_of_tot_term g.tcenv t in
          let ml_ty = term_as_mlty g ty in
          with_ty ml_ty (MLE_Const <| mlconst_of_const' t.pos c), E_PURE, ml_ty

        | Tm_name _
        | Tm_fvar _ -> //lookup in g; decide if its in left or right; tag is Pure because it's just a variable
          if is_type g t
          then ml_unit, E_PURE, ml_unit_ty //Erase type argument
          else begin match lookup_term g t with
                | Inl _, _ ->
                  ml_unit, E_PURE, ml_unit_ty

                | Inr (x, mltys, _), qual ->
                  //let _ = printfn "\n (*looked up tyscheme of \n %A \n as \n %A *) \n" x s in
                  begin match mltys with
                    | ([], t) when (t=ml_unit_ty) -> ml_unit, E_PURE, t //optimize (x:unit) to ()
                    | ([], t) -> maybe_eta_data_and_project_record g qual t x, E_PURE, t
                    | _ -> err_uninst g t mltys
                  end
               end

        | Tm_abs(bs, body, copt(* the annotated computation type of the body ... probably don't need it *)) ->
          let bs, body = SS.open_term bs body in
          let ml_bs, env = binders_as_ml_binders g bs in
          let ml_body, f, t = term_as_mlexpr env body in
          let f, tfun = List.fold_right
            (fun (_, targ) (f, t) -> E_PURE, MLTY_Fun (targ, f, t))
            ml_bs (f, t) in
          with_ty tfun <| MLE_Fun(ml_bs, ml_body), f, tfun

        | Tm_app({n=Tm_constant Const_reify}, [t]) ->
          let ml, e_tag, mlty = term_as_mlexpr' g (fst t) in
          ml, E_PURE, mlty

        | Tm_app({n=Tm_constant (Const_reflect _)}, [t]) ->
          let ml, e_tag, mlty = term_as_mlexpr' g (fst t) in
          ml, E_IMPURE, mlty

        | Tm_app(head, args) ->
          let is_total = function
            | Inl l -> FStar.Syntax.Util.is_total_lcomp l
            | Inr (l, flags) -> Ident.lid_equals l FStar.Syntax.Const.effect_Tot_lid
                             || flags |> List.existsb (function TOTAL -> true | _ -> false)
          in
          begin match head.n, (SS.compress head).n with
            | Tm_uvar _, _ -> //This should be a resolved uvar --- so reduce it before extraction
              let t = N.normalize [N.Beta; N.Iota; N.Zeta; N.EraseUniverses; N.AllowUnboundUniverses] g.tcenv t in
              term_as_mlexpr' g t

            | _, Tm_abs(bs, _, Some lc) when is_total lc -> //this is a beta_redex --- also reduce it before extraction
              let t = N.normalize [N.Beta; N.Iota; N.Zeta; N.EraseUniverses; N.AllowUnboundUniverses] g.tcenv t in
              term_as_mlexpr' g t

            | _ ->

              let rec extract_app is_data (mlhead, mlargs_f) (f(*:e_tag*), t (* the type of (mlhead mlargs) *)) restArgs =
    //            Printf.printf "synth_app restArgs=%d, t=%A\n" (List.length restArgs) t;
                match restArgs, t with
                    | [], _ ->
                        //1. If partially applied and head is a datacon, it needs to be eta-expanded
                        //2. If we're generating OCaml, and any of the arguments are impure,
                        //   and the head is not a primitive short-circuiting op,
                        //   then evaluation order must be enforced to be L-to-R (by hoisting)
                        let evaluation_order_guaranteed =
                          List.length mlargs_f = 1 ||
                          Util.codegen_fsharp () ||
                          (match head.n with
                           | Tm_fvar { fv_name = { v = v } } ->
                             v = Syntax.Const.op_And || v = Syntax.Const.op_Or
                           | _ ->
                              false)
                        in
                        let lbs, mlargs =
                            if evaluation_order_guaranteed
                            then [], List.rev mlargs_f |> List.map fst
                            else List.fold_left (fun (lbs, out_args) (arg, f) ->
                                    if f=E_PURE || f=E_GHOST
                                    then (lbs, arg::out_args)
                                    else let x = gensym () in
                                         (x, arg)::lbs, (with_ty arg.mlty <| MLE_Var x)::out_args)
                            ([], []) mlargs_f in
                        let app = maybe_eta_data_and_project_record g is_data t <| (with_ty t <| MLE_App(mlhead, mlargs)) in
                        let l_app = List.fold_right
                            (fun (x, arg) out ->
                              with_ty out.mlty <| mk_MLE_Let false (NonRec, [], [{mllb_name=x; mllb_tysc=Some ([], arg.mlty); mllb_add_unit=false; mllb_def=arg; print_typ=true}]) out)
                            lbs app in // lets are to ensure L to R eval ordering of arguments
                        l_app, f, t

                    | (arg, _)::rest, MLTY_Fun (formal_t, f', t) when is_type g arg -> //non-prefix type app; this type argument gets erased to unit
                      if type_leq g formal_t ml_unit_ty
                      then extract_app is_data (mlhead, (ml_unit, E_PURE)::mlargs_f) (join arg.pos f f', t) rest
                      else failwith (Util.format4 "Impossible: ill-typed application:\n\thead=%s, arg=%s, tag=%s\n\texpected type unit, got %s" //ill-typed; should be impossible
                                            (Code.string_of_mlexpr g.currentModule mlhead)
                                            (Print.term_to_string arg)
                                            (Print.tag_of_term arg)
                                            (Code.string_of_mlty g.currentModule formal_t))

                    | (e0, _)::rest, MLTY_Fun(tExpected, f', t) ->
                      let r = e0.pos in
                      let e0, f0, tInferred = term_as_mlexpr g e0 in
                      let e0 = maybe_coerce g e0 tInferred tExpected in // coerce the arguments of application, if they dont match up
                      extract_app is_data (mlhead, (e0, f0)::mlargs_f) (join_l r [f;f';f0], t) rest

                    | _ ->
                      begin match Util.udelta_unfold g t with
                        | Some t -> extract_app is_data (mlhead, mlargs_f) (f, t) restArgs
                        | None -> err_ill_typed_application g top restArgs t
                      end in

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


              if is_type g t
              then ml_unit, E_PURE, ml_unit_ty //Erase type argument: TODO: FIXME, this could be effectful
              else let head = U.un_uinst head in
                   begin match head.n with
                    | Tm_bvar _
                    | Tm_fvar _ ->
                       //             debug g (fun () -> printfn "head of app is %s\n" (Print.exp_to_string head));
                      let (head_ml, (vars, t), inst_ok), qual = match lookup_term g head with | Inr (u), q -> u, q | _ -> failwith "FIXME Ty" in
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
                          then let prefix, rest = Util.first_N n args in
        //                       let _ = (if n=1 then printfn "\n (*prefix was  \n %A \n  *) \n" prefix) in
                               let prefixAsMLTypes = List.map (fun (x, _) -> term_as_mlty g x) prefix in
        //                        let _ = printfn "\n (*about to instantiate  \n %A \n with \n %A \n \n *) \n" (vars,t) prefixAsMLTypes in
                               let t = instantiate (vars, t) prefixAsMLTypes in
                               let head = match head_ml.expr with
                                 | MLE_Name _
                                 | MLE_Var _ -> {head_ml with mlty=t}
                                 | MLE_App(head, [{expr=MLE_Const MLC_Unit}]) -> MLE_App({head with mlty=MLTY_Fun(ml_unit_ty, E_PURE, t)}, [ml_unit]) |> with_ty t
                                 | _ -> failwith "Impossible: Unexpected head term" in
                               head, t, rest
                          else err_uninst g head (vars, t) in
                        //debug g (fun () -> printfn "\n (*instantiating  \n %A \n with \n %A \n produced \n %A \n *) \n" (vars,t0) prefixAsMLTypes t);
                       begin match args with
                            | [] -> maybe_eta_data_and_project_record g qual head_t head_ml, E_PURE, head_t
                            | _  -> extract_app_maybe_projector qual head_ml (E_PURE, head_t) args
                       end

                    | _ ->
                      let head, f, t = term_as_mlexpr g head in // t is the type inferred for head, the head of the app
                      extract_app_maybe_projector None head (f, t) args
                 end
            end

        | Tm_ascribed(e0, tc, f) ->
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
                    let tcenv = TcEnv.set_current_module g.tcenv
                                (Ident.lid_of_path ((fst g.currentModule) @ [snd g.currentModule]) Range.dummyRange) in
                    let lbdef = N.normalize [N.AllowUnboundUniverses; N.EraseUniverses;
                                             N.Inlining; N.Eager_unfolding;
                                             N.Exclude N.Zeta; N.PureSubtermsWithinComputations; N.Primops]
                                tcenv lb.lbdef in
                    {lb with lbdef=lbdef})
            else lbs in
            //          let _ = printfn "\n (* let \n %s \n in \n %s *) \n" (Print.lbs_to_string (is_rec, lbs)) (Print.exp_to_string e') in
          let maybe_generalize {lbname=lbname_; lbeff=lbeff; lbtyp=t; lbdef=e}
            : lbname //just lbname returned back
            * e_tag  //the ML version of the effect label lbeff
            * (typ   //just the source type lbtyp=t, after compression
               * (S.binders //the erased type binders
                  * mltyscheme)) //translation of the source type t as a ML type scheme
            * bool   //whether or not to add a unit argument
            * term   //the term e, maybe after some type binders have been erased
            =
              let f_e = effect_as_etag g lbeff in
              let t = SS.compress t in
            //              debug g (fun () -> printfn "Let %s at type %s; expected effect is %A\n" (Print.lbname_to_string lbname) (Print.typ_to_string t) f_e);
              match t.n with
                | Tm_arrow(bs, c) when (List.hd bs |> is_type_binder g) ->
                   let bs, c = SS.open_comp bs c in
                  //need to generalize, but will erase all the type abstractions;
                  //If, after erasure, what remains is not a value, then add an extra unit arg. to preserve order of evaluation/generativity
                  //and to circumvent the value restriction

                  //TODO: ERASE ONLY THOSE THAT ABSTRACT OVER PURE FUNCTIONS in Type(i),
                  //      NOT, e.g., (x:int -> St Type)
                   let tbinders, tbody =
                        match Util.prefix_until (fun x -> not (is_type_binder g x)) bs with
                            | None -> bs, U.comp_result c
                            | Some (bs, b, rest) -> bs, U.arrow (b::rest) c in

                   let n_tbinders = List.length tbinders in
                   let e = normalize_abs e in
                   begin match e.n with
                      | Tm_abs(bs, body, _) ->
                        let bs, body = SS.open_term bs body in
                        if n_tbinders <= List.length bs
                        then let targs, rest_args = Util.first_N n_tbinders bs in
//                             printfn "tbinders are %s\n" (tbinders |> (Print.binders_to_string ", "));
//                             printfn "tbody is %s\n" (Print.typ_to_string tbody);
//                             printfn "targs are %s\n" (targs |> Print.binders_to_string ", ");
                             let expected_source_ty =
                                let s = List.map2 (fun (x, _) (y, _) -> S.NT(x, S.bv_to_name y)) tbinders targs in
                                SS.subst s tbody in
//                             printfn "After subst: expected_t is %s\n" (Print.typ_to_string expected_t);
                             let env = List.fold_left (fun env (a, _) -> UEnv.extend_ty env a None) g targs in
                             let expected_t = term_as_mlty env expected_source_ty in
                             (* debug g (fun () -> printfn "+++LB=%s ... Translated source type %s to mlty %s" *)
                             (*                (Print.lbname_to_string lbname) *)
                             (*                (Print.term_to_string expected_source_ty) *)
                             (*                (ML.Code.string_of_mlty g.currentModule expected_t)); *)
                             let polytype = targs |> List.map (fun (x, _) -> bv_as_ml_tyvar x), expected_t in
                             let add_unit = match rest_args with
                                | [] -> not (is_fstar_value body) //if it's a pure type app, then it will be extracted to a value in ML; so don't add a unit
                                | _ -> false in
                             let rest_args = if add_unit then (unit_binder::rest_args) else rest_args in
                             let body = match rest_args with
                                | [] -> body
                                | _ -> U.abs rest_args body None in
                             (lbname_, f_e, (t, (targs, polytype)), add_unit, body)

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
                       let e = mk (Tm_app(e, args)) None e.pos in
                       (lbname_, f_e, (t, (tbinders, polytype)), false, e)

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
                        err_value_restriction e
                   end

                | _ ->  (* no generalizations; TODO: normalize and retry? *)
                  let expected_t = term_as_mlty g t in
                  (* debug g (fun () -> printfn "+++LB=%s ... Translated source type %s to mlty %s" *)
                  (*                       (Print.lbname_to_string lbname) *)
                  (*                       (Print.term_to_string t) *)
                  (*                       (ML.Code.string_of_mlty g.currentModule expected_t)); *)
                  (lbname_, f_e, (t, ([], ([],expected_t))), false, e) in

          let check_lb env (nm, (lbname, f, (t, (targs, polytype)), add_unit, e)) =
              let env = List.fold_left (fun env (a, _) -> UEnv.extend_ty env a None) env targs in
              let expected_t = if add_unit then MLTY_Fun(ml_unit_ty, E_PURE, snd polytype) else snd polytype in
              let e, _ = check_term_as_mlexpr env e f expected_t in
              let f = maybe_downgrade_eff env f expected_t in
              f, {mllb_name=nm; mllb_tysc=Some polytype; mllb_add_unit=add_unit; mllb_def=e; print_typ=true} in

         (*after the above definitions, here is the main code for extracting let expressions*)
          let lbs = lbs |> List.map maybe_generalize in

          let env_body, lbs = List.fold_right (fun lb (env, lbs) ->
              let (lbname, _, (t, (_, polytype)), add_unit, _) = lb in
              let env, nm = UEnv.extend_lb env lbname t polytype add_unit true in
              env, (nm,lb)::lbs) lbs (g, []) in

          let env_def = if is_rec then env_body else g in

          let lbs = lbs |> List.map (check_lb env_def)  in

          let e'_rng = e'.pos in

          let e', f', t' = term_as_mlexpr env_body e' in

          let f = join_l e'_rng (f'::List.map fst lbs) in

          let is_rec = if is_rec = true then Rec else NonRec in

          with_ty_loc t' (mk_MLE_Let top_level (is_rec, [], List.map snd lbs) e') (Util.mlloc_of_range t.pos), f, t'

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
            let pat_t_compat, mlbranches = pats |> Util.fold_map (fun compat br ->
                let pat, when_opt, branch = SS.open_branch br in
                let env, p, pat_t_compat = extract_pat g pat t_e in
                let when_opt, f_when = match when_opt with
                    | None -> None, E_PURE
                    | Some w ->
                        let w, f_w, t_w = term_as_mlexpr env w in
                        let w = maybe_coerce env w t_w ml_bool_ty in
                        Some w, f_w in
                let mlbranch, f_branch, t_branch = term_as_mlexpr env branch in
                //Printf.printf "Extracted %s to %A\n" (Print.exp_to_string branch) mlbranch;
                compat&&pat_t_compat,
                p |> List.map (fun (p, wopt) ->
                    let when_clause = conjoin_opt wopt when_opt in
                    p, (when_clause, f_when), (mlbranch, f_branch, t_branch)))
                true in
             let mlbranches = List.flatten mlbranches in
             //if the type of the pattern isn't compatible with the type of the scrutinee
             //    insert a magic around the scrutinee
             let e = if pat_t_compat
                     then e
                     else (debug g (fun _ -> Util.print2 "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                                (Code.string_of_mlexpr g.currentModule e)
                                                (Code.string_of_mlty g.currentModule t_e));
                           with_ty t_e <| MLE_Coerce (e, t_e, MLTY_Top)) in
             begin match mlbranches with
                | [] ->
                    let fw, _, _ = Util.right <| UEnv.lookup_fv g (S.lid_as_fv FStar.Syntax.Const.failwith_lid Delta_constant None) in
                    with_ty ml_unit_ty <| MLE_App(fw, [with_ty ml_string_ty <| MLE_Const (MLC_String "unreachable")]),
                    E_PURE,
                    ml_unit_ty


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


(*copied from ocaml-asttrans.fs*)
let fresh = let c = mk_ref 0 in
            fun x -> (incr c; (x, !c))

let ind_discriminator_body env (discName:lident) (constrName:lident) : mlmodule1 =
    // First, lookup the original (F*) type to figure out how many implicit arguments there are.
    let _, fstar_disc_type = TypeChecker.Env.lookup_lid env.tcenv discName in
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
                        (MLE_Match(with_ty targ <| MLE_Name([], idsym mlid),
                                    // Note: it is legal in OCaml to write [Foo _] for a constructor with zero arguments, so don't bother.
                                   [MLP_CTor(mlpath_of_lident constrName, [MLP_Wild]), None, with_ty ml_bool_ty <| MLE_Const(MLC_Bool true);
                                    MLP_Wild, None, with_ty ml_bool_ty <| MLE_Const(MLC_Bool false)]))) in
    MLM_Let (NonRec,[], [{mllb_name=convIdent discName.ident; mllb_tysc=None; mllb_add_unit=false; mllb_def=discrBody; print_typ=false}] )
