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
open FStar.Syntax.Syntax
open FStar.Extraction
open FStar.Extraction.ML
open FStar.Extraction.ML.Syntax
open FStar.Extraction.ML.UEnv
open FStar.Extraction.ML.Util

module S  = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module U  = FStar.Syntax.Util
module TC = FStar.TypeChecker.Tc

let type_leq g t1 t2 = Util.type_leq (Util.udelta_unfold g) t1 t2
let type_leq_c g t1 t2 = Util.type_leq_c (Util.udelta_unfold g) t1 t2
let erasableType g t = Util.erasableType (Util.udelta_unfold g) t
let eraseTypeDeep g t = Util.eraseTypeDeep (Util.udelta_unfold g) t

module Print = FStar.Syntax.Print   

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

let err_ill_typed_application (t : term) args (ty : mlty) =
    fail t.pos (Util.format2 "Ill-typed application: application is %s \n remaining args are %s\n"
                (Print.term_to_string t)
                (args |> List.map (fun (x, _) -> Print.term_to_string x) |> String.concat " "))


let err_value_restriction t =
    fail t.pos ("Refusing to generalize because of the value restriction")

let err_unexpected_eff t f0 f1 =
    fail t.pos (Util.format3 "for expression %s, Expected effect %s; got effect %s" (Print.term_to_string t) (eff_to_string f0) (eff_to_string f1))

(********************************************************************************************)
(* Basic syntactic opeartions on a term                                                     *)
(********************************************************************************************)

(* Deciding which stratum a term belongs to, i.e., is it to be an ML expression or type? *)
type univ = 
    | Term
    | UZero
    | UPlus

let predecessor = function
    | Term -> failwith "Impossible"
    | UZero -> Term
    | UPlus -> UZero

//univ t:
//     Determines the level of a term from its
//     syntactic structure and type annotations   
let rec univ t = match (SS.compress t).n with 
    | Tm_delayed _
    | Tm_unknown -> 
        failwith "Impossible"

    | Tm_constant _ -> 
        Term

    | Tm_bvar x 
    | Tm_name x ->
        predecessor <| univ x.sort 

    | Tm_fvar fv -> 
        predecessor <| univ fv.fv_name.ty

    | Tm_ascribed(_, t, _) -> 
        predecessor <| univ t

    | Tm_type _ -> 
        UPlus

    | Tm_uvar (_, t) -> 
        predecessor <| univ t
           
    | Tm_uinst(t, _) -> 
        univ t

    | Tm_refine(x, _) -> 
        predecessor <| univ t

    | Tm_arrow(bs, c) -> 
        univ (U.comp_result c)

    | Tm_abs(_, _, Some c) -> 
        predecessor <| univ c.res_typ
       
    | Tm_abs(bs, body, None) -> 
        univ body

    | Tm_let(_, body) -> 
        univ body

    | Tm_match(_, branches) -> 
        begin match branches with 
        | (_, _, e)::_ -> univ e
        | _ -> failwith "Empty branches"
        end

    | Tm_meta(t, _) -> 
        univ t

    | Tm_app(head, _) -> 
        univ head

//is_type t:
//   The main predicate to determine the stratum
let is_type t = match univ t with 
    | Term -> false
    | _ -> true

let is_type_binder x = 
    match univ (fst x).sort with 
    | Term -> failwith "Impossible"
    | UZero -> false
    | UPlus -> true

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
            | _ -> def


(*INVARIANT: we MUST always perform deep erasure after extraction of types, even when done indirectly e.g. translate_typ_of_arg below.
  Otherwise, there will be Ob.magic because the types get erased at some places and not at other places *)
//let translate_typ (g:env) (t:typ) : mlty = eraseTypeDeep g (TypeExtraction.ext g t)
//let translate_typ_of_arg (g:env) (a:arg) : mlty = eraseTypeDeep g (TypeExtraction.getTypeFromArg g a)
// erasing here is better because if we need to generate OCaml types for binders and return values, they will be accurate. By the time we reach maybe_coerce, we cant change those


(********************************************************************************************)
(* Operations on ml terms, types, and effect tags                                           *)
(*     1. Instantiation of type schemes                                                     *)
(*     2. Erasure of terms                                                                  *)
(*     3. Coercion (Obj.magic)                                                              *) 
(********************************************************************************************)
let translate_typ (g:env) (t:term) : mlty = failwith ""

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
        | _ -> with_ty expect <| MLE_Coerce (e, ty, expect)
//         debug g (fun () -> printfn "\n (*needed to coerce expression \n %A \n of type \n %A \n to type \n %A *) \n" e tInferred tExpected);
      
//////////////////////////////////////////////////////////////////////////////////////////////
(********************************************************************************************)
(* The main extraction of terms to ML expressions                                           *)
(********************************************************************************************)
//////////////////////////////////////////////////////////////////////////////////////////////
      
//extract_pat g p
//     Translates an F* pattern to an ML pattern
//     The main work is erasing inaccessible (dot) patterns
//     And turning F*'s curried pattern style to ML's fully applied ones                
let extract_pat (g:env) p : (env * list<(mlpattern * option<mlexpr>)>) =
    let rec extract_one_pat (disjunctive_pat : bool) (imp : bool) g p : env * option<(mlpattern * list<mlexpr>)> = 
        match p.v with
          | Pat_disj _ -> failwith "Impossible"
 
          | Pat_constant (Const_int c) when (not !Options.use_native_int) -> 
            //these may be extracted to bigint, in which case, we need to emit a when clause
            let x = gensym() in // as_mlident (S.new_bv None Tm_bvar) in
            let when_clause = with_ty ml_bool_ty <| MLE_App(prims_op_equality, [with_ty ml_int_ty <| MLE_Var x; 
                                                            with_ty ml_int_ty <| (MLE_Const <| mlconst_of_const' p.p (Const_int c))]) in
            g, Some (MLP_Var x, [when_clause])
            
          | Pat_constant s     ->
            g, Some (MLP_Const (mlconst_of_const' p.p s), [])

          | Pat_cons (f, pats) ->
            let d, tys = match lookup_fv g f with
                | Inr({expr=MLE_Name n}, ttys, _) -> n, ttys
                | _ -> failwith "Expected a constructor" in
            let nTyVars = List.length (fst tys) in
            let tysVarPats, restPats =  Util.first_N nTyVars pats in
            let g, tyMLPats = Util.fold_map (fun g (p, imp) -> extract_one_pat disjunctive_pat true g p) g tysVarPats in (*not all of these were type vars in ML*)
            let g, restMLPats = Util.fold_map (fun g (p, imp) -> extract_one_pat disjunctive_pat false g p) g restPats in
            let mlPats, when_clauses = List.append tyMLPats restMLPats |> List.collect (function (Some x) -> [x] | _ -> []) |> List.split in
            g, Some (Util.resugar_pat None (MLP_CTor (d, mlPats)), when_clauses |> List.flatten)

          | Pat_var x ->
            let mlty = translate_typ g x.sort in
            let g = extend_bv g x ([], mlty) false false imp in
            g, (if imp then None else Some (MLP_Var (x.ppname.idText,0), []))

          | Pat_wild x when disjunctive_pat ->
            g, Some (MLP_Wild, [])

          | Pat_wild x -> (*how is this different from Pat_var? For extTest.naryTree.Node, the first projector uses Pat_var and the other one uses Pat_wild*)
            let mlty = translate_typ g x.sort in
            let g = UEnv.extend_bv g x ([], mlty) false false imp in
            g, (if imp then None else Some (MLP_Var (x.ppname.idText, 0), []))

          | Pat_dot_term _ ->
            g, None in

    let extract_one_pat disj g p = 
        match extract_one_pat disj false g p with 
            | g, Some (x, v) -> g, (x, v)
            | _ -> failwith "Impossible" in 
    
    let mk_when_clause whens = 
        match whens with 
            | [] -> None
            | hd::tl -> Some (List.fold_left conjoin hd tl) in
    
    match p.v with
      | Pat_disj [] -> failwith "Impossible"

      | Pat_disj (p::pats)      ->
        let g, p = extract_one_pat true g p in
        let ps = p :: (pats |> List.map (fun x -> snd (extract_one_pat true g x))) in
        let ps_when, rest = ps |> List.partition (function (_, _::_) -> true | _ -> false) in
        let ps = ps_when |> List.map (fun (x, whens) -> (x, mk_when_clause whens)) in
        //branches that contains a new when clause need to be split out
        let res = match rest with 
            | [] -> g, ps
            | rest -> g,  (MLP_Branch(List.map fst rest), None) :: ps in
        res

      | _ -> 
        let g, (p, whens) = extract_one_pat false g p in
        let when_clause = mk_when_clause whens in
        g, [(p, when_clause)] 

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
        | _ -> failwith "Impossible" in

   let as_record qual e =
        match e.expr, qual with
            | MLE_CTor(_, args), Some (Record_ctor(_, fields)) ->
               let path = Util.record_field_path fields in
               let fields = Util.record_fields fields args in
               with_ty e.ty <| MLE_Record(path, fields)
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
                      with_ty e.ty <| MLE_Fun(binders, body)
                    | _ -> failwith "Impossible" in

    match mlAppExpr.expr, qual with
        | _, None -> mlAppExpr

        | MLE_App({expr=MLE_Name mlp}, mle::args), Some (Record_projector f) ->
          let fn = Util.mlpath_of_lid f in
          let proj = MLE_Proj(mle, fn) in
          let e = match args with
            | [] -> proj
            | _ -> MLE_App(with_ty MLTY_Top <| proj, args) in //TODO: Fix imprecise with_ty on the projector 
          with_ty mlAppExpr.ty e 

        | MLE_App ({expr=MLE_Name mlp}, mlargs), Some Data_ctor
        | MLE_App ({expr=MLE_Name mlp}, mlargs), Some (Record_ctor _) -> 
          resugar_and_maybe_eta qual <| (with_ty mlAppExpr.ty <| MLE_CTor (mlp,mlargs))

        | MLE_Name mlp, Some Data_ctor
        | MLE_Name mlp, Some (Record_ctor _) -> 
          resugar_and_maybe_eta qual <| (with_ty mlAppExpr.ty <| MLE_CTor (mlp, []))

        | _ -> mlAppExpr


//The main extraction function
let rec check_term (g:env) (t:term) (f:e_tag) (ty:mlty) :  (mlexpr * mlty) =
    // debug g (fun () -> printfn "Checking %s at type %A\n" (Print.exp_to_string e) t);
    let e, t = check_term' g t f ty in
    let r, _, t = erase g e t f in 
    r, t

and check_term' (g:env) (e0:term) (f:e_tag) (ty:mlty) : (mlexpr * mlty) =
    let e, tag, t = synth_term g e0 in
    if eff_leq tag f
    then maybe_coerce g e t ty, ty
    else err_unexpected_eff e0 f tag

and synth_term (g:env) (t:term) : (mlexpr * e_tag * mlty) =
    let e, tag, ty = synth_term' g t in
    erase g e ty tag

and synth_term' (g:env) (top:term) : (mlexpr * e_tag * mlty) =
    (debug g (fun u -> Util.print_string (Util.format2 "now synthesizing term (%s) :  %s \n" (Print.tag_of_term top) (Print.term_to_string top))));
    let t = SS.compress top in
    match t.n with 
        | Tm_unknown
        | Tm_delayed _
        | Tm_uvar _
        | Tm_bvar _ -> failwith "Impossible"

        | Tm_type _
        | Tm_refine _
        | Tm_arrow _ ->
          ml_unit, E_PURE, ml_unit_ty 

        | Tm_meta(t, _) //TODO: handle the resugaring in case it's a 'Meta_desugared' ... for more readable output
        | Tm_uinst(t, _) -> 
          synth_term' g t

        | Tm_constant c ->
          let ty, _ = TC.type_of g.tcenv t in
          let ml_ty = translate_typ g ty in
          with_ty ml_ty (MLE_Const <| mlconst_of_const' t.pos c), E_PURE, ml_ty

        | Tm_name _
        | Tm_fvar _ -> //lookup in g; decide if its in left or right; tag is Pure because it's just a variable
          if is_type t
          then ml_unit, E_PURE, ml_unit_ty //Erase type argument
          else begin match lookup_term g t with 
                | Inl _, _ -> failwith "Impossible"

                | Inr (x, mltys, _), qual ->
                  //let _ = printfn "\n (*looked up tyscheme of \n %A \n as \n %A *) \n" x s in
                  begin match mltys with
                    | ([], t) -> maybe_eta_data_and_project_record g qual t x, E_PURE, t
                    | _ -> err_uninst g t mltys
                  end
               end

        | Tm_abs(bs, body, copt(* the annotated computation type of the body ... probably don't need it *)) -> 
          let named_binders, open_body = SS.open_term bs body in 
          let ml_bs, env = named_binders |> List.fold_left (fun (ml_bs, env) b -> 
                    if is_type_binder b 
                    then //no first-class polymorphism; so type-binders get wiped out
                         let b = fst b in
                         let env = extend_ty env b (Some MLTY_Top) in
                         let ml_b = (btvar_as_mlTermVar b (*name of the binder*),
                                     ml_unit_ty (*type of the binder. correspondingly, this argument gets converted to the unit value in application *)) in
                         ml_b::ml_bs, env
                    else let b = fst b in
                         let t = translate_typ env b.sort in
                         let env = extend_bv env b ([], t) false false false in
                         let ml_b = ((b.ppname.idText,0), t) in
                         ml_b::ml_bs, env) 
                ([], g) in
            let ml_bs = List.rev ml_bs in
            let ml_body, f, t = synth_term env body in
            //            printfn "Computed type of function body %s to be %A\n" (Print.exp_to_string body) t;
            let f, tfun = List.fold_right
                (fun (_, targ) (f, t) -> E_PURE, MLTY_Fun (targ, f, t))
                ml_bs (f, t) in
            //            printfn "Computed type of abstraction %s to be %A\n" (Print.exp_to_string e) t;
            with_ty tfun <| MLE_Fun(ml_bs, ml_body), f, tfun

        | Tm_app(head, args) ->
          let rec synth_app is_data (mlhead, mlargs_f) (f(*:e_tag*), t (* the type of (mlhead mlargs) *)) restArgs =
//            Printf.printf "synth_app restArgs=%d, t=%A\n" (List.length restArgs) t;
            match restArgs, t with
                | [], _ ->
                    //1. If partially applied and head is a datacon, it needs to be eta-expanded
                    //2. If we're generating OCaml, and any of the arguments are impure, 
                    //   and the head is not a primitive short-circuiting op, 
                    //   then evaluation order must be enforced to be L-to-R (by hoisting)
                    let lbs, mlargs =
                        if U.is_primop head || Util.codegen_fsharp()
                        then [], List.rev mlargs_f |> List.map fst
                        else List.fold_left (fun (lbs, out_args) (arg, f) ->
                                if f=E_PURE || f=E_GHOST
                                then (lbs, arg::out_args)
                                else let x = gensym () in
                                     (x, arg)::lbs, (with_ty arg.ty <| MLE_Var x)::out_args)
                        ([], []) mlargs_f in
                    let app = maybe_eta_data_and_project_record g is_data t <| (with_ty t <| MLE_App(mlhead, mlargs)) in
                    let l_app = List.fold_right 
                        (fun (x, arg) out -> 
                            with_ty out.ty <| MLE_Let((false, [{mllb_name=x; mllb_tysc=Some ([], arg.ty); mllb_add_unit=false; mllb_def=arg}]), 
                                                      out)) 
                        lbs app in // lets are to ensure L to R eval ordering of arguments
                    l_app, f, t

                | (arg, _)::rest, MLTY_Fun (tunit, f', t) when is_type arg -> //non-prefix type app; this type argument gets erased to unit
                  if type_leq g tunit ml_unit_ty
                  then synth_app is_data (mlhead, (ml_unit, E_PURE)::mlargs_f) (join f f', t) rest
                  else failwith "Impossible: ill-typed application" //ill-typed; should be impossible

                | (e0, _)::rest, MLTY_Fun(tExpected, f', t) ->
                  let e0, f0, tInferred = synth_term g e0 in
                  let e0 = maybe_coerce g e0 tInferred tExpected in // coerce the arguments of application, if they dont match up
                  synth_app is_data (mlhead, (e0, f0)::mlargs_f) (join_l [f;f';f0], t) rest

                | _ ->
                  begin match Util.udelta_unfold g t with
                    | Some t -> synth_app is_data (mlhead, mlargs_f) (f, t) restArgs
                    | None -> err_ill_typed_application top restArgs t
                  end in

          if is_type t
          then ml_unit, E_PURE, ml_unit_ty //Erase type argument: TODO: FIXME, this coul
          else let head = SS.compress head in
               begin match head.n with
                | Tm_bvar _
                | Tm_fvar _ ->
                   //             debug g (fun () -> printfn "head of app is %s\n" (Print.exp_to_string head));
                  let (head_ml, (vars, t), inst_ok), qual = match lookup_term g head with Inr (u), q -> u, q | _ -> failwith "FIXME Ty" in
                  let has_typ_apps = match args with 
                    | (a, _)::_ -> is_type a
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
                           let prefixAsMLTypes = List.map (fun (x, _) -> translate_typ g x) prefix in
    //                        let _ = printfn "\n (*about to instantiate  \n %A \n with \n %A \n \n *) \n" (vars,t) prefixAsMLTypes in
                           let t = instantiate (vars, t) prefixAsMLTypes in
                           let head = match head_ml.expr with
                             | MLE_Name _ 
                             | MLE_Var _ -> {head_ml with ty=t} 
                             | MLE_App(head, [{expr=MLE_Const MLC_Unit}]) -> MLE_App({head with ty=MLTY_Fun(ml_unit_ty, E_PURE, t)}, [ml_unit]) |> with_ty t
                             | _ -> failwith "Impossible" in
                           head, t, rest
                      else err_uninst g head (vars, t) in
                    //debug g (fun () -> printfn "\n (*instantiating  \n %A \n with \n %A \n produced \n %A \n *) \n" (vars,t0) prefixAsMLTypes t);
                   begin match args with
                        | [] -> maybe_eta_data_and_project_record g qual head_t head_ml, E_PURE, head_t
                        | _  -> synth_app qual (head_ml, []) (E_PURE, head_t) args
                   end

                | _ ->
                  let head, f, t = synth_term g head in // t is the type inferred for head, the head of the app
                  synth_app None (head, []) (f, t) args
               end

        | Tm_ascribed(e0, t, f) ->
          let t = translate_typ g t in
          let f = match f with
            | None -> failwith "Ascription node with an empty effect label"
            | Some l -> TypeExtraction.translate_eff g l in
          let e, t = check_term g e0 f t in
          e, f, t

        | Tm_let((is_rec, lbs), e') ->
            //          let _ = printfn "\n (* let \n %s \n in \n %s *) \n" (Print.lbs_to_string (is_rec, lbs)) (Print.exp_to_string e') in
          let maybe_generalize {lbname=lbname; lbeff=lbeff; lbtyp=t; lbdef=e} =
              let f_e = TypeExtraction.translate_eff g lbeff in
              let t = SS.compress t in
            //              debug g (fun () -> printfn "Let %s at type %s; expected effect is %A\n" (Print.lbname_to_string lbname) (Print.typ_to_string t) f_e);
              match t.n with
                | Tm_arrow(bs, c) when (List.hd bs |> is_type_binder) ->
                   let bs, c = SS.open_comp bs c in
                  //need to generalize, but will erase all the type abstractions;
                  //If, after erasure, what remains is not a value, then add an extra unit arg. to preserve order of evaluation/generativity
                  //and to circumvent the value restriction

                  //TODO: ERASE ONLY THOSE THAT ABSTRACT OVER PURE FUNCTIONS in Type(i), 
                  //      NOT, e.g., (x:int -> St Type)
                   let tbinders, tbody =
                        match Util.prefix_until (not << is_type_binder) bs with
                            | None -> bs, U.comp_result c
                            | Some (bs, b, rest) -> bs, U.arrow (b::rest) c in

                   let n_tbinders = List.length tbinders in
                   let e = normalize_abs e in
                   begin match e.n with
                      | Tm_abs(bs, body, _) ->
                        if n_tbinders <= List.length bs
                        then let targs, rest_args = Util.first_N n_tbinders bs in
//                             printfn "tbinders are %s\n" (tbinders |> (Print.binders_to_string ", "));
//                             printfn "tbody is %s\n" (Print.typ_to_string tbody);
//                             printfn "targs are %s\n" (targs |> Print.binders_to_string ", ");
                             let expected_t = 
                                let s = List.map2 (fun (x, _) (y, _) -> S.NT(x, S.bv_to_name y)) tbinders targs in
                                SS.subst s tbody in
//                             printfn "After subst: expected_t is %s\n" (Print.typ_to_string expected_t);
                             let env = List.fold_left (fun env (a, _) -> UEnv.extend_ty env a None) g targs in
                             let expected_t = translate_typ env expected_t in
                             let polytype = targs |> List.map (btvar_as_mltyvar << fst), expected_t in
                             let add_unit = match rest_args with
                                | [] -> not (is_fstar_value body) //if it's a pure type app, then it will be extracted to a value in ML; so don't add a unit
                                | _ -> false in
                             let rest_args = if add_unit then (unit_binder::rest_args) else rest_args in
                             let body = match rest_args with 
                                | [] -> body 
                                | _ -> U.abs rest_args body None in
                             (lbname, f_e, (t, (targs, polytype)), add_unit, body)

                        else (* fails to handle:
                                let f : a:Type -> b:Type -> a -> b -> Tot (nat * a * b) =
                                    fun (a:Type) ->
                                      let x = 0 in
                                      fun (b:Type) (y:a) (z:b) -> (x, y, z)

                                Could eta-expand; but with effects this is problem; see ETA-EXPANSION and NO GENERALIZATION below
                             *)
                             failwith "Not enough type binders" //TODO: better error message
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
                  let expected_t = translate_typ g t in
                  (lbname, f_e, (t, ([], ([],expected_t))), false, e) in

          let check_lb env (nm, (lbname, f, (t, (targs, polytype)), add_unit, e)) =
              let env = List.fold_left (fun env (a, _) -> UEnv.extend_ty env a None) env targs in
              let expected_t = if add_unit then MLTY_Fun(ml_unit_ty, E_PURE, snd polytype) else snd polytype in
              let e, _ = check_term env e f expected_t in
              f, {mllb_name=nm; mllb_tysc=Some polytype; mllb_add_unit=add_unit; mllb_def=e} in

         (*after the above definitions, here is the main code for extracting let expressions*)
          let lbs = lbs |> List.map maybe_generalize in

          let env_body, lbs = List.fold_right (fun lb (env, lbs) ->
              let (lbname, _, (t, (_, polytype)), add_unit, _) = lb in
              let env, nm = UEnv.extend_lb env lbname t polytype add_unit true in
              env, (nm,lb)::lbs) lbs (g, []) in

          let env_def = if is_rec then env_body else g in

          let lbs = lbs |> List.map (check_lb env_def)  in

          let e', f', t' = synth_term env_body e' in

          let f = join_l (f'::List.map fst lbs) in

          with_ty_loc t' (MLE_Let((is_rec, List.map snd lbs), e')) (TypeExtraction.mlloc_of_range t.pos), f, t'

      | Tm_match(scrutinee, pats) ->
        let e, f_e, t_e = synth_term g scrutinee in
        let b, then_e, else_e = check_pats_for_ite pats in
        let no_lift : mlexpr -> mlty -> mlexpr = fun x t -> x in
        if b then
            match then_e, else_e with
                | Some then_e, Some else_e ->
                    let then_mle, f_then, t_then = synth_term g then_e in
                    let else_mle, f_else, t_else = synth_term g else_e in
                    let t_branch, maybe_lift = 
                        if type_leq g t_then t_else  //the types agree except for effect labels
                        then t_else, no_lift 
                        else if type_leq g t_else t_then 
                        then t_then, no_lift
                        else MLTY_Top, apply_obj_repr in
                    with_ty t_branch <| MLE_If (e, maybe_lift then_mle t_then, Some (maybe_lift else_mle t_else)), 
                    join f_then f_else,
                    t_branch
                | _ -> failwith "ITE pats matched but then and else expressions not found?"
        else
            let mlbranches = pats |> List.collect (fun (pat, when_opt, branch) ->
                let env, p = extract_pat g pat in
                let when_opt, f_when = match when_opt with
                    | None -> None, E_PURE
                    | Some w -> 
                        let w, f_w, t_w = synth_term env w in
                        let w = maybe_coerce env w t_w ml_bool_ty in
                        Some w, f_w in
                let mlbranch, f_branch, t_branch = synth_term env branch in
                //Printf.printf "Extracted %s to %A\n" (Print.exp_to_string branch) mlbranch;
                p |> List.map (fun (p, wopt) -> 
                    let when_clause = conjoin_opt wopt when_opt in
                    p, (when_clause, f_when), (mlbranch, f_branch, t_branch)))
            in
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
                        let f = join f f_branch in 
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
    let wildcards = match fstar_disc_type.n with
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
    MLM_Let (false,[{mllb_name=convIdent discName.ident; mllb_tysc=None; mllb_add_unit=false; mllb_def=discrBody}] )
