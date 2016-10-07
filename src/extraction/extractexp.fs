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
module FStar.Extraction.ML.ExtractExp
open FStar
open FStar.Util
open FStar.Absyn
open FStar.Absyn.Syntax
open FStar.Const
open FStar.Extraction
open FStar.Extraction.ML.Syntax
open FStar.Extraction.ML.Env
open FStar.Extraction.ML.Util
open FStar.Ident

let type_leq g t1 t2 = Util.type_leq (Util.delta_unfold g) t1 t2
let type_leq_c g t1 t2 = Util.type_leq_c (Util.delta_unfold g) t1 t2
let erasableType g t = Util.erasableType (Util.delta_unfold g) t
let eraseTypeDeep g t = Util.eraseTypeDeep (Util.delta_unfold g) t

let fail r msg =
    Util.print_string <| Print.format_error r msg;
    failwith msg

let err_uninst env e (vars, t) =
    fail e.pos (Util.format3 "Variable %s has a polymorphic type (forall %s. %s); expected it to be fully instantiated"
                    (Print.exp_to_string e)
                    (vars |> List.map fst |> String.concat ", ")
                    (ML.Code.string_of_mlty env.currentModule t))

let err_ill_typed_application (e : exp) args (t : mlty) =
    fail e.pos (Util.format2 "Ill-typed application: application is %s \n remaining args are %s\n"
                (Print.exp_to_string e)
                 // t
                (Print.args_to_string args))


let err_value_restriction e =
    fail e.pos ("Refusing to generalize because of the value restriction")

let err_unexpected_eff e f0 f1 =
    fail e.pos (Util.format3 "for expression %s, Expected effect %s; got effect %s" (Print.exp_to_string e) (eff_to_string f0) (eff_to_string f1))

let is_constructor e = match (Util.compress_exp e).n with
    | Exp_fvar(_, Some Data_ctor)
    | Exp_fvar(_, Some (Record_ctor _)) -> true
    | _ -> false

(* something is a value iff it qualifies for the OCaml's "value restriction", which determines when a definition can be generalized *)
let rec is_value_or_type_app (e:exp) = match (Util.compress_exp e).n with
    | Exp_constant _
    | Exp_bvar _
    | Exp_fvar _
    | Exp_abs _  -> true
    | Exp_app(head, args) ->
        if is_constructor head
        then args |> List.for_all (fun (te, _) ->
                match te with
                    | Inl _ -> true (* type argument *)
                    | Inr e -> is_value_or_type_app e)
        else (match (Util.compress_exp head).n with
                 | Exp_bvar _
                 | Exp_fvar _ -> args |> List.for_all (function (Inl te, _) -> true | _ -> false)
                 | _ -> false)
    | Exp_meta(Meta_desugared(e, _))
    | Exp_ascribed(e, _, _) -> is_value_or_type_app e
    | _ -> false

let rec is_ml_value e = match e.expr with
    | MLE_Const _
    | MLE_Var   _
    | MLE_Name  _
    | MLE_Fun   _ -> true
    | MLE_CTor (_, exps)
    | MLE_Tuple exps -> Util.for_all is_ml_value exps
    | MLE_Record (_, fields) -> Util.for_all (fun (_, e) -> is_ml_value e) fields
    | _ -> false

(*INVARIANT: we MUST always perform deep erasure after extraction of types, even when done indirectly e.g. translate_typ_of_arg below.
  Otherwise, there will be Ob.magic because the types get erased at some places and not at other places *)
let translate_typ (g:env) (t:typ) : mlty = eraseTypeDeep g (ExtractTyp.extractTyp g t)
let translate_typ_of_arg (g:env) (a:arg) : mlty = eraseTypeDeep g (ExtractTyp.getTypeFromArg g a)

// erasing here is better because if we need to generate OCaml types for binders and return values, they will be accurate. By the time we reach maybe_coerce, we cant change those

let instantiate (s:mltyscheme) (args:list<mlty>) : mlty = Util.subst s args (*only handles fully applied types*)

let erasable (g:env)  (f:e_tag) (t:mlty) =
    f = E_GHOST
    || (f = E_PURE && erasableType g t)

let erase (g:env) (e:mlexpr) (f:e_tag) (t:mlty) : mlexpr * e_tag * mlty =
    if erasable g f t
    then (debug g (fun () -> Util.print2 "Erasing %s at type %s\n" (ML.Code.string_of_mlexpr g.currentModule e) (ML.Code.string_of_mlty g.currentModule t));
          let e_val = if type_leq g t ml_unit_ty then ml_unit else with_ty t <| MLE_Coerce(ml_unit, ml_unit_ty, t) in
          e_val, f, t)
    else e, f, t

let maybe_coerce (g:env) (e:mlexpr) (tInferred:mlty) (tExpected:mlty) : mlexpr =
    // let tExpected = eraseTypeDeep g tExpected in
    // is this needed? see translate_typ. Even if we coerce here, there is no way to change the type of the generate expression
    match type_leq_c g (Some e) tInferred tExpected with
        | true, Some e' -> e'
        | _ ->
//         debug g (fun () -> printfn "\n (*needed to coerce expression \n %A \n of type \n %A \n to type \n %A *) \n" e tInferred tExpected);
         with_ty tExpected <| MLE_Coerce (e, tInferred, tExpected)

let extract_pat (g:env) p : (env * list<(mlpattern * option<mlexpr>)>) =
(*what does disj stand for? NS: disjunctive *)
    let rec extract_one_pat (disj : bool) (imp : bool) g p : env * option<(mlpattern * list<mlexpr>)> =
        match p.v with
          | Pat_disj _ -> failwith "Impossible"

          | Pat_constant (Const_int (c, None)) ->
            let i = Const_int (c, None) in
            //these may be extracted to bigint, in which case, we need to emit a when clause
            let x = as_mlident (Util.new_bvd None) in
            let when_clause = with_ty ml_bool_ty <|
              MLE_App(prims_op_equality, [with_ty ml_int_ty <| MLE_Var x;
                                          with_ty ml_int_ty <| (MLE_Const <| mlconst_of_const' p.p i)]) in
            g, Some (MLP_Var x, [when_clause])

          | Pat_constant s     ->
            g, Some (MLP_Const (mlconst_of_const' p.p s), [])

          | Pat_cons (f, q, pats) ->
            let d,tys = match Env.lookup_fv g f with
                | {expr=MLE_Name n}, ttys, _ -> n, ttys
                | _ -> failwith "Expected a constructor" in
            let nTyVars = List.length (fst tys) in
            let tysVarPats, restPats =  Util.first_N nTyVars pats in
            let g, tyMLPats = Util.fold_map (fun g (p, imp) -> extract_one_pat disj true g p) g tysVarPats in (*not all of these were type vars in ML*)
            let g, restMLPats = Util.fold_map (fun g (p, imp) ->
                let env, popt = extract_one_pat disj false g p in
                let popt = match popt with
                    | None -> Some (MLP_Wild, [])
                    | _ -> popt in
                env, popt) g restPats in
            let mlPats, when_clauses = List.append tyMLPats restMLPats |> List.collect (function (Some x) -> [x] | _ -> []) |> List.split in
            g, Some (Util.resugar_pat q <| MLP_CTor (d, mlPats), when_clauses |> List.flatten)

          | Pat_var x ->
            let mlty = translate_typ g x.sort in
            let g = Env.extend_bv g x ([], mlty) false false imp in
            g, (if imp then None else Some (MLP_Var (as_mlident x.v), []))

          | Pat_wild x when disj ->
            g, Some (MLP_Wild, [])

          | Pat_wild x -> (*how is this different from Pat_var? For extTest.naryTree.Node, the first projector uses Pat_var and the other one uses Pat_wild*)
            let mlty = translate_typ g x.sort in
            let g = Env.extend_bv g x ([], mlty) false false imp in
            g, (if imp then None else Some (MLP_Var (as_mlident x.v), []))

          | Pat_tvar a ->
            let mlty = MLTY_Top in
            let g = Env.extend_ty g a (Some mlty) in
            g, (if imp then None else Some (MLP_Wild, []))

          | Pat_dot_term _
          | Pat_dot_typ _
          | Pat_twild _ ->
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

let normalize_abs e0 =
    let rec aux bs e =
        let e = Util.compress_exp e in
        match e.n with
            | Exp_abs(bs', body) -> aux (bs@bs') body
            | _ ->
              let e' = Util.unascribe e in
              if Util.is_fun e'
              then aux bs e'
              else mk_Exp_abs(bs, e) None e0.pos in
   aux [] e0

let ffi_mltuple_mlp (n:int) : mlpath =
    let name = if (2<n && n<6) then ("mktuple"^(Util.string_of_int n)) else (if n=2 then "mkpair" else (failwith "NYI in runtime/allocator/camlstack.mli")) in
    ["Camlstack"],name

(* TODO: Fix the with_ty annotations here, once the type of lalloc is stable *)
let fix_lalloc (arg (*the argument of lalloc (type arg is erased) *):mlexpr) : mlexpr =
    match arg.expr with
        | MLE_Tuple  args -> failwith "unexpected. Prims.TupleN is not specially handled yet. So, F* tuples, which are sugar forPrims.TupleN,  were expected to be extracted as MLE_CTor"
        | MLE_Record (mlns, fields) ->
            let args = List.map snd fields in
                let tup =  with_ty MLTY_Top <| MLE_App (with_ty MLTY_Top <| MLE_Name (ffi_mltuple_mlp (List.length args)), args) in
                let dummyTy = ml_unit_ty in
                with_ty dummyTy <| MLE_Coerce (tup,dummyTy,dummyTy) // if the pretty printing phase prints dummyTy, we will be in trouble
        | MLE_CTor (mlp, args) -> failwith "NYI: lalloc ctor"
        | _ -> failwith "for efficiency, the argument to lalloc should be a head normal form of the type. Extraction will then avoid creating this value on the heap."



(*Preconditions :
   1) residualType is the type of mlAppExpr
   2) mlAppExpr is an MLE_Name or an MLE_App with its head a named fvar, and isDataCons is true iff it names a data constructor of a data type.
  Postconditions
   1) the return value (say r) also has type residualType and it's extraction-preimage is definitionally equal (in Fstar ) to that of mlAppExpr
   2) meets the ML requirements that the args to datacons be tupled and that the datacons be fullly applied
*)
let maybe_lalloc_eta_data (g:env) (qual : option<fv_qual>) (residualType : mlty)  (mlAppExpr : mlexpr) : mlexpr =
    let rec eta_args more_args t = match t with
        | MLTY_Fun (t0, _, t1) ->
          let x = Util.gensym (), -1 in
          eta_args (((x, t0), with_ty t0 <| MLE_Var x)::more_args) t1
        | MLTY_Named (_, _) -> List.rev more_args, t
        | _ -> failwith "Impossible" in

   let as_record qual e =
        match e.expr, qual with
            | MLE_CTor(_, args), Some (Record_ctor(_, fields)) ->
               let path = Util.record_field_path fields in
               let fields = Util.record_fields fields args in
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
                    | _ -> failwith "Impossible" in

    match mlAppExpr.expr, qual with
        | MLE_App ({expr=MLE_Name mlp}, [mlarg]), _ when (mlp=mlp_lalloc) ->
          debug g (fun () -> Util.print_string "need to do lalloc surgery here\n");
          fix_lalloc mlarg

        | _, None -> mlAppExpr

        | MLE_App({expr=MLE_Name mlp}, mle::args), Some (Record_projector f) ->
          let fn = Util.mlpath_of_lid f in
          let proj = MLE_Proj(mle, fn) in
          let e = match args with
            | [] -> proj
            | _ ->
              MLE_App(with_ty MLTY_Top <| proj, args) in //TODO: Fix imprecise with_ty on the projector
          with_ty mlAppExpr.mlty e

        | MLE_App ({expr=MLE_Name mlp}, mlargs), Some Data_ctor
        | MLE_App ({expr=MLE_Name mlp}, mlargs), Some (Record_ctor _) ->
          resugar_and_maybe_eta qual <| (with_ty mlAppExpr.mlty <| MLE_CTor (mlp,mlargs))

        | MLE_Name mlp, Some Data_ctor
        | MLE_Name mlp, Some (Record_ctor _) ->
          resugar_and_maybe_eta qual <| (with_ty mlAppExpr.mlty <| MLE_CTor (mlp, []))

        | _ -> mlAppExpr

let check_pats_for_ite (l:list<(pat * option<exp> * exp)>) :(bool * option<exp> * option<exp>) =
    let def = false, None, None in
    if List.length l <> 2 then def
    else
        let (p1, w1, e1) = List.hd l in
        let (p2, w2, e2) = List.hd (List.tl l) in
        match (w1, w2, p1.v, p2.v) with
            | (None, None, Pat_constant (Const_bool true), Pat_constant (Const_bool false)) -> true, Some e1, Some e2
            | (None, None, Pat_constant (Const_bool false), Pat_constant (Const_bool true)) -> true, Some e2, Some e1
            | _ -> def


let rec check_exp (g:env) (e:exp) (f:e_tag) (t:mlty) : mlexpr =
    // debug g (fun () -> printfn "Checking %s at type %A\n" (Print.exp_to_string e) t);
    let e, _, _ = erase g (check_exp' g e f t) f t in
    e

and check_exp' (g:env) (e:exp) (f:e_tag) (t:mlty) : mlexpr =
    let e0, f0, t0 = synth_exp g e in
    if eff_leq f0 f
    then maybe_coerce g e0 t0 t
    else err_unexpected_eff e f f0

and synth_exp (g:env) (e:exp) : (mlexpr * e_tag * mlty) =
    let e, f, t = synth_exp' g e in
    erase g e f t
    // TODO: should we first check for erasability and only then bother synthesizing an expression? Perhaps not. the type and the tag get produced during sythesis

(* Unlike the \epsilon function in the thesis, this also produced an ml type for the computed ML expression,
 to avoid the need to infer them later, when less info is available*)
and synth_exp' (g:env) (e:exp) : (mlexpr * e_tag * mlty) =
   (debug g (fun u -> Util.print_string (Util.format2 "now synthesizing expression (%s) :  %s \n" (Print.tag_of_exp e) (Print.exp_to_string e))));
    let top = e in
    match (Util.compress_exp e).n with
        | Exp_constant c ->
          let t = Tc.Recheck.typing_const e.pos c in
          let ml_ty = translate_typ g t in
          with_ty ml_ty (MLE_Const <| mlconst_of_const' e.pos c), E_PURE, ml_ty

        | Exp_ascribed(e0, t, f) ->
          let t = translate_typ g t in
          let f = match f with
            | None -> failwith "Ascription node with an empty effect label"
            | Some l -> ExtractTyp.translate_eff g l in
          let e = check_exp g e0 f t in
          e, f, t

        | Exp_bvar _
        | Exp_fvar _ ->
          let (x, mltys, _), qual = lookup_var g e in
          //let _ = printfn "\n (*looked up tyscheme of \n %A \n as \n %A *) \n" x s in
          begin match mltys with
            | ([], t) -> maybe_lalloc_eta_data g qual t x, E_PURE, t
            | _ -> err_uninst g e mltys
          end

        | Exp_app(head, args) ->
          let rec synth_app is_data (mlhead, mlargs_f) (f(*:e_tag*), t (* the type of (mlhead mlargs) *)) restArgs =
          //            Printf.printf "synth_app restArgs=%d, t=%A\n" (List.length restArgs) t;
            match restArgs, t with
                | [], _ ->
                    //1. If partially applied and head is a datacon, it needs to be eta-expanded
                    //2. If we're generating OCaml, and any of the arguments are impure,
                    //   and the head is not a primitive short-circuiting op,
                    //   then evaluation order must be enforced to be L-to-R (by hoisting)
                    let lbs, mlargs =
                        if Util.is_primop head || Util.codegen_fsharp()
                        then [], List.rev mlargs_f |> List.map fst
                        else List.fold_left (fun (lbs, out_args) (arg, f) ->
                                if f=E_PURE || f=E_GHOST
                                then (lbs, arg::out_args)
                                else let x = Util.gensym (), -1 in
                                     (x, arg)::lbs, (with_ty arg.mlty <| MLE_Var x)::out_args)
                        ([], []) mlargs_f in
                    let app = maybe_lalloc_eta_data g is_data t <| (with_ty t <| MLE_App(mlhead, mlargs)) in
                    let l_app = List.fold_right
                        (fun (x, arg) out ->
                          with_ty out.mlty <| MLE_Let((NonRec, [], [{mllb_name=x; mllb_tysc=Some ([], arg.mlty); mllb_add_unit=false; mllb_def=arg; print_typ=true}]),
                                                      out))
                        lbs app in // lets are to ensure L to R eval ordering of arguments
                    l_app, f, t

                | (Inl tt, _)::rest, MLTY_Fun (tunit, f', t) -> //non-prefix type app; this type argument gets erased to unit
                  if type_leq g tunit ml_unit_ty
                  then synth_app is_data (mlhead, (ml_unit, E_PURE)::mlargs_f) (join tt.pos f f', t) rest
                  else failwith "Impossible: ill-typed application" //ill-typed; should be impossible


                | (Inr e0, _)::rest, MLTY_Fun(tExpected, f', t) ->
                  let e0_rng = e0.pos in
                  let e0, f0, tInferred = synth_exp g e0 in
                  let e0 = maybe_coerce g e0 tInferred tExpected in // coerce the arguments of application, if they dont match up
                  synth_app is_data (mlhead, (e0, f0)::mlargs_f) (join_l e0_rng [f;f';f0], t) rest

                | _ ->
                  begin match Util.delta_unfold g t with
                    | Some t -> synth_app is_data (mlhead, mlargs_f) (f, t) restArgs
                    | None -> err_ill_typed_application e restArgs t
                  end in

          let synth_app_maybe_projector is_data mlhead (f, t) args =
                match is_data with
                    | Some (Record_projector _) ->
                      let rec remove_implicits args f t = match args, t with
                        | (Inr ee, Some (Implicit _))::args, MLTY_Fun(_, f', t) ->
                          remove_implicits args (join ee.pos f f') t

                        | _ -> args, f, t in
                      let args, f, t = remove_implicits args f t in
                      synth_app is_data (mlhead, []) (f, t) args

                    | _ -> synth_app is_data (mlhead, []) (f, t) args in

          let head = Util.compress_exp head in
          begin match head.n with
            | Exp_bvar _
            | Exp_fvar _ ->
//              debug g (fun () -> printfn "head of app is %s\n" (Print.exp_to_string head));
              let (head_ml, (vars, t), inst_ok), qual = lookup_var g head in
              let has_typ_apps = match args with
                | (Inl _, _)::_ -> true
                | _ -> false in
//              debug g (fun () -> printfn "\n (*looked up tyscheme \n %A *) \n" (vars,t));
              let head_ml, head_t, args = match vars with
                | _::_ when ((not has_typ_apps) && inst_ok) ->
                  (* no explicit type applications although some were expected; but instantiation is permissible *)
//                  Printf.printf "Taking the type of %A to be %A\n" head_ml t;
                  head_ml, t, args

                | _ ->
                  let n = List.length vars in
                  if n <= List.length args
                  then let prefix, rest = Util.first_N n args in
//                       let _ = (if n=1 then printfn "\n (*prefix was  \n %A \n  *) \n" prefix) in
                       let prefixAsMLTypes = List.map (translate_typ_of_arg g) prefix in
//                        let _ = printfn "\n (*about to instantiate  \n %A \n with \n %A \n \n *) \n" (vars,t) prefixAsMLTypes in
                       let t = instantiate (vars, t) prefixAsMLTypes in
                       let head = match head_ml.expr with
                         | MLE_Name _
                         | MLE_Var _ -> {head_ml with mlty=t}
                         | MLE_App(head, [{expr=MLE_Const MLC_Unit}]) -> MLE_App({head with mlty=MLTY_Fun(ml_unit_ty, E_PURE, t)}, [ml_unit]) |> with_ty t
                         | _ -> failwith "Impossible" in
                       head, t, rest
                  else err_uninst g head (vars, t) in
                //debug g (fun () -> printfn "\n (*instantiating  \n %A \n with \n %A \n produced \n %A \n *) \n" (vars,t0) prefixAsMLTypes t);
               begin match args with
                    | [] -> maybe_lalloc_eta_data g qual head_t head_ml, E_PURE, head_t
                    | _  -> synth_app_maybe_projector qual head_ml (E_PURE, head_t) args
               end

            | _ ->
              let head, f, t = synth_exp g head in // t is the type inferred for head, the head of the app
              synth_app_maybe_projector None head (f, t) args
          end

        | Exp_abs(bs, body) ->
            let ml_bs, env = List.fold_left (fun (ml_bs, env) (b, _) -> match b with
                | Inl a -> //no first-class polymorphism; so type-binders get wiped out
                  let env = Env.extend_ty env a (Some MLTY_Top) in
                  let ml_b = (btvar_as_mlTermVar a (*name of the binder*) , ml_unit_ty (*type of the binder. correspondingly, this argument gets converted to the unit value in application *)) in
                  ml_b::ml_bs, env

                | Inr x ->
                  let t = translate_typ env x.sort in
                  let env = Env.extend_bv env x ([], t) false false false in
                  let ml_b = (as_mlident x.v, t) in
                  ml_b::ml_bs, env) ([], g) bs in
            let ml_bs = List.rev ml_bs in
            let ml_body, f, t = synth_exp env body in
//            printfn "Computed type of function body %s to be %A\n" (Print.exp_to_string body) t;
            let f, tfun = List.fold_right
                (fun (_, targ) (f, t) -> E_PURE, MLTY_Fun (targ, f, t))
                ml_bs (f, t) in
//            printfn "Computed type of abstraction %s to be %A\n" (Print.exp_to_string e) t;
            with_ty tfun <| MLE_Fun(ml_bs, ml_body), f, tfun

        | Exp_let((is_rec, lbs), e') ->
//          let _ = printfn "\n (* let \n %s \n in \n %s *) \n" (Print.lbs_to_string (is_rec, lbs)) (Print.exp_to_string e') in
          let maybe_generalize {lbname=lbname; lbeff=lbeff; lbtyp=t; lbdef=e} =
              let f_e = ExtractTyp.translate_eff g lbeff in
              let t = Util.compress_typ t in
//              debug g (fun () -> printfn "Let %s at type %s; expected effect is %A\n" (Print.lbname_to_string lbname) (Print.typ_to_string t) f_e);
              match t.n with
                | Typ_fun(bs, c) when is_type_abstraction bs ->
                  //need to generalize, but will erase all the type abstractions;
                  //If, after erasure, what remains is not a value, then add an extra unit arg. to preserve order of evaluation/generativity
                  //and to circumvent the value restriction
                   let tbinders, tbody =
                        match Util.prefix_until (function (Inr _, _) -> true | _ -> false) bs with
                            | None -> bs, Util.comp_result c
                            | Some (bs, b, rest) -> bs, mk_Typ_fun(b::rest, c) None c.pos in

                   let n = List.length tbinders in
                   let e = normalize_abs e in
                   begin match e.n with
                      | Exp_abs(bs, body) ->
                        if n <= List.length bs
                        then let targs, rest_args = Util.first_N n bs in
//                             printfn "tbinders are %s\n" (tbinders |> (Print.binders_to_string ", "));
//                             printfn "tbody is %s\n" (Print.typ_to_string tbody);
//                             printfn "targs are %s\n" (targs |> Print.binders_to_string ", ");
                             let expected_t = match Util.mk_subst_binder targs tbinders with
                                | None -> failwith "Not enough type binders in the body of the let expression"
                                | Some s -> Util.subst_typ s tbody in
//                             printfn "After subst: expected_t is %s\n" (Print.typ_to_string expected_t);
                             let targs = targs |> List.map (function (Inl a, _) -> a | _ -> failwith "Impossible") in
                             let env = List.fold_left (fun env a -> Env.extend_ty env a None) g targs in
                             let expected_t = translate_typ env expected_t in
                             let polytype = targs |> List.map btvar_as_mltyvar, expected_t in
                             let add_unit = match rest_args with
                                | [] -> not (is_value_or_type_app body) //if it's a pure type app, then it will be extracted to a value in ML; so don't add a unit
                                | _ -> false in
                             let rest_args = if add_unit then (unit_binder::rest_args) else rest_args in
                             let body = match rest_args with | [] -> body | _ -> mk_Exp_abs(rest_args, body) None e.pos in
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
              let env = List.fold_left (fun env a -> Env.extend_ty env a None) env targs in
              let expected_t = if add_unit then MLTY_Fun(ml_unit_ty, E_PURE, snd polytype) else snd polytype in
              let e = check_exp env e f expected_t in
              f, {mllb_name=nm; mllb_tysc=Some polytype; mllb_add_unit=add_unit; mllb_def=e; print_typ=true} in

         (*after the above definitions, here is the main code for extracting let expressions*)
          let lbs = lbs |> List.map maybe_generalize in

          let env_body, lbs = List.fold_right (fun lb (env, lbs) ->
              let (lbname, _, (t, (_, polytype)), add_unit, _) = lb in
              let env, nm = Env.extend_lb env lbname t polytype add_unit true in
              env, (nm,lb)::lbs) lbs (g, []) in

          let env_def = if is_rec then env_body else g in

          let lbs = lbs |> List.map (check_lb env_def)  in

          let e'_rng = e'.pos in
          let e', f', t' = synth_exp env_body e' in

          let f = join_l e'_rng (f'::List.map fst lbs) in

          let is_rec = if is_rec then Rec else NonRec in

          with_ty_loc t' (MLE_Let((is_rec, [], List.map snd lbs), e')) (Util.mlloc_of_range e.pos), f, t'

      | Exp_match(scrutinee, pats) ->
        let e, f_e, t_e = synth_exp g scrutinee in
        let b, then_e, else_e = check_pats_for_ite pats in
        let no_lift : mlexpr -> mlty -> mlexpr = fun x t -> x in
        if b then
            match then_e, else_e with
                | Some then_e, Some else_e ->
                    let then_mle, f_then, t_then = synth_exp g then_e in
                    let else_mle, f_else, t_else = synth_exp g else_e in
                    let t_branch, maybe_lift =
                        if type_leq g t_then t_else  //the types agree except for effect labels
                        then t_else, no_lift
                        else if type_leq g t_else t_then
                        then t_then, no_lift
                        else MLTY_Top, apply_obj_repr in
                    with_ty t_branch <| MLE_If (e, maybe_lift then_mle t_then, Some (maybe_lift else_mle t_else)),
                    join top.pos f_then f_else,
                    t_branch
                | _ -> failwith "ITE pats matched but then and else expressions not found?"
        else
            let mlbranches = pats |> List.collect (fun (pat, when_opt, branch) ->
                let env, p = extract_pat g pat in
                let when_opt, f_when = match when_opt with
                    | None -> None, E_PURE
                    | Some w ->
                        let w, f_w, t_w = synth_exp env w in
                        let w = maybe_coerce env w t_w ml_bool_ty in
                        Some w, f_w in
                let mlbranch, f_branch, t_branch = synth_exp env branch in
                //Printf.printf "Extracted %s to %A\n" (Print.exp_to_string branch) mlbranch;
                p |> List.map (fun (p, wopt) ->
                    let when_clause = conjoin_opt wopt when_opt in
                    p, (when_clause, f_when), (mlbranch, f_branch, t_branch)))
            in
            begin match mlbranches with
                | [] ->
                    let fw, _, _ = lookup_fv g (Util.fv Const.failwith_lid) in
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
                   with_ty t_match <| MLE_Match(e, mlbranches),
                   f_match,
                   t_match
            end

      | Exp_meta(Meta_desugared(e, _)) -> synth_exp g e //TODO: handle the re-sugaring

      | Exp_uvar _
      | Exp_delayed _ -> fail e.pos "Unexpected expression"

(*copied from ocaml-asttrans.fs*)
let fresh = let c = mk_ref 0 in
            fun x -> (incr c; (x, !c))

let ind_discriminator_body env (discName:lident) (constrName:lident) : mlmodule1 =
    // First, lookup the original (F*) type to figure out how many implicit arguments there are.
    let fstar_disc_type: typ = Tc.Env.lookup_lid env.tcenv discName in
    let wildcards = match fstar_disc_type.n with
        | Typ_fun (binders, _) ->
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
    MLM_Let (NonRec,[],[{mllb_name=convIdent discName.ident; mllb_tysc=None; mllb_add_unit=false; mllb_def=discrBody; print_typ=true}] )
