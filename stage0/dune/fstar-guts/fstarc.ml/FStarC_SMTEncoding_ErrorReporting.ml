open Prims
type goal =
  {
  goal_id: Prims.int ;
  goal_msg: FStarC_Errors_Msg.error_message ;
  goal_range: FStarC_Range_Type.t ;
  goal_term: FStarC_SMTEncoding_Term.term ;
  goal_source: FStarC_Syntax_Syntax.term }
let __proj__Mkgoal__item__goal_id (projectee : goal) : Prims.int=
  match projectee with
  | { goal_id; goal_msg; goal_range; goal_term; goal_source;_} -> goal_id
let __proj__Mkgoal__item__goal_msg (projectee : goal) :
  FStarC_Errors_Msg.error_message=
  match projectee with
  | { goal_id; goal_msg; goal_range; goal_term; goal_source;_} -> goal_msg
let __proj__Mkgoal__item__goal_range (projectee : goal) :
  FStarC_Range_Type.t=
  match projectee with
  | { goal_id; goal_msg; goal_range; goal_term; goal_source;_} -> goal_range
let __proj__Mkgoal__item__goal_term (projectee : goal) :
  FStarC_SMTEncoding_Term.term=
  match projectee with
  | { goal_id; goal_msg; goal_range; goal_term; goal_source;_} -> goal_term
let __proj__Mkgoal__item__goal_source (projectee : goal) :
  FStarC_Syntax_Syntax.term=
  match projectee with
  | { goal_id; goal_msg; goal_range; goal_term; goal_source;_} -> goal_source
type ctx_elt =
  | CVar of FStarC_Syntax_Syntax.bv 
  | CDef of FStarC_Syntax_Syntax.bv * FStarC_Syntax_Syntax.term 
  | CHyp of FStarC_Syntax_Syntax.term 
  | CMatch of FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.pat 
let uu___is_CVar (projectee : ctx_elt) : Prims.bool=
  match projectee with | CVar _0 -> true | uu___ -> false
let __proj__CVar__item___0 (projectee : ctx_elt) : FStarC_Syntax_Syntax.bv=
  match projectee with | CVar _0 -> _0
let uu___is_CDef (projectee : ctx_elt) : Prims.bool=
  match projectee with | CDef (_0, _1) -> true | uu___ -> false
let __proj__CDef__item___0 (projectee : ctx_elt) : FStarC_Syntax_Syntax.bv=
  match projectee with | CDef (_0, _1) -> _0
let __proj__CDef__item___1 (projectee : ctx_elt) : FStarC_Syntax_Syntax.term=
  match projectee with | CDef (_0, _1) -> _1
let uu___is_CHyp (projectee : ctx_elt) : Prims.bool=
  match projectee with | CHyp _0 -> true | uu___ -> false
let __proj__CHyp__item___0 (projectee : ctx_elt) : FStarC_Syntax_Syntax.term=
  match projectee with | CHyp _0 -> _0
let uu___is_CMatch (projectee : ctx_elt) : Prims.bool=
  match projectee with | CMatch (_0, _1) -> true | uu___ -> false
let __proj__CMatch__item___0 (projectee : ctx_elt) :
  FStarC_Syntax_Syntax.term= match projectee with | CMatch (_0, _1) -> _0
let __proj__CMatch__item___1 (projectee : ctx_elt) :
  FStarC_Syntax_Syntax.pat= match projectee with | CMatch (_0, _1) -> _1
type goal_tree =
  | GTrivial 
  | GLeaf of goal 
  | GCtx of FStarC_SMTEncoding_Term.decl Prims.list * ctx_elt Prims.list *
  goal_tree 
  | GBranch of goal_tree Prims.list 
let uu___is_GTrivial (projectee : goal_tree) : Prims.bool=
  match projectee with | GTrivial -> true | uu___ -> false
let uu___is_GLeaf (projectee : goal_tree) : Prims.bool=
  match projectee with | GLeaf _0 -> true | uu___ -> false
let __proj__GLeaf__item___0 (projectee : goal_tree) : goal=
  match projectee with | GLeaf _0 -> _0
let uu___is_GCtx (projectee : goal_tree) : Prims.bool=
  match projectee with | GCtx (_0, _1, _2) -> true | uu___ -> false
let __proj__GCtx__item___0 (projectee : goal_tree) :
  FStarC_SMTEncoding_Term.decl Prims.list=
  match projectee with | GCtx (_0, _1, _2) -> _0
let __proj__GCtx__item___1 (projectee : goal_tree) : ctx_elt Prims.list=
  match projectee with | GCtx (_0, _1, _2) -> _1
let __proj__GCtx__item___2 (projectee : goal_tree) : goal_tree=
  match projectee with | GCtx (_0, _1, _2) -> _2
let uu___is_GBranch (projectee : goal_tree) : Prims.bool=
  match projectee with | GBranch _0 -> true | uu___ -> false
let __proj__GBranch__item___0 (projectee : goal_tree) : goal_tree Prims.list=
  match projectee with | GBranch _0 -> _0
let gctx (ds : FStarC_SMTEncoding_Term.decl Prims.list)
  (cs : ctx_elt Prims.list) (t : goal_tree) : goal_tree=
  match t with | GTrivial -> GTrivial | uu___ -> GCtx (ds, cs, t)
let gbranch (ts : goal_tree Prims.list) : goal_tree=
  let uu___ =
    FStarC_List.filter
      (fun uu___1 -> match uu___1 with | GTrivial -> false | uu___2 -> true)
      ts in
  match uu___ with | [] -> GTrivial | t::[] -> t | ts1 -> GBranch ts1
let rec goals_of (t : goal_tree) : goal Prims.list=
  match t with
  | GTrivial -> []
  | GLeaf g -> [g]
  | GCtx (uu___, uu___1, t1) -> goals_of t1
  | GBranch ts -> FStarC_List.collect goals_of ts
let goal_context (t : goal_tree) (g : goal) : ctx_elt Prims.list=
  let rec aux t1 =
    match t1 with
    | GTrivial -> FStar_Pervasives_Native.None
    | GLeaf g' ->
        if g'.goal_id = g.goal_id
        then FStar_Pervasives_Native.Some []
        else FStar_Pervasives_Native.None
    | GCtx (uu___, cs, t2) ->
        let uu___1 = aux t2 in
        FStarC_Option.map (fun cs' -> FStarC_List.op_At cs cs') uu___1
    | GBranch ts ->
        FStarC_List.fold_left
          (fun acc t2 ->
             match acc with
             | FStar_Pervasives_Native.Some uu___ -> acc
             | FStar_Pervasives_Native.None -> aux t2)
          FStar_Pervasives_Native.None ts in
  let uu___ = aux t in FStarC_Option.dflt [] uu___
let rec all_decls (t : goal_tree) : FStarC_SMTEncoding_Term.decl Prims.list=
  match t with
  | GTrivial -> []
  | GLeaf g ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 =
              FStarC_Class_Show.show FStarC_Class_Show.showable_int g.goal_id in
            Prims.strcat "@goal_" uu___3 in
          ((g.goal_term), FStar_Pervasives_Native.None, uu___2) in
        FStarC_SMTEncoding_Util.mkAssume uu___1 in
      [uu___]
  | GCtx (ds, uu___, t1) ->
      let uu___1 = all_decls t1 in FStarC_List.op_At ds uu___1
  | GBranch ts -> FStarC_List.collect all_decls ts
let quantifier_free (t : FStarC_SMTEncoding_Term.term) : Prims.bool=
  let budget = FStarC_Effect.mk_ref (Prims.of_int 200) in
  let rec aux t1 =
    let uu___ =
      let uu___1 = FStarC_Effect.op_Bang budget in uu___1 <= Prims.int_zero in
    if uu___
    then false
    else
      ((let uu___2 =
          let uu___3 = FStarC_Effect.op_Bang budget in uu___3 - Prims.int_one in
        FStarC_Effect.op_Colon_Equals budget uu___2);
       (match t1 with
        | FStarC_SMTEncoding_Term.Quant
            (uu___2, uu___3, uu___4, uu___5, uu___6, uu___7) -> false
        | FStarC_SMTEncoding_Term.App (uu___2, tms, uu___3) ->
            FStarC_List.for_all aux tms
        | FStarC_SMTEncoding_Term.Let (tms, t2) ->
            let uu___2 = FStarC_List.for_all aux tms in
            if uu___2 then aux t2 else false
        | FStarC_SMTEncoding_Term.Labeled (t2, uu___2, uu___3) -> aux t2
        | uu___2 -> true)) in
  aux t
let destruct_label (q : FStarC_Syntax_Syntax.term) :
  (FStarC_Syntax_Syntax.term * FStarC_Errors_Msg.error_message *
    FStarC_Range_Type.t) FStar_Pervasives_Native.option=
  let uu___ =
    let uu___1 = FStarC_Syntax_Subst.compress q in
    uu___1.FStarC_Syntax_Syntax.n in
  match uu___ with
  | FStarC_Syntax_Syntax.Tm_meta
      { FStarC_Syntax_Syntax.tm2 = tm;
        FStarC_Syntax_Syntax.meta = FStarC_Syntax_Syntax.Meta_labeled
          (msg, r, uu___1);_}
      -> FStar_Pervasives_Native.Some (tm, msg, r)
  | FStarC_Syntax_Syntax.Tm_app uu___1 ->
      let uu___2 = FStarC_Syntax_Util.head_and_args_full q in
      (match uu___2 with
       | (head, args) ->
           let uu___3 =
             let uu___4 =
               let uu___5 = FStarC_Syntax_Util.un_uinst head in
               uu___5.FStarC_Syntax_Syntax.n in
             (uu___4, args) in
           (match uu___3 with
            | (FStarC_Syntax_Syntax.Tm_fvar fv,
               (r, uu___4)::(msg, uu___5)::(phi, uu___6)::[]) when
                FStarC_Syntax_Syntax.fv_eq_lid fv
                  FStarC_Parser_Const.labeled_lid
                ->
                let uu___7 =
                  let uu___8 =
                    FStarC_Syntax_Embeddings_Base.try_unembed
                      FStarC_Syntax_Embeddings.e_range r
                      FStarC_Syntax_Embeddings_Base.id_norm_cb in
                  let uu___9 =
                    FStarC_Syntax_Embeddings_Base.try_unembed
                      FStarC_Syntax_Embeddings.e_string msg
                      FStarC_Syntax_Embeddings_Base.id_norm_cb in
                  (uu___8, uu___9) in
                (match uu___7 with
                 | (FStar_Pervasives_Native.Some r1,
                    FStar_Pervasives_Native.Some s) ->
                     FStar_Pervasives_Native.Some
                       (phi, (FStarC_Errors_Msg.mkmsg s), r1)
                 | (FStar_Pervasives_Native.None,
                    FStar_Pervasives_Native.Some s) ->
                     FStar_Pervasives_Native.Some
                       (phi, (FStarC_Errors_Msg.mkmsg s),
                         (phi.FStarC_Syntax_Syntax.pos))
                 | uu___8 -> FStar_Pervasives_Native.None)
            | uu___4 -> FStar_Pervasives_Native.None))
  | uu___1 -> FStar_Pervasives_Native.None
let destruct_transparent (q : FStarC_Syntax_Syntax.term) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  let uu___ =
    let uu___1 = FStarC_Syntax_Subst.compress q in
    uu___1.FStarC_Syntax_Syntax.n in
  match uu___ with
  | FStarC_Syntax_Syntax.Tm_app uu___1 ->
      let uu___2 = FStarC_Syntax_Util.head_and_args_full q in
      (match uu___2 with
       | (head, args) ->
           let uu___3 =
             let uu___4 =
               let uu___5 = FStarC_Syntax_Util.un_uinst head in
               uu___5.FStarC_Syntax_Syntax.n in
             (uu___4, args) in
           (match uu___3 with
            | (FStarC_Syntax_Syntax.Tm_fvar fv, uu___4::(phi, uu___5)::[])
                when
                FStarC_Syntax_Syntax.fv_eq_lid fv
                  FStarC_Parser_Const.by_tactic_lid
                -> FStar_Pervasives_Native.Some phi
            | (FStarC_Syntax_Syntax.Tm_fvar fv,
               uu___4::uu___5::(phi, uu___6)::[]) when
                FStarC_Syntax_Syntax.fv_eq_lid fv
                  FStarC_Parser_Const.rewrite_by_tactic_lid
                -> FStar_Pervasives_Native.Some phi
            | (FStarC_Syntax_Syntax.Tm_fvar fv, (phi, uu___4)::[]) when
                FStarC_Syntax_Syntax.fv_eq_lid fv
                  FStarC_Parser_Const.squash_lid
                -> FStar_Pervasives_Native.Some phi
            | uu___4 -> FStar_Pervasives_Native.None))
  | uu___1 -> FStar_Pervasives_Native.None
let rec collect_conjuncts (q : FStarC_Syntax_Syntax.term) :
  FStarC_Syntax_Syntax.term Prims.list=
  let uu___ =
    let uu___1 =
      let uu___2 = destruct_label q in
      match uu___2 with
      | FStar_Pervasives_Native.Some v -> true
      | uu___3 -> false in
    if uu___1
    then true
    else
      (let uu___2 = destruct_transparent q in
       match uu___2 with
       | FStar_Pervasives_Native.Some v -> true
       | uu___3 -> false) in
  if uu___
  then [q]
  else
    (let uu___1 = FStarC_Syntax_Formula.destruct_typ_as_formula q in
     match uu___1 with
     | FStar_Pervasives_Native.Some (FStarC_Syntax_Formula.BaseConn
         (lid, (p1, uu___2)::(p2, uu___3)::[])) when
         FStarC_Ident.lid_equals lid FStarC_Parser_Const.and_lid ->
         let uu___4 = collect_conjuncts p1 in
         let uu___5 = collect_conjuncts p2 in FStarC_List.op_At uu___4 uu___5
     | uu___2 -> [q])
let split_goals
  (use_env_msg : (unit -> Prims.string) FStar_Pervasives_Native.option)
  (env : FStarC_SMTEncoding_Env.env_t) (q : FStarC_Syntax_Syntax.term) :
  (goal_tree * FStarC_SMTEncoding_Term.decls_t)=
  let ctr = FStarC_Effect.mk_ref Prims.int_zero in
  let name_ctr = FStarC_Effect.mk_ref Prims.int_zero in
  let fresh_name prefix =
    (let uu___1 =
       let uu___2 = FStarC_Effect.op_Bang name_ctr in uu___2 + Prims.int_one in
     FStarC_Effect.op_Colon_Equals name_ctr uu___1);
    (let uu___1 =
       let uu___2 = FStarC_Effect.op_Bang name_ctr in
       FStarC_Class_Show.show FStarC_Class_Show.showable_int uu___2 in
     Prims.strcat prefix uu___1) in
  let uu___ =
    match use_env_msg with
    | FStar_Pervasives_Native.None -> (false, FStar_Pprint.empty)
    | FStar_Pervasives_Native.Some f ->
        let uu___1 = let uu___2 = f () in FStar_Pprint.doc_of_string uu___2 in
        (true, uu___1) in
  match uu___ with
  | (flag, msg_prefix) ->
      let hyp t =
        let uu___1 =
          let uu___2 = fresh_name "@hypothesis_" in
          (t, FStar_Pervasives_Native.None, uu___2) in
        FStarC_SMTEncoding_Util.mkAssume uu___1 in
      let mk_leaf env1 msg ropt q1 =
        let uu___1 = FStarC_SMTEncoding_EncodeTerm.encode_formula q1 env1 in
        match uu___1 with
        | (t, decls) ->
            (match t with
             | FStarC_SMTEncoding_Term.App
                 (FStarC_SMTEncoding_Term.TrueOp, [], uu___2) ->
                 (GTrivial, decls)
             | uu___2 ->
                 let msg1 =
                   if flag
                   then
                     (FStar_Pprint.op_Hat_Hat
                        (FStarC_Errors_Msg.text
                           "Failed to verify implicit argument: ") msg_prefix)
                     :: msg
                   else msg in
                 let rng = q1.FStarC_Syntax_Syntax.pos in
                 let rng1 =
                   match ropt with
                   | FStar_Pervasives_Native.None -> rng
                   | FStar_Pervasives_Native.Some r ->
                       let uu___3 =
                         FStarC_Range_Ops.rng_included
                           (FStarC_Range_Type.use_range rng)
                           (FStarC_Range_Type.use_range r) in
                       if uu___3
                       then rng
                       else
                         FStarC_Range_Type.set_def_range r
                           (FStarC_Range_Type.def_range rng) in
                 ((let uu___4 =
                     let uu___5 = FStarC_Effect.op_Bang ctr in
                     uu___5 + Prims.int_one in
                   FStarC_Effect.op_Colon_Equals ctr uu___4);
                  (let uu___4 =
                     let uu___5 =
                       let uu___6 = FStarC_Effect.op_Bang ctr in
                       {
                         goal_id = uu___6;
                         goal_msg = msg1;
                         goal_range = rng1;
                         goal_term = t;
                         goal_source = q1
                       } in
                     GLeaf uu___5 in
                   (uu___4, decls)))) in
      let rec aux env1 default_msg ropt q1 =
        let q2 = FStarC_Syntax_Util.unascribe q1 in
        let uu___1 = destruct_label q2 in
        match uu___1 with
        | FStar_Pervasives_Native.Some (phi, msg, r) ->
            let msg1 =
              match msg with
              | d::[] when
                  let uu___2 = FStarC_Errors_Msg.renderdoc d in
                  uu___2 = "Could not prove post-condition" -> default_msg
              | uu___2 -> msg in
            aux env1 msg1 (FStar_Pervasives_Native.Some r) phi
        | FStar_Pervasives_Native.None ->
            let uu___2 = destruct_transparent q2 in
            (match uu___2 with
             | FStar_Pervasives_Native.Some phi ->
                 aux env1 default_msg ropt phi
             | FStar_Pervasives_Native.None ->
                 let uu___3 =
                   FStarC_Syntax_Formula.destruct_typ_as_formula q2 in
                 (match uu___3 with
                  | FStar_Pervasives_Native.Some
                      (FStarC_Syntax_Formula.BaseConn (lid, [])) when
                      FStarC_Ident.lid_equals lid
                        FStarC_Parser_Const.true_lid
                      -> (GTrivial, [], true)
                  | FStar_Pervasives_Native.Some
                      (FStarC_Syntax_Formula.BaseConn
                      (lid, uu___4::uu___5::[])) when
                      FStarC_Ident.lid_equals lid FStarC_Parser_Const.and_lid
                      ->
                      let rec seq cs =
                        match cs with
                        | [] -> (GTrivial, [], true)
                        | c::[] -> aux env1 default_msg ropt c
                        | c::cs1 ->
                            let uu___6 = aux env1 default_msg ropt c in
                            (match uu___6 with
                             | (t, decls, ok) ->
                                 let uu___7 = seq cs1 in
                                 (match uu___7 with
                                  | (rest, decls', ok') ->
                                      let uu___8 =
                                        if
                                          ok &&
                                            (Prims.not
                                               (match rest with
                                                | GTrivial -> true
                                                | uu___9 -> false))
                                        then
                                          let uu___9 =
                                            FStarC_SMTEncoding_EncodeTerm.encode_formula
                                              c env1 in
                                          match uu___9 with
                                          | (e, decls'') ->
                                              let uu___10 = quantifier_free e in
                                              (if uu___10
                                               then
                                                 let uu___11 =
                                                   let uu___12 =
                                                     let uu___13 = hyp e in
                                                     [uu___13] in
                                                   gctx uu___12 [CHyp c] rest in
                                                 (uu___11, decls'')
                                               else (rest, decls''))
                                        else (rest, []) in
                                      (match uu___8 with
                                       | (rest1, decls'') ->
                                           let uu___9 = gbranch [t; rest1] in
                                           (uu___9,
                                             (FStarC_List.op_At decls
                                                (FStarC_List.op_At decls'
                                                   decls'')), (ok && ok'))))) in
                      let uu___6 = collect_conjuncts q2 in seq uu___6
                  | FStar_Pervasives_Native.Some
                      (FStarC_Syntax_Formula.BaseConn
                      (lid, (lhs, uu___4)::(rhs, uu___5)::[])) when
                      FStarC_Ident.lid_equals lid FStarC_Parser_Const.imp_lid
                      ->
                      let uu___6 = aux env1 default_msg ropt rhs in
                      (match uu___6 with
                       | (t, decls, ok) ->
                           (match t with
                            | GTrivial -> (GTrivial, decls, ok)
                            | uu___7 ->
                                let uu___8 =
                                  FStarC_SMTEncoding_EncodeTerm.encode_formula
                                    lhs env1 in
                                (match uu___8 with
                                 | (l, decls') ->
                                     let uu___9 =
                                       let uu___10 =
                                         let uu___11 = hyp l in [uu___11] in
                                       gctx uu___10 [CHyp lhs] t in
                                     (uu___9,
                                       (FStarC_List.op_At decls decls'), ok))))
                  | FStar_Pervasives_Native.Some
                      (FStarC_Syntax_Formula.BaseConn
                      (lid, (g, uu___4)::(th, uu___5)::(el, uu___6)::[]))
                      when
                      FStarC_Ident.lid_equals lid FStarC_Parser_Const.ite_lid
                      ->
                      let uu___7 = aux env1 default_msg ropt th in
                      (match uu___7 with
                       | (t1, decls1, ok1) ->
                           let uu___8 = aux env1 default_msg ropt el in
                           (match uu___8 with
                            | (t2, decls2, ok2) ->
                                (match (t1, t2) with
                                 | (GTrivial, GTrivial) ->
                                     (GTrivial,
                                       (FStarC_List.op_At decls1 decls2),
                                       (ok1 && ok2))
                                 | uu___9 ->
                                     let uu___10 =
                                       FStarC_SMTEncoding_EncodeTerm.encode_formula
                                         g env1 in
                                     (match uu___10 with
                                      | (ge, decls3) ->
                                          let uu___11 =
                                            let uu___12 =
                                              let uu___13 =
                                                let uu___14 =
                                                  let uu___15 = hyp ge in
                                                  [uu___15] in
                                                gctx uu___14 [CHyp g] t1 in
                                              let uu___14 =
                                                let uu___15 =
                                                  let uu___16 =
                                                    let uu___17 =
                                                      let uu___18 =
                                                        FStarC_SMTEncoding_Util.mkNot
                                                          ge in
                                                      hyp uu___18 in
                                                    [uu___17] in
                                                  let uu___17 =
                                                    let uu___18 =
                                                      let uu___19 =
                                                        FStarC_Syntax_Util.mk_neg
                                                          g in
                                                      CHyp uu___19 in
                                                    [uu___18] in
                                                  gctx uu___16 uu___17 t2 in
                                                [uu___15] in
                                              uu___13 :: uu___14 in
                                            gbranch uu___12 in
                                          (uu___11,
                                            (FStarC_List.op_At decls1
                                               (FStarC_List.op_At decls2
                                                  decls3)), (ok1 && ok2))))))
                  | FStar_Pervasives_Native.Some (FStarC_Syntax_Formula.QAll
                      (bs, _pats, body)) ->
                      let uu___4 =
                        FStarC_List.fold_left
                          (fun uu___5 b ->
                             match uu___5 with
                             | (vars, guards, env2, decls, names) ->
                                 let x = b.FStarC_Syntax_Syntax.binder_bv in
                                 let fv =
                                   let uu___6 =
                                     let uu___7 = fresh_name "@sk_" in
                                     (uu___7,
                                       FStarC_SMTEncoding_Term.Term_sort) in
                                   FStarC_SMTEncoding_Term.mk_fv uu___6 in
                                 let env' =
                                   let uu___6 =
                                     FStarC_SMTEncoding_Util.mkFreeV fv in
                                   FStarC_SMTEncoding_Env.push_term_var env2
                                     x uu___6 in
                                 let uu___6 =
                                   let uu___7 =
                                     FStarC_SMTEncoding_EncodeTerm.norm env2
                                       x.FStarC_Syntax_Syntax.sort in
                                   let uu___8 =
                                     FStarC_SMTEncoding_Util.mkFreeV fv in
                                   FStarC_SMTEncoding_EncodeTerm.encode_term_pred
                                     FStar_Pervasives_Native.None uu___7 env2
                                     uu___8 in
                                 (match uu___6 with
                                  | (g, decls') ->
                                      ((fv :: vars), (g :: guards), env',
                                        (FStarC_List.op_At decls decls'), (x
                                        :: names)))) ([], [], env1, [], [])
                          bs in
                      (match uu___4 with
                       | (vars, guards, env', decls, names) ->
                           let uu___5 =
                             ((FStarC_List.rev vars),
                               (FStarC_List.rev guards),
                               (FStarC_List.rev names)) in
                           (match uu___5 with
                            | (vars1, guards1, names1) ->
                                let uu___6 = aux env' default_msg ropt body in
                                (match uu___6 with
                                 | (t, decls', ok) ->
                                     let ds =
                                       let uu___7 =
                                         FStarC_List.map
                                           (fun fv ->
                                              FStarC_SMTEncoding_Term.DeclFun
                                                ((FStarC_SMTEncoding_Term.fv_name
                                                    fv), [],
                                                  (FStarC_SMTEncoding_Term.fv_sort
                                                     fv),
                                                  FStar_Pervasives_Native.None))
                                           vars1 in
                                       let uu___8 =
                                         let uu___9 =
                                           FStarC_List.filter
                                             (fun uu___10 ->
                                                match uu___10 with
                                                | FStarC_SMTEncoding_Term.App
                                                    (FStarC_SMTEncoding_Term.TrueOp,
                                                     [], uu___11)
                                                    -> false
                                                | uu___11 -> true) guards1 in
                                         FStarC_List.map hyp uu___9 in
                                       FStarC_List.op_At uu___7 uu___8 in
                                     let uu___7 =
                                       let uu___8 =
                                         FStarC_List.map
                                           (fun uu___9 -> CVar uu___9) names1 in
                                       gctx ds uu___8 t in
                                     (uu___7,
                                       (FStarC_List.op_At decls decls'), ok))))
                  | uu___4 ->
                      let uu___5 =
                        let uu___6 = FStarC_Syntax_Subst.compress q2 in
                        uu___6.FStarC_Syntax_Syntax.n in
                      (match uu___5 with
                       | FStarC_Syntax_Syntax.Tm_match
                           { FStarC_Syntax_Syntax.scrutinee = e;
                             FStarC_Syntax_Syntax.ret_opt = uu___6;
                             FStarC_Syntax_Syntax.brs = brs;
                             FStarC_Syntax_Syntax.rc_opt1 = uu___7;_}
                           ->
                           let scrsym = fresh_name "@sk_" in
                           let scr' =
                             FStarC_SMTEncoding_Util.mkFreeV
                               (FStarC_SMTEncoding_Term.mk_fv
                                  (scrsym, FStarC_SMTEncoding_Term.Term_sort)) in
                           let uu___8 =
                             FStarC_SMTEncoding_EncodeTerm.encode_term e env1 in
                           (match uu___8 with
                            | (scr, decls0) ->
                                let env' = env1 in
                                let rec go negs brs1 =
                                  match brs1 with
                                  | [] -> (GTrivial, [], false)
                                  | b::brs2 ->
                                      let uu___9 =
                                        FStarC_SMTEncoding_EncodeTerm.encode_branch_pattern
                                          env' scr' b in
                                      (match uu___9 with
                                       | (guard, p, br, envb, declsb) ->
                                           let uu___10 =
                                             aux envb default_msg ropt br in
                                           (match uu___10 with
                                            | (t, declst, ok) ->
                                                let uu___11 =
                                                  let uu___12 =
                                                    let uu___13 =
                                                      FStarC_SMTEncoding_Util.mkNot
                                                        guard in
                                                    uu___13 :: negs in
                                                  go uu___12 brs2 in
                                                (match uu___11 with
                                                 | (rest, declsr, ok') ->
                                                     let uu___12 =
                                                       let uu___13 =
                                                         let uu___14 =
                                                           let uu___15 =
                                                             let uu___16 =
                                                               let uu___17 =
                                                                 FStarC_SMTEncoding_Util.mk_and_l
                                                                   (FStarC_List.rev
                                                                    (guard ::
                                                                    negs)) in
                                                               hyp uu___17 in
                                                             [uu___16] in
                                                           gctx uu___15
                                                             [CMatch (e, p)]
                                                             t in
                                                         [uu___14; rest] in
                                                       gbranch uu___13 in
                                                     (uu___12,
                                                       (FStarC_List.op_At
                                                          declsb
                                                          (FStarC_List.op_At
                                                             declst declsr)),
                                                       (ok && ok'))))) in
                                let uu___9 = go [] brs in
                                (match uu___9 with
                                 | (t, decls, ok) ->
                                     let uu___10 =
                                       let uu___11 =
                                         let uu___12 =
                                           let uu___13 =
                                             let uu___14 =
                                               FStarC_SMTEncoding_Util.mkEq
                                                 (scr', scr) in
                                             hyp uu___14 in
                                           [uu___13] in
                                         (FStarC_SMTEncoding_Term.DeclFun
                                            (scrsym, [],
                                              FStarC_SMTEncoding_Term.Term_sort,
                                              FStar_Pervasives_Native.None))
                                           :: uu___12 in
                                       gctx uu___11 [] t in
                                     (uu___10,
                                       (FStarC_List.op_At decls0 decls), ok)))
                       | FStarC_Syntax_Syntax.Tm_let
                           {
                             FStarC_Syntax_Syntax.lbs =
                               (false,
                                {
                                  FStarC_Syntax_Syntax.lbname =
                                    FStar_Pervasives.Inl x;
                                  FStarC_Syntax_Syntax.lbunivs = uu___6;
                                  FStarC_Syntax_Syntax.lbtyp = t1;
                                  FStarC_Syntax_Syntax.lbeff = uu___7;
                                  FStarC_Syntax_Syntax.lbdef = e1;
                                  FStarC_Syntax_Syntax.lbattrs = uu___8;
                                  FStarC_Syntax_Syntax.lbpos = uu___9;_}::[]);
                             FStarC_Syntax_Syntax.body1 = e2;_}
                           ->
                           let uu___10 =
                             let uu___11 =
                               FStarC_Syntax_Util.ascribe e1
                                 ((FStar_Pervasives.Inl t1),
                                   FStar_Pervasives_Native.None, false) in
                             FStarC_SMTEncoding_EncodeTerm.encode_term
                               uu___11 env1 in
                           (match uu___10 with
                            | (ee1, decls1) ->
                                let uu___11 =
                                  FStarC_Syntax_Subst.open_term
                                    [FStarC_Syntax_Syntax.mk_binder x] e2 in
                                (match uu___11 with
                                 | (xs, e21) ->
                                     let x1 =
                                       (FStarC_List.hd xs).FStarC_Syntax_Syntax.binder_bv in
                                     let env' =
                                       FStarC_SMTEncoding_Env.push_term_var
                                         env1 x1 ee1 in
                                     let uu___12 =
                                       aux env' default_msg ropt e21 in
                                     (match uu___12 with
                                      | (t, decls2, ok) ->
                                          ((gctx [] [CDef (x1, e1)] t),
                                            (FStarC_List.op_At decls1 decls2),
                                            ok))))
                       | FStarC_Syntax_Syntax.Tm_meta
                           { FStarC_Syntax_Syntax.tm2 = tm;
                             FStarC_Syntax_Syntax.meta = uu___6;_}
                           -> aux env1 default_msg ropt tm
                       | uu___6 ->
                           let uu___7 = mk_leaf env1 default_msg ropt q2 in
                           (match uu___7 with
                            | (t, decls) -> (t, decls, true))))) in
      let uu___1 =
        aux env (FStarC_Errors_Msg.mkmsg "Assertion failed")
          FStar_Pervasives_Native.None q in
      (match uu___1 with | (t, decls, uu___2) -> (t, decls))
