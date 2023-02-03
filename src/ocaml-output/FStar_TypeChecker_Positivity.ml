open Prims
let (debug_positivity :
  FStar_TypeChecker_Env.env_t -> (unit -> Prims.string) -> unit) =
  fun env ->
    fun msg ->
      let uu___ =
        FStar_Compiler_Effect.op_Less_Bar (FStar_TypeChecker_Env.debug env)
          (FStar_Options.Other "Positivity") in
      if uu___
      then
        let uu___1 =
          let uu___2 = let uu___3 = msg () in Prims.op_Hat uu___3 "\n" in
          Prims.op_Hat "Positivity::" uu___2 in
        FStar_Compiler_Util.print_string uu___1
      else ()
let (apply_datacon_arrow :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.arg Prims.list -> FStar_Syntax_Syntax.term)
  =
  fun dlid ->
    fun dt ->
      fun all_params ->
        let rec aux t args =
          let uu___ =
            let uu___1 =
              let uu___2 = FStar_Syntax_Subst.compress t in
              uu___2.FStar_Syntax_Syntax.n in
            (uu___1, args) in
          match uu___ with
          | (uu___1, []) -> t
          | (FStar_Syntax_Syntax.Tm_arrow (b::bs, c), a::args1) ->
              let tail =
                FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                  t.FStar_Syntax_Syntax.pos in
              let uu___1 = FStar_Syntax_Subst.open_term_1 b tail in
              (match uu___1 with
               | (b1, tail1) ->
                   let tail2 =
                     FStar_Syntax_Subst.subst
                       [FStar_Syntax_Syntax.NT
                          ((b1.FStar_Syntax_Syntax.binder_bv),
                            (FStar_Pervasives_Native.fst a))] tail1 in
                   aux tail2 args1)
          | uu___1 ->
              let uu___2 =
                let uu___3 =
                  let uu___4 = FStar_Syntax_Print.args_to_string all_params in
                  let uu___5 = FStar_Ident.string_of_lid dlid in
                  let uu___6 = FStar_Syntax_Print.term_to_string dt in
                  FStar_Compiler_Util.format3
                    "Unexpected application of type parameters %s to a data constructor %s : %s"
                    uu___4 uu___5 uu___6 in
                (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                  uu___3) in
              let uu___3 = FStar_Ident.range_of_lid dlid in
              FStar_Errors.raise_error uu___2 uu___3 in
        aux dt all_params
let (ty_occurs_in :
  FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun ty_lid ->
    fun t ->
      let uu___ = FStar_Syntax_Free.fvars t in
      FStar_Compiler_Util.set_mem ty_lid uu___
let rec (term_as_fv_or_name :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universes),
      FStar_Syntax_Syntax.bv) FStar_Pervasives.either
      FStar_Pervasives_Native.option)
  =
  fun t ->
    let uu___ =
      let uu___1 = FStar_Syntax_Subst.compress t in
      uu___1.FStar_Syntax_Syntax.n in
    match uu___ with
    | FStar_Syntax_Syntax.Tm_name x ->
        FStar_Pervasives_Native.Some (FStar_Pervasives.Inr x)
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Pervasives_Native.Some (FStar_Pervasives.Inl (fv, []))
    | FStar_Syntax_Syntax.Tm_uinst (t1, us) ->
        let uu___1 =
          let uu___2 = FStar_Syntax_Subst.compress t1 in
          uu___2.FStar_Syntax_Syntax.n in
        (match uu___1 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Pervasives_Native.Some (FStar_Pervasives.Inl (fv, us))
         | uu___2 ->
             failwith "term_as_fv_or_name: impossible non fvar in uinst")
    | FStar_Syntax_Syntax.Tm_ascribed (t1, uu___1, uu___2) ->
        term_as_fv_or_name t1
    | uu___1 -> FStar_Pervasives_Native.None
type unfolded_memo_elt =
  (FStar_Ident.lident * FStar_Syntax_Syntax.args * Prims.int) Prims.list
type unfolded_memo_t = unfolded_memo_elt FStar_Compiler_Effect.ref
let (already_unfolded :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.args ->
      unfolded_memo_t -> FStar_TypeChecker_Env.env_t -> Prims.bool)
  =
  fun ilid ->
    fun args ->
      fun unfolded ->
        fun env ->
          let uu___ = FStar_Compiler_Effect.op_Bang unfolded in
          FStar_Compiler_List.existsML
            (fun uu___1 ->
               match uu___1 with
               | (lid, l, n) ->
                   ((FStar_Ident.lid_equals lid ilid) &&
                      ((FStar_Compiler_List.length args) >= n))
                     &&
                     (let args1 =
                        let uu___2 = FStar_Compiler_List.splitAt n args in
                        FStar_Pervasives_Native.fst uu___2 in
                      FStar_Compiler_List.fold_left2
                        (fun b ->
                           fun a ->
                             fun a' ->
                               b &&
                                 (FStar_TypeChecker_Rel.teq_nosmt_force env
                                    (FStar_Pervasives_Native.fst a)
                                    (FStar_Pervasives_Native.fst a'))) true
                        args1 l)) uu___
let rec (ty_strictly_positive_in_type :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident Prims.list ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.term -> unfolded_memo_t -> Prims.bool)
  =
  fun env ->
    fun mutuals ->
      fun ty_lid ->
        fun in_type ->
          fun unfolded ->
            debug_positivity env
              (fun uu___1 ->
                 let uu___2 = FStar_Syntax_Print.term_to_string in_type in
                 Prims.op_Hat "Checking strict positivity in type: " uu___2);
            (let in_type1 =
               FStar_TypeChecker_Normalize.normalize
                 [FStar_TypeChecker_Env.Beta;
                 FStar_TypeChecker_Env.HNF;
                 FStar_TypeChecker_Env.Weak;
                 FStar_TypeChecker_Env.Iota;
                 FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                 FStar_TypeChecker_Env.UnfoldUntil
                   FStar_Syntax_Syntax.delta_constant] env in_type in
             debug_positivity env
               (fun uu___2 ->
                  let uu___3 = FStar_Syntax_Print.term_to_string in_type1 in
                  Prims.op_Hat
                    "Checking strict positivity in type, after normalization: "
                    uu___3);
             (let uu___2 =
                let uu___3 = ty_occurs_in ty_lid in_type1 in
                Prims.op_Negation uu___3 in
              if uu___2
              then true
              else
                (debug_positivity env
                   (fun uu___5 -> "ty does occur in this type");
                 (let uu___5 =
                    let uu___6 = FStar_Syntax_Subst.compress in_type1 in
                    uu___6.FStar_Syntax_Syntax.n in
                  match uu___5 with
                  | FStar_Syntax_Syntax.Tm_fvar uu___6 ->
                      (debug_positivity env
                         (fun uu___8 ->
                            "Checking strict positivity in an fvar/Tm_uinst/Tm_type, return true");
                       true)
                  | FStar_Syntax_Syntax.Tm_uinst uu___6 ->
                      (debug_positivity env
                         (fun uu___8 ->
                            "Checking strict positivity in an fvar/Tm_uinst/Tm_type, return true");
                       true)
                  | FStar_Syntax_Syntax.Tm_type uu___6 ->
                      (debug_positivity env
                         (fun uu___8 ->
                            "Checking strict positivity in an fvar/Tm_uinst/Tm_type, return true");
                       true)
                  | FStar_Syntax_Syntax.Tm_ascribed (t, uu___6, uu___7) ->
                      ty_strictly_positive_in_type env mutuals ty_lid t
                        unfolded
                  | FStar_Syntax_Syntax.Tm_meta (t, uu___6) ->
                      ty_strictly_positive_in_type env mutuals ty_lid t
                        unfolded
                  | FStar_Syntax_Syntax.Tm_app (t, args) ->
                      let fv_or_name_opt = term_as_fv_or_name t in
                      (match fv_or_name_opt with
                       | FStar_Pervasives_Native.None ->
                           (debug_positivity env
                              (fun uu___7 ->
                                 let uu___8 =
                                   FStar_Ident.string_of_lid ty_lid in
                                 let uu___9 =
                                   FStar_Syntax_Print.term_to_string t in
                                 FStar_Compiler_Util.format2
                                   "Failed to check positivity of %s in a term with head %s"
                                   uu___8 uu___9);
                            false)
                       | FStar_Pervasives_Native.Some (FStar_Pervasives.Inr
                           uu___6) ->
                           (debug_positivity env
                              (fun uu___8 ->
                                 "ty is an app node with head that is a bv");
                            (let uu___8 =
                               env.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                 env t (let must_tot = false in must_tot) in
                             match uu___8 with
                             | (head_ty, uu___9) ->
                                 check_ty_strictly_positive_in_args env
                                   mutuals ty_lid head_ty args unfolded))
                       | FStar_Pervasives_Native.Some (FStar_Pervasives.Inl
                           (fv, us)) ->
                           let uu___6 =
                             (FStar_Ident.lid_equals
                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                ty_lid)
                               ||
                               (FStar_Compiler_List.existsML
                                  (FStar_Ident.lid_equals
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                  mutuals) in
                           if uu___6
                           then
                             (debug_positivity env
                                (fun uu___8 ->
                                   let uu___9 =
                                     FStar_Ident.string_of_lid ty_lid in
                                   FStar_Compiler_Util.format1
                                     "Checking strict positivity in the Tm_app node where head lid is %s itself, checking that ty does not occur in the arguments"
                                     uu___9);
                              FStar_Compiler_List.for_all
                                (fun uu___8 ->
                                   match uu___8 with
                                   | (t1, uu___9) ->
                                       let uu___10 = ty_occurs_in ty_lid t1 in
                                       Prims.op_Negation uu___10) args)
                           else
                             (debug_positivity env
                                (fun uu___9 ->
                                   let uu___10 =
                                     FStar_Ident.string_of_lid ty_lid in
                                   FStar_Compiler_Util.format1
                                     "Checking strict positivity in the Tm_app node, head lid is not %s, so checking nested positivity"
                                     uu___10);
                              ty_strictly_positive_in_arguments_to_fvar env
                                mutuals ty_lid
                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                us args unfolded))
                  | FStar_Syntax_Syntax.Tm_arrow (uu___6, c) ->
                      (debug_positivity env
                         (fun uu___8 ->
                            "Checking strict positivity in Tm_arrow");
                       (let check_comp =
                          (FStar_Syntax_Util.is_pure_or_ghost_comp c) ||
                            (let uu___8 =
                               let uu___9 =
                                 let uu___10 =
                                   FStar_Compiler_Effect.op_Bar_Greater c
                                     FStar_Syntax_Util.comp_effect_name in
                                 FStar_Compiler_Effect.op_Bar_Greater uu___10
                                   (FStar_TypeChecker_Env.norm_eff_name env) in
                               FStar_Compiler_Effect.op_Bar_Greater uu___9
                                 (FStar_TypeChecker_Env.lookup_effect_quals
                                    env) in
                             FStar_Compiler_Effect.op_Bar_Greater uu___8
                               (FStar_Compiler_List.contains
                                  FStar_Syntax_Syntax.TotalEffect)) in
                        if Prims.op_Negation check_comp
                        then
                          (debug_positivity env
                             (fun uu___9 ->
                                "Checking strict positivity , the arrow is impure, so return true");
                           true)
                        else
                          (debug_positivity env
                             (fun uu___10 ->
                                "Checking strict positivity for an arrow, checking that ty does not occur in the binders, and that it is strictly positive in the return type");
                           (let uu___10 =
                              FStar_Syntax_Util.arrow_formals_comp in_type1 in
                            match uu___10 with
                            | (sbs, c1) ->
                                let return_type =
                                  FStar_Syntax_Util.comp_result c1 in
                                let ty_lid_not_to_left_of_arrow =
                                  FStar_Compiler_List.for_all
                                    (fun uu___11 ->
                                       match uu___11 with
                                       | { FStar_Syntax_Syntax.binder_bv = b;
                                           FStar_Syntax_Syntax.binder_qual =
                                             uu___12;
                                           FStar_Syntax_Syntax.binder_attrs =
                                             uu___13;_}
                                           ->
                                           let uu___14 =
                                             ty_occurs_in ty_lid
                                               b.FStar_Syntax_Syntax.sort in
                                           Prims.op_Negation uu___14) sbs in
                                if ty_lid_not_to_left_of_arrow
                                then
                                  let uu___11 =
                                    FStar_TypeChecker_Env.push_binders env
                                      sbs in
                                  ty_strictly_positive_in_type uu___11
                                    mutuals ty_lid return_type unfolded
                                else false))))
                  | FStar_Syntax_Syntax.Tm_refine (bv, f) ->
                      (debug_positivity env
                         (fun uu___7 ->
                            "Checking strict positivity in an Tm_refine, recur in the bv sort)");
                       (let uu___7 =
                          let uu___8 =
                            let uu___9 = FStar_Syntax_Syntax.mk_binder bv in
                            [uu___9] in
                          FStar_Syntax_Subst.open_term uu___8 f in
                        match uu___7 with
                        | (b::[], f1) ->
                            let uu___8 =
                              ty_strictly_positive_in_type env mutuals ty_lid
                                (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort
                                unfolded in
                            if uu___8
                            then
                              let env1 =
                                FStar_TypeChecker_Env.push_binders env [b] in
                              ty_strictly_positive_in_type env1 mutuals
                                ty_lid f1 unfolded
                            else false))
                  | FStar_Syntax_Syntax.Tm_match
                      (scrutinee, uu___6, branches, uu___7) ->
                      (debug_positivity env
                         (fun uu___9 ->
                            "Checking strict positivity in an Tm_match, recur in the branches)");
                       (let uu___9 =
                          FStar_Compiler_List.existsML
                            (fun mutual -> ty_occurs_in mutual scrutinee)
                            (ty_lid :: mutuals) in
                        if uu___9
                        then false
                        else
                          FStar_Compiler_List.for_all
                            (fun uu___11 ->
                               match uu___11 with
                               | (p, uu___12, t) ->
                                   let bs =
                                     let uu___13 =
                                       FStar_Syntax_Syntax.pat_bvs p in
                                     FStar_Compiler_List.map
                                       FStar_Syntax_Syntax.mk_binder uu___13 in
                                   let uu___13 =
                                     FStar_Syntax_Subst.open_term bs t in
                                   (match uu___13 with
                                    | (bs1, t1) ->
                                        let uu___14 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs1 in
                                        ty_strictly_positive_in_type uu___14
                                          mutuals ty_lid t1 unfolded))
                            branches))
                  | FStar_Syntax_Syntax.Tm_abs uu___6 ->
                      let uu___7 = FStar_Syntax_Util.abs_formals in_type1 in
                      (match uu___7 with
                       | (bs, body, uu___8) ->
                           let rec aux env1 bs1 =
                             match bs1 with
                             | [] ->
                                 ty_strictly_positive_in_type env1 mutuals
                                   ty_lid body unfolded
                             | b::bs2 ->
                                 let uu___9 =
                                   ty_strictly_positive_in_type env1 mutuals
                                     ty_lid
                                     (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort
                                     unfolded in
                                 if uu___9
                                 then
                                   let env2 =
                                     FStar_TypeChecker_Env.push_binders env1
                                       [b] in
                                   aux env2 bs2
                                 else false in
                           aux env bs)
                  | uu___6 ->
                      (debug_positivity env
                         (fun uu___8 ->
                            let uu___9 =
                              FStar_Syntax_Print.tag_of_term in_type1 in
                            let uu___10 =
                              FStar_Syntax_Print.term_to_string in_type1 in
                            FStar_Compiler_Util.format2
                              "Checking strict positivity, unexpected tag: %s and term %s"
                              uu___9 uu___10);
                       false)))))
and (check_ty_strictly_positive_in_args :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident Prims.list ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.typ ->
          FStar_Syntax_Syntax.args -> unfolded_memo_t -> Prims.bool)
  =
  fun env ->
    fun mutuals ->
      fun ty_lid ->
        fun head_t ->
          fun args ->
            fun unfolded ->
              let uu___ = FStar_Syntax_Util.arrow_formals head_t in
              match uu___ with
              | (bs, uu___1) ->
                  let rec aux bs1 args1 =
                    match (bs1, args1) with
                    | (uu___2, []) -> true
                    | ([], uu___2) ->
                        FStar_Compiler_List.for_all
                          (fun uu___3 ->
                             match uu___3 with
                             | (arg, uu___4) ->
                                 let uu___5 = ty_occurs_in ty_lid arg in
                                 Prims.op_Negation uu___5) args1
                    | (b::bs2, (arg, uu___2)::args2) ->
                        (debug_positivity env
                           (fun uu___4 ->
                              let uu___5 = FStar_Ident.string_of_lid ty_lid in
                              let uu___6 =
                                FStar_Syntax_Print.term_to_string arg in
                              let uu___7 =
                                FStar_Syntax_Print.binder_to_string b in
                              FStar_Compiler_Util.format3
                                "Checking positivity of %s in argument %s and binder %s"
                                uu___5 uu___6 uu___7);
                         (let this_occurrence_ok =
                            (let uu___4 = ty_occurs_in ty_lid arg in
                             Prims.op_Negation uu___4) ||
                              ((FStar_Syntax_Util.has_attribute
                                  b.FStar_Syntax_Syntax.binder_attrs
                                  FStar_Parser_Const.binder_strictly_positive_attr)
                                 &&
                                 (ty_strictly_positive_in_type env mutuals
                                    ty_lid arg unfolded)) in
                          if Prims.op_Negation this_occurrence_ok
                          then
                            (debug_positivity env
                               (fun uu___5 ->
                                  let uu___6 =
                                    FStar_Ident.string_of_lid ty_lid in
                                  let uu___7 =
                                    FStar_Syntax_Print.term_to_string arg in
                                  let uu___8 =
                                    FStar_Syntax_Print.binder_to_string b in
                                  FStar_Compiler_Util.format3
                                    "Failed checking positivity of %s in argument %s and binder %s"
                                    uu___6 uu___7 uu___8);
                             false)
                          else aux bs2 args2)) in
                  aux bs args
and (ty_strictly_positive_in_arguments_to_fvar :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident Prims.list ->
      FStar_Ident.lident ->
        FStar_Ident.lident ->
          FStar_Syntax_Syntax.universes ->
            FStar_Syntax_Syntax.args -> unfolded_memo_t -> Prims.bool)
  =
  fun env ->
    fun mutuals ->
      fun ty_lid ->
        fun fv ->
          fun us ->
            fun args ->
              fun unfolded ->
                debug_positivity env
                  (fun uu___1 ->
                     let uu___2 = FStar_Ident.string_of_lid ty_lid in
                     let uu___3 = FStar_Ident.string_of_lid fv in
                     let uu___4 = FStar_Syntax_Print.args_to_string args in
                     FStar_Compiler_Util.format3
                       "Checking positivity of %s in application of fv %s to %s"
                       uu___2 uu___3 uu___4);
                (let uu___1 = FStar_TypeChecker_Env.datacons_of_typ env fv in
                 match uu___1 with
                 | (b, idatas) ->
                     if Prims.op_Negation b
                     then
                       let uu___2 =
                         FStar_TypeChecker_Env.try_lookup_lid env fv in
                       (match uu___2 with
                        | FStar_Pervasives_Native.Some
                            ((uu___3, fv_ty), uu___4) ->
                            check_ty_strictly_positive_in_args env mutuals
                              ty_lid fv_ty args unfolded
                        | FStar_Pervasives_Native.None ->
                            (debug_positivity env
                               (fun uu___4 ->
                                  "Checking positivity of an application, head type not found, return false");
                             false))
                     else
                       (let ilid = fv in
                        let uu___3 = already_unfolded ilid args unfolded env in
                        if uu___3
                        then
                          (debug_positivity env
                             (fun uu___5 ->
                                "Checking nested positivity, we have already unfolded this inductive with these args");
                           true)
                        else
                          (let num_ibs =
                             let uu___5 =
                               FStar_TypeChecker_Env.num_inductive_ty_params
                                 env ilid in
                             FStar_Compiler_Option.get uu___5 in
                           let params =
                             let uu___5 =
                               FStar_Compiler_List.splitAt num_ibs args in
                             FStar_Pervasives_Native.fst uu___5 in
                           debug_positivity env
                             (fun uu___6 ->
                                let uu___7 = FStar_Ident.string_of_lid ilid in
                                let uu___8 =
                                  FStar_Syntax_Print.args_to_string params in
                                FStar_Compiler_Util.format3
                                  "Checking positivity in datacon, number of type parameters is %s, adding %s to the memo table"
                                  (Prims.string_of_int num_ibs) uu___7 uu___8);
                           (let uu___7 =
                              let uu___8 =
                                FStar_Compiler_Effect.op_Bang unfolded in
                              FStar_List_Tot_Base.op_At uu___8
                                [(ilid, params, num_ibs)] in
                            FStar_Compiler_Effect.op_Colon_Equals unfolded
                              uu___7);
                           FStar_Compiler_List.for_all
                             (fun d ->
                                ty_strictly_positive_in_datacon_of_applied_inductive
                                  env mutuals ty_lid d ilid us args num_ibs
                                  unfolded) idatas)))
and (ty_strictly_positive_in_datacon_of_applied_inductive :
  FStar_TypeChecker_Env.env_t ->
    FStar_Ident.lident Prims.list ->
      FStar_Ident.lident ->
        FStar_Ident.lident ->
          FStar_Ident.lident ->
            FStar_Syntax_Syntax.universes ->
              FStar_Syntax_Syntax.args ->
                Prims.int -> unfolded_memo_t -> Prims.bool)
  =
  fun env ->
    fun mutuals ->
      fun ty_lid ->
        fun dlid ->
          fun ilid ->
            fun us ->
              fun args ->
                fun num_ibs ->
                  fun unfolded ->
                    debug_positivity env
                      (fun uu___1 ->
                         let uu___2 = FStar_Ident.string_of_lid ty_lid in
                         let uu___3 = FStar_Ident.string_of_lid dlid in
                         let uu___4 = FStar_Ident.string_of_lid ilid in
                         FStar_Compiler_Util.format3
                           "Checking positivity of %s in data constructor %s : %s"
                           uu___2 uu___3 uu___4);
                    (let dt =
                       let uu___1 =
                         FStar_TypeChecker_Env.try_lookup_and_inst_lid env us
                           dlid in
                       match uu___1 with
                       | FStar_Pervasives_Native.Some (t, uu___2) -> t
                       | FStar_Pervasives_Native.None ->
                           let uu___2 =
                             let uu___3 =
                               let uu___4 = FStar_Ident.string_of_lid dlid in
                               FStar_Compiler_Util.format1
                                 "Data constructor %s not found when checking positivity"
                                 uu___4 in
                             (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                               uu___3) in
                           let uu___3 = FStar_Ident.range_of_lid ty_lid in
                           FStar_Errors.raise_error uu___2 uu___3 in
                     debug_positivity env
                       (fun uu___2 ->
                          let uu___3 = FStar_Syntax_Print.term_to_string dt in
                          Prims.op_Hat
                            "Checking positivity in the data constructor type: "
                            uu___3);
                     (let uu___2 = FStar_Compiler_List.splitAt num_ibs args in
                      match uu___2 with
                      | (args1, uu___3) ->
                          let applied_dt = apply_datacon_arrow dlid dt args1 in
                          let uu___4 =
                            FStar_Syntax_Util.arrow_formals applied_dt in
                          (match uu___4 with
                           | (fields, t) ->
                               (match fields with
                                | [] ->
                                    let uu___5 =
                                      FStar_Syntax_Util.head_and_args_full t in
                                    (match uu___5 with
                                     | (head, uu___6) ->
                                         let uu___7 =
                                           let uu___8 =
                                             FStar_Syntax_Util.un_uinst head in
                                           uu___8.FStar_Syntax_Syntax.n in
                                         (match uu___7 with
                                          | FStar_Syntax_Syntax.Tm_fvar fv ->
                                              let uu___8 =
                                                FStar_Ident.lid_equals
                                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                                  ilid in
                                              if uu___8 then true else false
                                          | uu___8 -> false))
                                | uu___5 ->
                                    let rec strictly_positive_in_all_fields
                                      env1 fields1 =
                                      match fields1 with
                                      | [] -> true
                                      | f::fields2 ->
                                          let uu___6 =
                                            ty_strictly_positive_in_type env1
                                              mutuals ty_lid
                                              (f.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort
                                              unfolded in
                                          if uu___6
                                          then
                                            let env2 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 [f] in
                                            strictly_positive_in_all_fields
                                              env2 fields2
                                          else false in
                                    strictly_positive_in_all_fields env
                                      fields))))
let (name_strictly_positive_in_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun env ->
    fun bv ->
      fun t ->
        let fv_lid =
          FStar_Ident.lid_of_str "__fv_lid_for_positivity_checking__" in
        let fv = FStar_Syntax_Syntax.tconst fv_lid in
        let t1 = FStar_Syntax_Subst.subst [FStar_Syntax_Syntax.NT (bv, fv)] t in
        let uu___ = FStar_Compiler_Util.mk_ref [] in
        ty_strictly_positive_in_type env [] fv_lid t1 uu___
let (ty_strictly_positive_in_datacon_decl :
  FStar_TypeChecker_Env.env_t ->
    FStar_Ident.lident Prims.list ->
      FStar_Ident.lident ->
        FStar_Ident.lident ->
          FStar_Syntax_Syntax.binders ->
            FStar_Syntax_Syntax.universes -> unfolded_memo_t -> Prims.bool)
  =
  fun env ->
    fun mutuals ->
      fun ty_lid ->
        fun dlid ->
          fun ty_bs ->
            fun us ->
              fun unfolded ->
                let dt =
                  let uu___ =
                    FStar_TypeChecker_Env.try_lookup_and_inst_lid env us dlid in
                  match uu___ with
                  | FStar_Pervasives_Native.Some (t, uu___1) -> t
                  | FStar_Pervasives_Native.None ->
                      let uu___1 =
                        let uu___2 =
                          let uu___3 = FStar_Ident.string_of_lid dlid in
                          FStar_Compiler_Util.format1
                            "Error looking up data constructor %s when checking positivity"
                            uu___3 in
                        (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                          uu___2) in
                      let uu___2 = FStar_Ident.range_of_lid ty_lid in
                      FStar_Errors.raise_error uu___1 uu___2 in
                debug_positivity env
                  (fun uu___1 ->
                     let uu___2 = FStar_Syntax_Print.term_to_string dt in
                     Prims.op_Hat "Checking data constructor type: " uu___2);
                (let raise_unexpected_type uu___1 =
                   let uu___2 =
                     let uu___3 =
                       let uu___4 = FStar_Ident.string_of_lid dlid in
                       let uu___5 = FStar_Syntax_Print.term_to_string dt in
                       FStar_Compiler_Util.format2
                         "Unexpected type for data constructor %s : %s"
                         uu___4 uu___5 in
                     (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                       uu___3) in
                   let uu___3 = FStar_Ident.range_of_lid dlid in
                   FStar_Errors.raise_error uu___2 uu___3 in
                 let check_return_type t =
                   let uu___1 = FStar_Syntax_Util.head_and_args t in
                   match uu___1 with
                   | (head, args) ->
                       let uu___2 =
                         let uu___3 = FStar_Syntax_Util.un_uinst head in
                         uu___3.FStar_Syntax_Syntax.n in
                       (match uu___2 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            let uu___3 =
                              FStar_Compiler_List.existsML
                                (FStar_Syntax_Syntax.fv_eq_lid fv) mutuals in
                            if uu___3
                            then
                              let uu___4 =
                                FStar_Compiler_List.for_all
                                  (fun mutual ->
                                     FStar_Compiler_List.for_all
                                       (fun uu___5 ->
                                          match uu___5 with
                                          | (arg, uu___6) ->
                                              let uu___7 =
                                                ty_occurs_in mutual arg in
                                              Prims.op_Negation uu___7) args)
                                  mutuals in
                              (if uu___4
                               then ()
                               else raise_unexpected_type ())
                            else raise_unexpected_type ()
                        | uu___3 -> raise_unexpected_type ()) in
                 let uu___1 = FStar_Syntax_Util.args_of_binders ty_bs in
                 match uu___1 with
                 | (ty_bs1, args) ->
                     let dt1 = apply_datacon_arrow dlid dt args in
                     let uu___2 = FStar_Syntax_Util.arrow_formals dt1 in
                     (match uu___2 with
                      | (fields, return_type) ->
                          (check_return_type return_type;
                           (let check_annotated_binders_are_strictly_positive_in_field
                              f =
                              let incorrectly_annotated_binder =
                                FStar_Compiler_List.tryFind
                                  (fun b ->
                                     let uu___4 =
                                       FStar_Syntax_Util.has_attribute
                                         b.FStar_Syntax_Syntax.binder_attrs
                                         FStar_Parser_Const.binder_strictly_positive_attr in
                                     if uu___4
                                     then
                                       let uu___5 =
                                         name_strictly_positive_in_type env
                                           b.FStar_Syntax_Syntax.binder_bv
                                           (f.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                                       Prims.op_Negation uu___5
                                     else false) ty_bs1 in
                              match incorrectly_annotated_binder with
                              | FStar_Pervasives_Native.None -> ()
                              | FStar_Pervasives_Native.Some b ->
                                  let uu___4 =
                                    let uu___5 =
                                      let uu___6 =
                                        FStar_Syntax_Print.binder_to_string b in
                                      FStar_Compiler_Util.format1
                                        "Binder %s is marked strictly positive, but its use in the definition is not"
                                        uu___6 in
                                    (FStar_Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                                      uu___5) in
                                  let uu___5 =
                                    FStar_Syntax_Syntax.range_of_bv
                                      b.FStar_Syntax_Syntax.binder_bv in
                                  FStar_Errors.raise_error uu___4 uu___5 in
                            let rec check_all_fields env1 fields1 =
                              match fields1 with
                              | [] -> true
                              | field::fields2 ->
                                  (check_annotated_binders_are_strictly_positive_in_field
                                     field;
                                   (let uu___5 =
                                      let uu___6 =
                                        ty_strictly_positive_in_type env1
                                          mutuals ty_lid
                                          (field.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort
                                          unfolded in
                                      Prims.op_Negation uu___6 in
                                    if uu___5
                                    then false
                                    else
                                      (let env2 =
                                         FStar_TypeChecker_Env.push_binders
                                           env1 [field] in
                                       check_all_fields env2 fields2))) in
                            check_all_fields env fields))))
let (check_strict_positivity :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt -> Prims.bool)
  =
  fun env ->
    fun mutuals ->
      fun ty ->
        let unfolded_inductives = FStar_Compiler_Util.mk_ref [] in
        let uu___ =
          match ty.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (lid, us, bs, uu___1, uu___2, uu___3) -> (lid, us, bs)
          | uu___1 -> failwith "Impossible!" in
        match uu___ with
        | (ty_lid, ty_us, ty_params) ->
            let mutuals1 = ty_lid :: mutuals in
            let uu___1 = FStar_Syntax_Subst.univ_var_opening ty_us in
            (match uu___1 with
             | (ty_usubst, ty_us1) ->
                 let env1 = FStar_TypeChecker_Env.push_univ_vars env ty_us1 in
                 let ty_params1 =
                   FStar_Syntax_Subst.subst_binders ty_usubst ty_params in
                 let ty_params2 = FStar_Syntax_Subst.open_binders ty_params1 in
                 let env2 =
                   FStar_TypeChecker_Env.push_binders env1 ty_params2 in
                 let datacons =
                   let uu___2 =
                     FStar_TypeChecker_Env.datacons_of_typ env2 ty_lid in
                   FStar_Pervasives_Native.snd uu___2 in
                 FStar_Compiler_List.for_all
                   (fun d ->
                      FStar_Compiler_List.for_all
                        (fun ty_lid1 ->
                           let uu___2 =
                             FStar_Compiler_List.map
                               (fun uu___3 ->
                                  FStar_Syntax_Syntax.U_name uu___3) ty_us1 in
                           ty_strictly_positive_in_datacon_decl env2 mutuals1
                             ty_lid1 d ty_params2 uu___2 unfolded_inductives)
                        mutuals1) datacons)
let (check_exn_strict_positivity :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> Prims.bool) =
  fun env ->
    fun data_ctor_lid ->
      let unfolded_inductives = FStar_Compiler_Util.mk_ref [] in
      ty_strictly_positive_in_datacon_decl env [] FStar_Parser_Const.exn_lid
        data_ctor_lid [] [] unfolded_inductives