open Prims
let (tun_r : FStar_Range.range -> FStar_Syntax_Syntax.term) =
  fun r ->
    let uu___29_5 = FStar_Syntax_Syntax.tun in
    {
      FStar_Syntax_Syntax.n = (uu___29_5.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = r;
      FStar_Syntax_Syntax.vars = (uu___29_5.FStar_Syntax_Syntax.vars)
    }
type annotated_pat =
  (FStar_Syntax_Syntax.pat * (FStar_Syntax_Syntax.bv *
    FStar_Syntax_Syntax.typ) Prims.list)
let (desugar_disjunctive_pattern :
  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list) Prims.list ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.branch Prims.list)
  =
  fun annotated_pats ->
    fun when_opt ->
      fun branch ->
        FStar_All.pipe_right annotated_pats
          (FStar_List.map
             (fun uu____110 ->
                match uu____110 with
                | (pat, annots) ->
                    let branch1 =
                      FStar_List.fold_left
                        (fun br ->
                           fun uu____165 ->
                             match uu____165 with
                             | (bv, ty) ->
                                 let lb =
                                   let uu____183 =
                                     FStar_Syntax_Syntax.bv_to_name bv in
                                   FStar_Syntax_Util.mk_letbinding
                                     (FStar_Util.Inl bv) [] ty
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____183 [] br.FStar_Syntax_Syntax.pos in
                                 let branch1 =
                                   let uu____189 =
                                     let uu____190 =
                                       FStar_Syntax_Syntax.mk_binder bv in
                                     [uu____190] in
                                   FStar_Syntax_Subst.close uu____189 branch in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((false, [lb]), branch1))
                                   br.FStar_Syntax_Syntax.pos) branch annots in
                    FStar_Syntax_Util.branch (pat, when_opt, branch1)))
let (trans_qual :
  FStar_Range.range ->
    FStar_Ident.lident FStar_Pervasives_Native.option ->
      FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier)
  =
  fun r ->
    fun maybe_effect_id ->
      fun uu___0_247 ->
        match uu___0_247 with
        | FStar_Parser_AST.Private -> FStar_Syntax_Syntax.Private
        | FStar_Parser_AST.Assumption -> FStar_Syntax_Syntax.Assumption
        | FStar_Parser_AST.Unfold_for_unification_and_vcgen ->
            FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
        | FStar_Parser_AST.Inline_for_extraction ->
            FStar_Syntax_Syntax.Inline_for_extraction
        | FStar_Parser_AST.NoExtract -> FStar_Syntax_Syntax.NoExtract
        | FStar_Parser_AST.Irreducible -> FStar_Syntax_Syntax.Irreducible
        | FStar_Parser_AST.Logic -> FStar_Syntax_Syntax.Logic
        | FStar_Parser_AST.TotalEffect -> FStar_Syntax_Syntax.TotalEffect
        | FStar_Parser_AST.Effect_qual -> FStar_Syntax_Syntax.Effect
        | FStar_Parser_AST.New -> FStar_Syntax_Syntax.New
        | FStar_Parser_AST.Abstract -> FStar_Syntax_Syntax.Abstract
        | FStar_Parser_AST.Opaque ->
            (FStar_Errors.log_issue r
               (FStar_Errors.Warning_DeprecatedOpaqueQualifier,
                 "The 'opaque' qualifier is deprecated since its use was strangely schizophrenic. There were two overloaded uses: (1) Given 'opaque val f : t', the behavior was to exclude the definition of 'f' to the SMT solver. This corresponds roughly to the new 'irreducible' qualifier. (2) Given 'opaque type t = t'', the behavior was to provide the definition of 't' to the SMT solver, but not to inline it, unless absolutely required for unification. This corresponds roughly to the behavior of 'unfoldable' (which is currently the default).");
             FStar_Syntax_Syntax.Visible_default)
        | FStar_Parser_AST.Reflectable ->
            (match maybe_effect_id with
             | FStar_Pervasives_Native.None ->
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_ReflectOnlySupportedOnEffects,
                     "Qualifier reflect only supported on effects") r
             | FStar_Pervasives_Native.Some effect_id ->
                 FStar_Syntax_Syntax.Reflectable effect_id)
        | FStar_Parser_AST.Reifiable -> FStar_Syntax_Syntax.Reifiable
        | FStar_Parser_AST.Noeq -> FStar_Syntax_Syntax.Noeq
        | FStar_Parser_AST.Unopteq -> FStar_Syntax_Syntax.Unopteq
        | FStar_Parser_AST.DefaultEffect ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_DefaultQualifierNotAllowedOnEffects,
                "The 'default' qualifier on effects is no longer supported")
              r
        | FStar_Parser_AST.Inline ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnsupportedQualifier,
                "Unsupported qualifier") r
        | FStar_Parser_AST.Visible ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnsupportedQualifier,
                "Unsupported qualifier") r
let (trans_pragma : FStar_Parser_AST.pragma -> FStar_Syntax_Syntax.pragma) =
  fun uu___1_267 ->
    match uu___1_267 with
    | FStar_Parser_AST.SetOptions s -> FStar_Syntax_Syntax.SetOptions s
    | FStar_Parser_AST.ResetOptions sopt ->
        FStar_Syntax_Syntax.ResetOptions sopt
    | FStar_Parser_AST.PushOptions sopt ->
        FStar_Syntax_Syntax.PushOptions sopt
    | FStar_Parser_AST.PopOptions -> FStar_Syntax_Syntax.PopOptions
    | FStar_Parser_AST.RestartSolver -> FStar_Syntax_Syntax.RestartSolver
    | FStar_Parser_AST.LightOff -> FStar_Syntax_Syntax.LightOff
let (as_imp :
  FStar_Parser_AST.imp ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
  =
  fun uu___2_285 ->
    match uu___2_285 with
    | FStar_Parser_AST.Hash ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | uu____288 -> FStar_Pervasives_Native.None
let arg_withimp_e :
  'uuuuuu296 .
    FStar_Parser_AST.imp ->
      'uuuuuu296 ->
        ('uuuuuu296 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  = fun imp -> fun t -> (t, (as_imp imp))
let arg_withimp_t :
  'uuuuuu322 .
    FStar_Parser_AST.imp ->
      'uuuuuu322 ->
        ('uuuuuu322 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  =
  fun imp ->
    fun t ->
      match imp with
      | FStar_Parser_AST.Hash ->
          (t, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag))
      | uu____341 -> (t, FStar_Pervasives_Native.None)
let (contains_binder : FStar_Parser_AST.binder Prims.list -> Prims.bool) =
  fun binders ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____362 -> true
            | uu____368 -> false))
let rec (unparen : FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun t ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____377 -> t
let (tm_type_z : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r ->
    let uu____384 =
      let uu____385 = FStar_Ident.lid_of_path ["Type0"] r in
      FStar_Parser_AST.Name uu____385 in
    FStar_Parser_AST.mk_term uu____384 r FStar_Parser_AST.Kind
let (tm_type : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r ->
    let uu____395 =
      let uu____396 = FStar_Ident.lid_of_path ["Type"] r in
      FStar_Parser_AST.Name uu____396 in
    FStar_Parser_AST.mk_term uu____395 r FStar_Parser_AST.Kind
let rec (is_comp_type :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun env ->
    fun t ->
      let uu____412 =
        let uu____413 = unparen t in uu____413.FStar_Parser_AST.tm in
      match uu____412 with
      | FStar_Parser_AST.Name l ->
          let uu____416 = FStar_Syntax_DsEnv.try_lookup_effect_name env l in
          FStar_All.pipe_right uu____416 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l, uu____423) ->
          let uu____436 = FStar_Syntax_DsEnv.try_lookup_effect_name env l in
          FStar_All.pipe_right uu____436 FStar_Option.isSome
      | FStar_Parser_AST.App (head, uu____443, uu____444) ->
          is_comp_type env head
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1, uu____449, uu____450) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____455, t1) -> is_comp_type env t1
      | uu____457 -> false
let (unit_ty : FStar_Range.range -> FStar_Parser_AST.term) =
  fun rng ->
    FStar_Parser_AST.mk_term
      (FStar_Parser_AST.Name FStar_Parser_Const.unit_lid) rng
      FStar_Parser_AST.Type_level
type env_t = FStar_Syntax_DsEnv.env
type lenv_t = FStar_Syntax_Syntax.bv Prims.list
let (desugar_name' :
  (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
    env_t ->
      Prims.bool ->
        FStar_Ident.lid ->
          FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun setpos ->
    fun env ->
      fun resolve ->
        fun l ->
          let tm_attrs_opt =
            if resolve
            then FStar_Syntax_DsEnv.try_lookup_lid_with_attributes env l
            else
              FStar_Syntax_DsEnv.try_lookup_lid_with_attributes_no_resolve
                env l in
          match tm_attrs_opt with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (tm, attrs) ->
              let tm1 = setpos tm in FStar_Pervasives_Native.Some tm1
let desugar_name :
  'uuuuuu553 .
    'uuuuuu553 ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        env_t -> Prims.bool -> FStar_Ident.lident -> FStar_Syntax_Syntax.term
  =
  fun mk ->
    fun setpos ->
      fun env ->
        fun resolve ->
          fun l ->
            FStar_Syntax_DsEnv.fail_or env (desugar_name' setpos env resolve)
              l
let (compile_op_lid :
  Prims.int -> Prims.string -> FStar_Range.range -> FStar_Ident.lident) =
  fun n ->
    fun s ->
      fun r ->
        let uu____606 =
          let uu____607 =
            let uu____608 =
              let uu____614 = FStar_Parser_AST.compile_op n s r in
              (uu____614, r) in
            FStar_Ident.mk_ident uu____608 in
          [uu____607] in
        FStar_All.pipe_right uu____606 FStar_Ident.lid_of_ids
let (op_as_term :
  env_t ->
    Prims.int ->
      FStar_Ident.ident ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env ->
    fun arity ->
      fun op ->
        let r l dd =
          let uu____652 =
            let uu____653 =
              let uu____654 =
                let uu____655 = FStar_Ident.range_of_id op in
                FStar_Ident.set_lid_range l uu____655 in
              FStar_Syntax_Syntax.lid_as_fv uu____654 dd
                FStar_Pervasives_Native.None in
            FStar_All.pipe_right uu____653 FStar_Syntax_Syntax.fv_to_tm in
          FStar_Pervasives_Native.Some uu____652 in
        let fallback uu____663 =
          let uu____664 = FStar_Ident.string_of_id op in
          match uu____664 with
          | "=" ->
              r FStar_Parser_Const.op_Eq FStar_Syntax_Syntax.delta_equational
          | ":=" ->
              r FStar_Parser_Const.write_lid
                FStar_Syntax_Syntax.delta_equational
          | "<" ->
              r FStar_Parser_Const.op_LT FStar_Syntax_Syntax.delta_equational
          | "<=" ->
              r FStar_Parser_Const.op_LTE
                FStar_Syntax_Syntax.delta_equational
          | ">" ->
              r FStar_Parser_Const.op_GT FStar_Syntax_Syntax.delta_equational
          | ">=" ->
              r FStar_Parser_Const.op_GTE
                FStar_Syntax_Syntax.delta_equational
          | "&&" ->
              r FStar_Parser_Const.op_And
                FStar_Syntax_Syntax.delta_equational
          | "||" ->
              r FStar_Parser_Const.op_Or FStar_Syntax_Syntax.delta_equational
          | "+" ->
              r FStar_Parser_Const.op_Addition
                FStar_Syntax_Syntax.delta_equational
          | "-" when arity = Prims.int_one ->
              r FStar_Parser_Const.op_Minus
                FStar_Syntax_Syntax.delta_equational
          | "-" ->
              r FStar_Parser_Const.op_Subtraction
                FStar_Syntax_Syntax.delta_equational
          | "/" ->
              r FStar_Parser_Const.op_Division
                FStar_Syntax_Syntax.delta_equational
          | "%" ->
              r FStar_Parser_Const.op_Modulus
                FStar_Syntax_Syntax.delta_equational
          | "!" ->
              r FStar_Parser_Const.read_lid
                FStar_Syntax_Syntax.delta_equational
          | "@" ->
              let uu____685 = FStar_Options.ml_ish () in
              if uu____685
              then
                r FStar_Parser_Const.list_append_lid
                  (FStar_Syntax_Syntax.Delta_equational_at_level
                     (Prims.of_int (2)))
              else
                r FStar_Parser_Const.list_tot_append_lid
                  (FStar_Syntax_Syntax.Delta_equational_at_level
                     (Prims.of_int (2)))
          | "|>" ->
              r FStar_Parser_Const.pipe_right_lid
                FStar_Syntax_Syntax.delta_equational
          | "<|" ->
              r FStar_Parser_Const.pipe_left_lid
                FStar_Syntax_Syntax.delta_equational
          | "<>" ->
              r FStar_Parser_Const.op_notEq
                FStar_Syntax_Syntax.delta_equational
          | "~" ->
              r FStar_Parser_Const.not_lid
                (FStar_Syntax_Syntax.Delta_constant_at_level
                   (Prims.of_int (2)))
          | "==" ->
              r FStar_Parser_Const.eq2_lid
                (FStar_Syntax_Syntax.Delta_constant_at_level
                   (Prims.of_int (2)))
          | "<<" ->
              r FStar_Parser_Const.precedes_lid
                FStar_Syntax_Syntax.delta_constant
          | "/\\" ->
              r FStar_Parser_Const.and_lid
                (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
          | "\\/" ->
              r FStar_Parser_Const.or_lid
                (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
          | "==>" ->
              r FStar_Parser_Const.imp_lid
                (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
          | "<==>" ->
              r FStar_Parser_Const.iff_lid
                (FStar_Syntax_Syntax.Delta_constant_at_level
                   (Prims.of_int (2)))
          | uu____710 -> FStar_Pervasives_Native.None in
        let uu____712 =
          let uu____715 =
            let uu____716 = FStar_Ident.string_of_id op in
            let uu____718 = FStar_Ident.range_of_id op in
            compile_op_lid arity uu____716 uu____718 in
          desugar_name'
            (fun t ->
               let uu___180_726 = t in
               let uu____727 = FStar_Ident.range_of_id op in
               {
                 FStar_Syntax_Syntax.n = (uu___180_726.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = uu____727;
                 FStar_Syntax_Syntax.vars =
                   (uu___180_726.FStar_Syntax_Syntax.vars)
               }) env true uu____715 in
        match uu____712 with
        | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
        | uu____732 -> fallback ()
let (sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list)
  =
  fun ftv ->
    let uu____747 =
      FStar_Util.remove_dups
        (fun x ->
           fun y ->
             let uu____756 = FStar_Ident.string_of_id x in
             let uu____758 = FStar_Ident.string_of_id y in
             uu____756 = uu____758) ftv in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x ->
            fun y ->
              let uu____771 = FStar_Ident.string_of_id x in
              let uu____773 = FStar_Ident.string_of_id y in
              FStar_String.compare uu____771 uu____773)) uu____747
let rec (free_type_vars_b :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Syntax_DsEnv.env * FStar_Ident.ident Prims.list))
  =
  fun env ->
    fun binder ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____808 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____812 = FStar_Syntax_DsEnv.push_bv env x in
          (match uu____812 with | (env1, uu____824) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____827, term) ->
          let uu____829 = free_type_vars env term in (env, uu____829)
      | FStar_Parser_AST.TAnnotated (id, uu____835) ->
          let uu____836 = FStar_Syntax_DsEnv.push_bv env id in
          (match uu____836 with | (env1, uu____848) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____852 = free_type_vars env t in (env, uu____852)
and (free_type_vars :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list)
  =
  fun env ->
    fun t ->
      let uu____859 =
        let uu____860 = unparen t in uu____860.FStar_Parser_AST.tm in
      match uu____859 with
      | FStar_Parser_AST.Labeled uu____863 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____876 = FStar_Syntax_DsEnv.try_lookup_id env a in
          (match uu____876 with
           | FStar_Pervasives_Native.None -> [a]
           | uu____881 -> [])
      | FStar_Parser_AST.Wild -> []
      | FStar_Parser_AST.Const uu____884 -> []
      | FStar_Parser_AST.Uvar uu____885 -> []
      | FStar_Parser_AST.Var uu____886 -> []
      | FStar_Parser_AST.Projector uu____887 -> []
      | FStar_Parser_AST.Discrim uu____892 -> []
      | FStar_Parser_AST.Name uu____893 -> []
      | FStar_Parser_AST.Requires (t1, uu____895) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1, uu____903) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____910, t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1, t', tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None -> []
             | FStar_Pervasives_Native.Some t2 -> [t2]) in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____929, ts) ->
          FStar_List.collect
            (fun uu____950 ->
               match uu____950 with
               | (t1, uu____958) -> free_type_vars env t1) ts
      | FStar_Parser_AST.Op (uu____959, ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1, t2, uu____967) ->
          let uu____968 = free_type_vars env t1 in
          let uu____971 = free_type_vars env t2 in
          FStar_List.append uu____968 uu____971
      | FStar_Parser_AST.Refine (b, t1) ->
          let uu____976 = free_type_vars_b env b in
          (match uu____976 with
           | (env1, f) ->
               let uu____991 = free_type_vars env1 t1 in
               FStar_List.append f uu____991)
      | FStar_Parser_AST.Sum (binders, body) ->
          let uu____1008 =
            FStar_List.fold_left
              (fun uu____1032 ->
                 fun bt ->
                   match uu____1032 with
                   | (env1, free) ->
                       let uu____1056 =
                         match bt with
                         | FStar_Util.Inl binder ->
                             free_type_vars_b env1 binder
                         | FStar_Util.Inr t1 ->
                             let uu____1071 = free_type_vars env1 body in
                             (env1, uu____1071) in
                       (match uu____1056 with
                        | (env2, f) -> (env2, (FStar_List.append f free))))
              (env, []) binders in
          (match uu____1008 with
           | (env1, free) ->
               let uu____1100 = free_type_vars env1 body in
               FStar_List.append free uu____1100)
      | FStar_Parser_AST.Product (binders, body) ->
          let uu____1109 =
            FStar_List.fold_left
              (fun uu____1129 ->
                 fun binder ->
                   match uu____1129 with
                   | (env1, free) ->
                       let uu____1149 = free_type_vars_b env1 binder in
                       (match uu____1149 with
                        | (env2, f) -> (env2, (FStar_List.append f free))))
              (env, []) binders in
          (match uu____1109 with
           | (env1, free) ->
               let uu____1180 = free_type_vars env1 body in
               FStar_List.append free uu____1180)
      | FStar_Parser_AST.Project (t1, uu____1184) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.CalcProof (rel, init, steps) ->
          let uu____1195 = free_type_vars env rel in
          let uu____1198 =
            let uu____1201 = free_type_vars env init in
            let uu____1204 =
              FStar_List.collect
                (fun uu____1213 ->
                   match uu____1213 with
                   | FStar_Parser_AST.CalcStep (rel1, just, next) ->
                       let uu____1219 = free_type_vars env rel1 in
                       let uu____1222 =
                         let uu____1225 = free_type_vars env just in
                         let uu____1228 = free_type_vars env next in
                         FStar_List.append uu____1225 uu____1228 in
                       FStar_List.append uu____1219 uu____1222) steps in
            FStar_List.append uu____1201 uu____1204 in
          FStar_List.append uu____1195 uu____1198
      | FStar_Parser_AST.Abs uu____1231 -> []
      | FStar_Parser_AST.Let uu____1238 -> []
      | FStar_Parser_AST.LetOpen uu____1259 -> []
      | FStar_Parser_AST.If uu____1264 -> []
      | FStar_Parser_AST.QForall uu____1271 -> []
      | FStar_Parser_AST.QExists uu____1290 -> []
      | FStar_Parser_AST.Record uu____1309 -> []
      | FStar_Parser_AST.Match uu____1322 -> []
      | FStar_Parser_AST.TryWith uu____1337 -> []
      | FStar_Parser_AST.Bind uu____1352 -> []
      | FStar_Parser_AST.Quote uu____1359 -> []
      | FStar_Parser_AST.VQuote uu____1364 -> []
      | FStar_Parser_AST.Antiquote uu____1365 -> []
      | FStar_Parser_AST.Seq uu____1366 -> []
let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun t ->
    let rec aux args t1 =
      let uu____1420 =
        let uu____1421 = unparen t1 in uu____1421.FStar_Parser_AST.tm in
      match uu____1420 with
      | FStar_Parser_AST.App (t2, arg, imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l, args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____1463 -> (t1, args) in
    aux [] t
let (close :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env ->
    fun t ->
      let ftv =
        let uu____1488 = free_type_vars env t in
        FStar_All.pipe_left sort_ftv uu____1488 in
      if (FStar_List.length ftv) = Prims.int_zero
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x ->
                   let uu____1511 =
                     let uu____1512 =
                       let uu____1517 =
                         let uu____1518 = FStar_Ident.range_of_id x in
                         tm_type uu____1518 in
                       (x, uu____1517) in
                     FStar_Parser_AST.TAnnotated uu____1512 in
                   let uu____1519 = FStar_Ident.range_of_id x in
                   FStar_Parser_AST.mk_binder uu____1511 uu____1519
                     FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit))) in
         let result =
           FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (binders, t))
             t.FStar_Parser_AST.range t.FStar_Parser_AST.level in
         result)
let (close_fun :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env ->
    fun t ->
      let ftv =
        let uu____1537 = free_type_vars env t in
        FStar_All.pipe_left sort_ftv uu____1537 in
      if (FStar_List.length ftv) = Prims.int_zero
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x ->
                   let uu____1560 =
                     let uu____1561 =
                       let uu____1566 =
                         let uu____1567 = FStar_Ident.range_of_id x in
                         tm_type uu____1567 in
                       (x, uu____1566) in
                     FStar_Parser_AST.TAnnotated uu____1561 in
                   let uu____1568 = FStar_Ident.range_of_id x in
                   FStar_Parser_AST.mk_binder uu____1560 uu____1568
                     FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit))) in
         let t1 =
           let uu____1570 =
             let uu____1571 = unparen t in uu____1571.FStar_Parser_AST.tm in
           match uu____1570 with
           | FStar_Parser_AST.Product uu____1572 -> t
           | uu____1579 ->
               FStar_Parser_AST.mk_term
                 (FStar_Parser_AST.App
                    ((FStar_Parser_AST.mk_term
                        (FStar_Parser_AST.Name
                           FStar_Parser_Const.effect_Tot_lid)
                        t.FStar_Parser_AST.range t.FStar_Parser_AST.level),
                      t, FStar_Parser_AST.Nothing)) t.FStar_Parser_AST.range
                 t.FStar_Parser_AST.level in
         let result =
           FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (binders, t1))
             t1.FStar_Parser_AST.range t1.FStar_Parser_AST.level in
         result)
let rec (uncurry :
  FStar_Parser_AST.binder Prims.list ->
    FStar_Parser_AST.term ->
      (FStar_Parser_AST.binder Prims.list * FStar_Parser_AST.term))
  =
  fun bs ->
    fun t ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (binders, t1) ->
          uncurry (FStar_List.append bs binders) t1
      | uu____1616 -> (bs, t)
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild uu____1627 -> true
    | FStar_Parser_AST.PatTvar (uu____1631, uu____1632) -> true
    | FStar_Parser_AST.PatVar (uu____1638, uu____1639) -> true
    | FStar_Parser_AST.PatAscribed (p1, uu____1646) -> is_var_pattern p1
    | uu____1659 -> false
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1, uu____1670) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____1683;
           FStar_Parser_AST.prange = uu____1684;_},
         uu____1685)
        -> true
    | uu____1697 -> false
let (replace_unit_pattern :
  FStar_Parser_AST.pattern -> FStar_Parser_AST.pattern) =
  fun p ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatConst (FStar_Const.Const_unit) ->
        FStar_Parser_AST.mk_pattern
          (FStar_Parser_AST.PatAscribed
             ((FStar_Parser_AST.mk_pattern
                 (FStar_Parser_AST.PatWild FStar_Pervasives_Native.None)
                 p.FStar_Parser_AST.prange),
               ((unit_ty p.FStar_Parser_AST.prange),
                 FStar_Pervasives_Native.None))) p.FStar_Parser_AST.prange
    | uu____1713 -> p
let rec (destruct_app_pattern :
  env_t ->
    Prims.bool ->
      FStar_Parser_AST.pattern ->
        ((FStar_Ident.ident, FStar_Ident.lid) FStar_Util.either *
          FStar_Parser_AST.pattern Prims.list * (FStar_Parser_AST.term *
          FStar_Parser_AST.term FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.option))
  =
  fun env ->
    fun is_top_level ->
      fun p ->
        match p.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatAscribed (p1, t) ->
            let uu____1786 = destruct_app_pattern env is_top_level p1 in
            (match uu____1786 with
             | (name, args, uu____1829) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id, uu____1879);
               FStar_Parser_AST.prange = uu____1880;_},
             args)
            when is_top_level ->
            let uu____1890 =
              let uu____1895 = FStar_Syntax_DsEnv.qualify env id in
              FStar_Util.Inr uu____1895 in
            (uu____1890, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id, uu____1917);
               FStar_Parser_AST.prange = uu____1918;_},
             args)
            -> ((FStar_Util.Inl id), args, FStar_Pervasives_Native.None)
        | uu____1948 -> failwith "Not an app pattern"
let rec (gather_pattern_bound_vars_maybe_top :
  FStar_Ident.ident FStar_Util.set ->
    FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set)
  =
  fun acc ->
    fun p ->
      let gather_pattern_bound_vars_from_list =
        FStar_List.fold_left gather_pattern_bound_vars_maybe_top acc in
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatWild uu____2000 -> acc
      | FStar_Parser_AST.PatConst uu____2003 -> acc
      | FStar_Parser_AST.PatName uu____2004 -> acc
      | FStar_Parser_AST.PatOp uu____2005 -> acc
      | FStar_Parser_AST.PatApp (phead, pats) ->
          gather_pattern_bound_vars_from_list (phead :: pats)
      | FStar_Parser_AST.PatTvar (x, uu____2013) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatVar (x, uu____2019) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatTuple (pats, uu____2028) ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu____2045 =
            FStar_List.map FStar_Pervasives_Native.snd guarded_pats in
          gather_pattern_bound_vars_from_list uu____2045
      | FStar_Parser_AST.PatAscribed (pat, uu____2053) ->
          gather_pattern_bound_vars_maybe_top acc pat
let (gather_pattern_bound_vars :
  FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set) =
  let acc =
    FStar_Util.new_set
      (fun id1 ->
         fun id2 ->
           let uu____2081 =
             let uu____2083 = FStar_Ident.string_of_id id1 in
             let uu____2085 = FStar_Ident.string_of_id id2 in
             uu____2083 = uu____2085 in
           if uu____2081 then Prims.int_zero else Prims.int_one) in
  fun p -> gather_pattern_bound_vars_maybe_top acc p
type bnd =
  | LocalBinder of (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) 
  | LetBinder of (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)) 
let (uu___is_LocalBinder : bnd -> Prims.bool) =
  fun projectee ->
    match projectee with | LocalBinder _0 -> true | uu____2133 -> false
let (__proj__LocalBinder__item___0 :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun projectee -> match projectee with | LocalBinder _0 -> _0
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee ->
    match projectee with | LetBinder _0 -> true | uu____2174 -> false
let (__proj__LetBinder__item___0 :
  bnd ->
    (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)))
  = fun projectee -> match projectee with | LetBinder _0 -> _0
let (is_implicit : bnd -> Prims.bool) =
  fun b ->
    match b with
    | LocalBinder
        (uu____2222, FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____2223))
        -> true
    | uu____2226 -> false
let (binder_of_bnd :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun uu___3_2237 ->
    match uu___3_2237 with
    | LocalBinder (a, aq) -> (a, aq)
    | uu____2244 -> failwith "Impossible"
let (mk_lb :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list *
    (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Range.range)
    -> FStar_Syntax_Syntax.letbinding)
  =
  fun uu____2277 ->
    match uu____2277 with
    | (attrs, n, t, e, pos) ->
        {
          FStar_Syntax_Syntax.lbname = n;
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_ALL_lid;
          FStar_Syntax_Syntax.lbdef = e;
          FStar_Syntax_Syntax.lbattrs = attrs;
          FStar_Syntax_Syntax.lbpos = pos
        }
let (no_annot_abs :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs -> fun t -> FStar_Syntax_Util.abs bs t FStar_Pervasives_Native.None
let (mk_ref_read :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm ->
    let tm' =
      let uu____2359 =
        let uu____2376 =
          let uu____2379 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
          FStar_Syntax_Syntax.fv_to_tm uu____2379 in
        let uu____2380 =
          let uu____2391 =
            let uu____2400 = FStar_Syntax_Syntax.as_implicit false in
            (tm, uu____2400) in
          [uu____2391] in
        (uu____2376, uu____2380) in
      FStar_Syntax_Syntax.Tm_app uu____2359 in
    FStar_Syntax_Syntax.mk tm' tm.FStar_Syntax_Syntax.pos
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm ->
    let tm' =
      let uu____2449 =
        let uu____2466 =
          let uu____2469 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
          FStar_Syntax_Syntax.fv_to_tm uu____2469 in
        let uu____2470 =
          let uu____2481 =
            let uu____2490 = FStar_Syntax_Syntax.as_implicit false in
            (tm, uu____2490) in
          [uu____2481] in
        (uu____2466, uu____2470) in
      FStar_Syntax_Syntax.Tm_app uu____2449 in
    FStar_Syntax_Syntax.mk tm' tm.FStar_Syntax_Syntax.pos
let (mk_ref_assign :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Range.range ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1 ->
    fun t2 ->
      fun pos ->
        let tm =
          let uu____2553 =
            let uu____2570 =
              let uu____2573 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Syntax_Syntax.fv_to_tm uu____2573 in
            let uu____2574 =
              let uu____2585 =
                let uu____2594 = FStar_Syntax_Syntax.as_implicit false in
                (t1, uu____2594) in
              let uu____2602 =
                let uu____2613 =
                  let uu____2622 = FStar_Syntax_Syntax.as_implicit false in
                  (t2, uu____2622) in
                [uu____2613] in
              uu____2585 :: uu____2602 in
            (uu____2570, uu____2574) in
          FStar_Syntax_Syntax.Tm_app uu____2553 in
        FStar_Syntax_Syntax.mk tm pos
let rec (generalize_annotated_univs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun s ->
    let bs_univnames bs =
      let uu____2682 =
        let uu____2697 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name in
        FStar_List.fold_left
          (fun uvs ->
             fun uu____2716 ->
               match uu____2716 with
               | ({ FStar_Syntax_Syntax.ppname = uu____2727;
                    FStar_Syntax_Syntax.index = uu____2728;
                    FStar_Syntax_Syntax.sort = t;_},
                  uu____2730) ->
                   let uu____2738 = FStar_Syntax_Free.univnames t in
                   FStar_Util.set_union uvs uu____2738) uu____2697 in
      FStar_All.pipe_right bs uu____2682 in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____2754 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____2772 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs, lids) ->
        let uvs =
          let uu____2800 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs ->
                    fun se ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____2821, uu____2822, bs, t, uu____2825,
                             uu____2826)
                            ->
                            let uu____2835 = bs_univnames bs in
                            let uu____2838 = FStar_Syntax_Free.univnames t in
                            FStar_Util.set_union uu____2835 uu____2838
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____2841, uu____2842, t, uu____2844,
                             uu____2845, uu____2846)
                            -> FStar_Syntax_Free.univnames t
                        | uu____2853 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt" in
                      FStar_Util.set_union uvs se_univs) empty_set) in
          FStar_All.pipe_right uu____2800 FStar_Util.set_elements in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs in
        let uu___567_2862 = s in
        let uu____2863 =
          let uu____2864 =
            let uu____2873 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid, uu____2891, bs, t, lids1, lids2) ->
                          let uu___578_2904 = se in
                          let uu____2905 =
                            let uu____2906 =
                              let uu____2923 =
                                FStar_Syntax_Subst.subst_binders usubst bs in
                              let uu____2924 =
                                let uu____2925 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst in
                                FStar_Syntax_Subst.subst uu____2925 t in
                              (lid, uvs, uu____2923, uu____2924, lids1,
                                lids2) in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____2906 in
                          {
                            FStar_Syntax_Syntax.sigel = uu____2905;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___578_2904.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___578_2904.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___578_2904.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___578_2904.FStar_Syntax_Syntax.sigattrs);
                            FStar_Syntax_Syntax.sigopts =
                              (uu___578_2904.FStar_Syntax_Syntax.sigopts)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid, uu____2939, t, tlid, n, lids1) ->
                          let uu___588_2950 = se in
                          let uu____2951 =
                            let uu____2952 =
                              let uu____2968 =
                                FStar_Syntax_Subst.subst usubst t in
                              (lid, uvs, uu____2968, tlid, n, lids1) in
                            FStar_Syntax_Syntax.Sig_datacon uu____2952 in
                          {
                            FStar_Syntax_Syntax.sigel = uu____2951;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___588_2950.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___588_2950.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___588_2950.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___588_2950.FStar_Syntax_Syntax.sigattrs);
                            FStar_Syntax_Syntax.sigopts =
                              (uu___588_2950.FStar_Syntax_Syntax.sigopts)
                          }
                      | uu____2972 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt")) in
            (uu____2873, lids) in
          FStar_Syntax_Syntax.Sig_bundle uu____2864 in
        {
          FStar_Syntax_Syntax.sigel = uu____2863;
          FStar_Syntax_Syntax.sigrng =
            (uu___567_2862.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___567_2862.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___567_2862.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___567_2862.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___567_2862.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____2979, t) ->
        let uvs =
          let uu____2982 = FStar_Syntax_Free.univnames t in
          FStar_All.pipe_right uu____2982 FStar_Util.set_elements in
        let uu___597_2987 = s in
        let uu____2988 =
          let uu____2989 =
            let uu____2996 = FStar_Syntax_Subst.close_univ_vars uvs t in
            (lid, uvs, uu____2996) in
          FStar_Syntax_Syntax.Sig_declare_typ uu____2989 in
        {
          FStar_Syntax_Syntax.sigel = uu____2988;
          FStar_Syntax_Syntax.sigrng =
            (uu___597_2987.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___597_2987.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___597_2987.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___597_2987.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___597_2987.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_let ((b, lbs), lids) ->
        let lb_univnames lb =
          let uu____3020 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp in
          let uu____3023 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs, e, uu____3030) ->
                let uvs1 = bs_univnames bs in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____3063, (FStar_Util.Inl t, uu____3065),
                       uu____3066)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____3113, (FStar_Util.Inr c, uu____3115),
                       uu____3116)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____3163 -> empty_set in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_arrow (bs, uu____3165) ->
                bs_univnames bs
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____3186, (FStar_Util.Inl t, uu____3188), uu____3189) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____3236, (FStar_Util.Inr c, uu____3238), uu____3239) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____3286 -> empty_set in
          FStar_Util.set_union uu____3020 uu____3023 in
        let all_lb_univs =
          let uu____3290 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs ->
                    fun lb ->
                      let uu____3306 = lb_univnames lb in
                      FStar_Util.set_union uvs uu____3306) empty_set) in
          FStar_All.pipe_right uu____3290 FStar_Util.set_elements in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs in
        let uu___656_3316 = s in
        let uu____3317 =
          let uu____3318 =
            let uu____3325 =
              let uu____3326 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb ->
                        let uu___659_3338 = lb in
                        let uu____3339 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp in
                        let uu____3342 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___659_3338.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____3339;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___659_3338.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____3342;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___659_3338.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___659_3338.FStar_Syntax_Syntax.lbpos)
                        })) in
              (b, uu____3326) in
            (uu____3325, lids) in
          FStar_Syntax_Syntax.Sig_let uu____3318 in
        {
          FStar_Syntax_Syntax.sigel = uu____3317;
          FStar_Syntax_Syntax.sigrng =
            (uu___656_3316.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___656_3316.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___656_3316.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___656_3316.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___656_3316.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid, uu____3351, fml) ->
        let uvs =
          let uu____3354 = FStar_Syntax_Free.univnames fml in
          FStar_All.pipe_right uu____3354 FStar_Util.set_elements in
        let uu___667_3359 = s in
        let uu____3360 =
          let uu____3361 =
            let uu____3368 = FStar_Syntax_Subst.close_univ_vars uvs fml in
            (lid, uvs, uu____3368) in
          FStar_Syntax_Syntax.Sig_assume uu____3361 in
        {
          FStar_Syntax_Syntax.sigel = uu____3360;
          FStar_Syntax_Syntax.sigrng =
            (uu___667_3359.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___667_3359.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___667_3359.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___667_3359.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___667_3359.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uu____3370, bs, c, flags)
        ->
        let uvs =
          let uu____3379 =
            let uu____3382 = bs_univnames bs in
            let uu____3385 = FStar_Syntax_Free.univnames_comp c in
            FStar_Util.set_union uu____3382 uu____3385 in
          FStar_All.pipe_right uu____3379 FStar_Util.set_elements in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs in
        let uu___678_3393 = s in
        let uu____3394 =
          let uu____3395 =
            let uu____3408 = FStar_Syntax_Subst.subst_binders usubst bs in
            let uu____3409 = FStar_Syntax_Subst.subst_comp usubst c in
            (lid, uvs, uu____3408, uu____3409, flags) in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____3395 in
        {
          FStar_Syntax_Syntax.sigel = uu____3394;
          FStar_Syntax_Syntax.sigrng =
            (uu___678_3393.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___678_3393.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___678_3393.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___678_3393.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___678_3393.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_fail (errs, lax, ses) ->
        let uu___685_3427 = s in
        let uu____3428 =
          let uu____3429 =
            let uu____3442 = FStar_List.map generalize_annotated_univs ses in
            (errs, lax, uu____3442) in
          FStar_Syntax_Syntax.Sig_fail uu____3429 in
        {
          FStar_Syntax_Syntax.sigel = uu____3428;
          FStar_Syntax_Syntax.sigrng =
            (uu___685_3427.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___685_3427.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___685_3427.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___685_3427.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___685_3427.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_new_effect uu____3451 -> s
    | FStar_Syntax_Syntax.Sig_sub_effect uu____3452 -> s
    | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____3453 -> s
    | FStar_Syntax_Syntax.Sig_polymonadic_subcomp uu____3464 -> s
    | FStar_Syntax_Syntax.Sig_splice uu____3473 -> s
    | FStar_Syntax_Syntax.Sig_pragma uu____3480 -> s
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___4_3488 ->
    match uu___4_3488 with
    | "lift1" -> true
    | "lift2" -> true
    | "pure" -> true
    | "app" -> true
    | "push" -> true
    | "wp_if_then_else" -> true
    | "wp_assert" -> true
    | "wp_assume" -> true
    | "wp_close" -> true
    | "stronger" -> true
    | "ite_wp" -> true
    | "wp_trivial" -> true
    | "ctx" -> true
    | "gctx" -> true
    | "lift_from_pure" -> true
    | "return_wp" -> true
    | "return_elab" -> true
    | "bind_wp" -> true
    | "bind_elab" -> true
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
    | uu____3537 -> false
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u ->
    fun n ->
      if n = Prims.int_zero
      then u
      else
        (let uu____3558 = sum_to_universe u (n - Prims.int_one) in
         FStar_Syntax_Syntax.U_succ uu____3558)
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n -> sum_to_universe FStar_Syntax_Syntax.U_zero n
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int, FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t ->
    let uu____3584 =
      let uu____3585 = unparen t in uu____3585.FStar_Parser_AST.tm in
    match uu____3584 with
    | FStar_Parser_AST.Wild -> FStar_Util.Inr FStar_Syntax_Syntax.U_unknown
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr, uu____3595)) ->
        let n = FStar_Util.int_of_string repr in
        (if n < Prims.int_zero
         then
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_NegativeUniverseConstFatal_NotSupported,
               (Prims.op_Hat
                  "Negative universe constant  are not supported : " repr))
             t.FStar_Parser_AST.range
         else ();
         FStar_Util.Inl n)
    | FStar_Parser_AST.Op (op_plus, t1::t2::[]) ->
        let u1 = desugar_maybe_non_constant_universe t1 in
        let u2 = desugar_maybe_non_constant_universe t2 in
        (match (u1, u2) with
         | (FStar_Util.Inl n1, FStar_Util.Inl n2) -> FStar_Util.Inl (n1 + n2)
         | (FStar_Util.Inl n, FStar_Util.Inr u) ->
             let uu____3686 = sum_to_universe u n in
             FStar_Util.Inr uu____3686
         | (FStar_Util.Inr u, FStar_Util.Inl n) ->
             let uu____3703 = sum_to_universe u n in
             FStar_Util.Inr uu____3703
         | (FStar_Util.Inr u11, FStar_Util.Inr u21) ->
             let uu____3719 =
               let uu____3725 =
                 let uu____3727 = FStar_Parser_AST.term_to_string t in
                 Prims.op_Hat
                   "This universe might contain a sum of two universe variables "
                   uu____3727 in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____3725) in
             FStar_Errors.raise_error uu____3719 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____3736 ->
        let rec aux t1 univargs =
          let uu____3773 =
            let uu____3774 = unparen t1 in uu____3774.FStar_Parser_AST.tm in
          match uu____3773 with
          | FStar_Parser_AST.App (t2, targ, uu____3782) ->
              let uarg = desugar_maybe_non_constant_universe targ in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid ->
              if
                FStar_List.existsb
                  (fun uu___5_3809 ->
                     match uu___5_3809 with
                     | FStar_Util.Inr uu____3816 -> true
                     | uu____3819 -> false) univargs
              then
                let uu____3827 =
                  let uu____3828 =
                    FStar_List.map
                      (fun uu___6_3838 ->
                         match uu___6_3838 with
                         | FStar_Util.Inl n -> int_to_universe n
                         | FStar_Util.Inr u -> u) univargs in
                  FStar_Syntax_Syntax.U_max uu____3828 in
                FStar_Util.Inr uu____3827
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___7_3864 ->
                        match uu___7_3864 with
                        | FStar_Util.Inl n -> n
                        | FStar_Util.Inr uu____3874 -> failwith "impossible")
                     univargs in
                 let uu____3878 =
                   FStar_List.fold_left
                     (fun m -> fun n -> if m > n then m else n)
                     Prims.int_zero nargs in
                 FStar_Util.Inl uu____3878)
          | uu____3894 ->
              let uu____3895 =
                let uu____3901 =
                  let uu____3903 =
                    let uu____3905 = FStar_Parser_AST.term_to_string t1 in
                    Prims.op_Hat uu____3905 " in universe context" in
                  Prims.op_Hat "Unexpected term " uu____3903 in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3901) in
              FStar_Errors.raise_error uu____3895 t1.FStar_Parser_AST.range in
        aux t []
    | uu____3920 ->
        let uu____3921 =
          let uu____3927 =
            let uu____3929 =
              let uu____3931 = FStar_Parser_AST.term_to_string t in
              Prims.op_Hat uu____3931 " in universe context" in
            Prims.op_Hat "Unexpected term " uu____3929 in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3927) in
        FStar_Errors.raise_error uu____3921 t.FStar_Parser_AST.range
let (desugar_universe :
  FStar_Parser_AST.term -> FStar_Syntax_Syntax.universe) =
  fun t ->
    let u = desugar_maybe_non_constant_universe t in
    match u with
    | FStar_Util.Inl n -> int_to_universe n
    | FStar_Util.Inr u1 -> u1
let (check_no_aq : FStar_Syntax_Syntax.antiquotations -> unit) =
  fun aq ->
    match aq with
    | [] -> ()
    | (bv,
       {
         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_quoted
           (e,
            { FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
              FStar_Syntax_Syntax.antiquotes = uu____3972;_});
         FStar_Syntax_Syntax.pos = uu____3973;
         FStar_Syntax_Syntax.vars = uu____3974;_})::uu____3975
        ->
        let uu____4006 =
          let uu____4012 =
            let uu____4014 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____4014 in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4012) in
        FStar_Errors.raise_error uu____4006 e.FStar_Syntax_Syntax.pos
    | (bv, e)::uu____4020 ->
        let uu____4039 =
          let uu____4045 =
            let uu____4047 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____4047 in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4045) in
        FStar_Errors.raise_error uu____4039 e.FStar_Syntax_Syntax.pos
let check_fields :
  'uuuuuu4060 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident * 'uuuuuu4060) Prims.list ->
        FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env ->
    fun fields ->
      fun rg ->
        let uu____4088 = FStar_List.hd fields in
        match uu____4088 with
        | (f, uu____4098) ->
            let record =
              FStar_Syntax_DsEnv.fail_or env
                (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f in
            let check_field uu____4109 =
              match uu____4109 with
              | (f', uu____4115) ->
                  let uu____4116 =
                    FStar_Syntax_DsEnv.belongs_to_record env f' record in
                  if uu____4116
                  then ()
                  else
                    (let msg =
                       let uu____4123 = FStar_Ident.string_of_lid f in
                       let uu____4125 =
                         FStar_Ident.string_of_lid
                           record.FStar_Syntax_DsEnv.typename in
                       let uu____4127 = FStar_Ident.string_of_lid f' in
                       FStar_Util.format3
                         "Field %s belongs to record type %s, whereas field %s does not"
                         uu____4123 uu____4125 uu____4127 in
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FieldsNotBelongToSameRecordType,
                         msg) rg) in
            ((let uu____4132 = FStar_List.tl fields in
              FStar_List.iter check_field uu____4132);
             (match () with | () -> record))
let (check_linear_pattern_variables :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t Prims.list ->
    FStar_Range.range -> unit)
  =
  fun pats ->
    fun r ->
      let rec pat_vars p =
        match p.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_dot_term uu____4180 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_wild uu____4187 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_constant uu____4188 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_var x ->
            FStar_Util.set_add x FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_cons (uu____4190, pats1) ->
            let aux out uu____4231 =
              match uu____4231 with
              | (p1, uu____4244) ->
                  let intersection =
                    let uu____4254 = pat_vars p1 in
                    FStar_Util.set_intersect uu____4254 out in
                  let uu____4257 = FStar_Util.set_is_empty intersection in
                  if uu____4257
                  then
                    let uu____4262 = pat_vars p1 in
                    FStar_Util.set_union out uu____4262
                  else
                    (let duplicate_bv =
                       let uu____4268 = FStar_Util.set_elements intersection in
                       FStar_List.hd uu____4268 in
                     let uu____4271 =
                       let uu____4277 =
                         let uu____4279 =
                           FStar_Ident.string_of_id
                             duplicate_bv.FStar_Syntax_Syntax.ppname in
                         FStar_Util.format1
                           "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                           uu____4279 in
                       (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                         uu____4277) in
                     FStar_Errors.raise_error uu____4271 r) in
            FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1 in
      match pats with
      | [] -> ()
      | p::[] ->
          let uu____4303 = pat_vars p in
          FStar_All.pipe_right uu____4303 (fun uu____4308 -> ())
      | p::ps ->
          let pvars = pat_vars p in
          let aux p1 =
            let uu____4332 =
              let uu____4334 = pat_vars p1 in
              FStar_Util.set_eq pvars uu____4334 in
            if uu____4332
            then ()
            else
              (let nonlinear_vars =
                 let uu____4343 = pat_vars p1 in
                 FStar_Util.set_symmetric_difference pvars uu____4343 in
               let first_nonlinear_var =
                 let uu____4347 = FStar_Util.set_elements nonlinear_vars in
                 FStar_List.hd uu____4347 in
               let uu____4350 =
                 let uu____4356 =
                   let uu____4358 =
                     FStar_Ident.string_of_id
                       first_nonlinear_var.FStar_Syntax_Syntax.ppname in
                   FStar_Util.format1
                     "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                     uu____4358 in
                 (FStar_Errors.Fatal_IncoherentPatterns, uu____4356) in
               FStar_Errors.raise_error uu____4350 r) in
          FStar_List.iter aux ps
let (smt_pat_lid : FStar_Range.range -> FStar_Ident.lident) =
  fun r -> FStar_Ident.set_lid_range FStar_Parser_Const.smtpat_lid r
let (smt_pat_or_lid : FStar_Range.range -> FStar_Ident.lident) =
  fun r -> FStar_Ident.set_lid_range FStar_Parser_Const.smtpatOr_lid r
let rec (desugar_data_pat :
  Prims.bool ->
    env_t ->
      FStar_Parser_AST.pattern -> (env_t * bnd * annotated_pat Prims.list))
  =
  fun top_level_ascr_allowed ->
    fun env ->
      fun p ->
        let resolvex l e x =
          let uu____4685 =
            FStar_Util.find_opt
              (fun y ->
                 let uu____4692 =
                   FStar_Ident.string_of_id y.FStar_Syntax_Syntax.ppname in
                 let uu____4694 = FStar_Ident.string_of_id x in
                 uu____4692 = uu____4694) l in
          match uu____4685 with
          | FStar_Pervasives_Native.Some y -> (l, e, y)
          | uu____4708 ->
              let uu____4711 = FStar_Syntax_DsEnv.push_bv e x in
              (match uu____4711 with | (e1, xbv) -> ((xbv :: l), e1, xbv)) in
        let rec aux' top loc env1 p1 =
          let pos q =
            FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange in
          let pos_r r q = FStar_Syntax_Syntax.withinfo q r in
          let orig = p1 in
          match p1.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOr uu____4852 ->
              failwith "impossible: PatOr handled below"
          | FStar_Parser_AST.PatOp op ->
              let id_op =
                let uu____4874 =
                  let uu____4880 =
                    let uu____4882 = FStar_Ident.string_of_id op in
                    let uu____4884 = FStar_Ident.range_of_id op in
                    FStar_Parser_AST.compile_op Prims.int_zero uu____4882
                      uu____4884 in
                  let uu____4886 = FStar_Ident.range_of_id op in
                  (uu____4880, uu____4886) in
                FStar_Ident.mk_ident uu____4874 in
              let p2 =
                let uu___912_4889 = p1 in
                {
                  FStar_Parser_AST.pat =
                    (FStar_Parser_AST.PatVar
                       (id_op, FStar_Pervasives_Native.None));
                  FStar_Parser_AST.prange =
                    (uu___912_4889.FStar_Parser_AST.prange)
                } in
              aux loc env1 p2
          | FStar_Parser_AST.PatAscribed (p2, (t, tacopt)) ->
              ((match tacopt with
                | FStar_Pervasives_Native.None -> ()
                | FStar_Pervasives_Native.Some uu____4906 ->
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                        "Type ascriptions within patterns cannot be associated with a tactic")
                      orig.FStar_Parser_AST.prange);
               (let uu____4909 = aux loc env1 p2 in
                match uu____4909 with
                | (loc1, env', binder, p3, annots) ->
                    let uu____4965 =
                      match binder with
                      | LetBinder uu____4986 -> failwith "impossible"
                      | LocalBinder (x, aq) ->
                          let t1 =
                            let uu____5011 = close_fun env1 t in
                            desugar_term env1 uu____5011 in
                          let x1 =
                            let uu___938_5013 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___938_5013.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___938_5013.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            } in
                          ([(x1, t1)], (LocalBinder (x1, aq))) in
                    (match uu____4965 with
                     | (annots', binder1) ->
                         ((match p3.FStar_Syntax_Syntax.v with
                           | FStar_Syntax_Syntax.Pat_var uu____5059 -> ()
                           | FStar_Syntax_Syntax.Pat_wild uu____5060 -> ()
                           | uu____5061 when top && top_level_ascr_allowed ->
                               ()
                           | uu____5062 ->
                               FStar_Errors.raise_error
                                 (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                                   "Type ascriptions within patterns are only allowed on variables")
                                 orig.FStar_Parser_AST.prange);
                          (loc1, env', binder1, p3,
                            (FStar_List.append annots' annots))))))
          | FStar_Parser_AST.PatWild aq ->
              let aq1 = trans_aqual env1 aq in
              let x =
                let uu____5080 = tun_r p1.FStar_Parser_AST.prange in
                FStar_Syntax_Syntax.new_bv
                  (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                  uu____5080 in
              let uu____5081 =
                FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x) in
              (loc, env1, (LocalBinder (x, aq1)), uu____5081, [])
          | FStar_Parser_AST.PatConst c ->
              let x =
                let uu____5094 = tun_r p1.FStar_Parser_AST.prange in
                FStar_Syntax_Syntax.new_bv
                  (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                  uu____5094 in
              let uu____5095 =
                FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c) in
              (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                uu____5095, [])
          | FStar_Parser_AST.PatTvar (x, aq) ->
              let aq1 = trans_aqual env1 aq in
              let uu____5113 = resolvex loc env1 x in
              (match uu____5113 with
               | (loc1, env2, xbv) ->
                   let uu____5145 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_var xbv) in
                   (loc1, env2, (LocalBinder (xbv, aq1)), uu____5145, []))
          | FStar_Parser_AST.PatVar (x, aq) ->
              let aq1 = trans_aqual env1 aq in
              let uu____5163 = resolvex loc env1 x in
              (match uu____5163 with
               | (loc1, env2, xbv) ->
                   let uu____5195 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_var xbv) in
                   (loc1, env2, (LocalBinder (xbv, aq1)), uu____5195, []))
          | FStar_Parser_AST.PatName l ->
              let l1 =
                FStar_Syntax_DsEnv.fail_or env1
                  (FStar_Syntax_DsEnv.try_lookup_datacon env1) l in
              let x =
                let uu____5209 = tun_r p1.FStar_Parser_AST.prange in
                FStar_Syntax_Syntax.new_bv
                  (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                  uu____5209 in
              let uu____5210 =
                FStar_All.pipe_left pos
                  (FStar_Syntax_Syntax.Pat_cons (l1, [])) in
              (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                uu____5210, [])
          | FStar_Parser_AST.PatApp
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                 FStar_Parser_AST.prange = uu____5238;_},
               args)
              ->
              let uu____5244 =
                FStar_List.fold_right
                  (fun arg ->
                     fun uu____5305 ->
                       match uu____5305 with
                       | (loc1, env2, annots, args1) ->
                           let uu____5386 = aux loc1 env2 arg in
                           (match uu____5386 with
                            | (loc2, env3, b, arg1, ans) ->
                                let imp = is_implicit b in
                                (loc2, env3, (FStar_List.append ans annots),
                                  ((arg1, imp) :: args1)))) args
                  (loc, env1, [], []) in
              (match uu____5244 with
               | (loc1, env2, annots, args1) ->
                   let l1 =
                     FStar_Syntax_DsEnv.fail_or env2
                       (FStar_Syntax_DsEnv.try_lookup_datacon env2) l in
                   let x =
                     let uu____5558 = tun_r p1.FStar_Parser_AST.prange in
                     FStar_Syntax_Syntax.new_bv
                       (FStar_Pervasives_Native.Some
                          (p1.FStar_Parser_AST.prange)) uu____5558 in
                   let uu____5559 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_cons (l1, args1)) in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None)),
                     uu____5559, annots))
          | FStar_Parser_AST.PatApp uu____5575 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                p1.FStar_Parser_AST.prange
          | FStar_Parser_AST.PatList pats ->
              let uu____5603 =
                FStar_List.fold_right
                  (fun pat ->
                     fun uu____5653 ->
                       match uu____5653 with
                       | (loc1, env2, annots, pats1) ->
                           let uu____5714 = aux loc1 env2 pat in
                           (match uu____5714 with
                            | (loc2, env3, uu____5753, pat1, ans) ->
                                (loc2, env3, (FStar_List.append ans annots),
                                  (pat1 :: pats1)))) pats (loc, env1, [], []) in
              (match uu____5603 with
               | (loc1, env2, annots, pats1) ->
                   let pat =
                     let uu____5847 =
                       let uu____5850 =
                         let uu____5857 =
                           FStar_Range.end_range p1.FStar_Parser_AST.prange in
                         pos_r uu____5857 in
                       let uu____5858 =
                         let uu____5859 =
                           let uu____5873 =
                             FStar_Syntax_Syntax.lid_as_fv
                               FStar_Parser_Const.nil_lid
                               FStar_Syntax_Syntax.delta_constant
                               (FStar_Pervasives_Native.Some
                                  FStar_Syntax_Syntax.Data_ctor) in
                           (uu____5873, []) in
                         FStar_Syntax_Syntax.Pat_cons uu____5859 in
                       FStar_All.pipe_left uu____5850 uu____5858 in
                     FStar_List.fold_right
                       (fun hd ->
                          fun tl ->
                            let r =
                              FStar_Range.union_ranges
                                hd.FStar_Syntax_Syntax.p
                                tl.FStar_Syntax_Syntax.p in
                            let uu____5907 =
                              let uu____5908 =
                                let uu____5922 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.cons_lid
                                    FStar_Syntax_Syntax.delta_constant
                                    (FStar_Pervasives_Native.Some
                                       FStar_Syntax_Syntax.Data_ctor) in
                                (uu____5922, [(hd, false); (tl, false)]) in
                              FStar_Syntax_Syntax.Pat_cons uu____5908 in
                            FStar_All.pipe_left (pos_r r) uu____5907) pats1
                       uu____5847 in
                   let x =
                     let uu____5964 = tun_r p1.FStar_Parser_AST.prange in
                     FStar_Syntax_Syntax.new_bv
                       (FStar_Pervasives_Native.Some
                          (p1.FStar_Parser_AST.prange)) uu____5964 in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None)), pat,
                     annots))
          | FStar_Parser_AST.PatTuple (args, dep) ->
              let uu____5979 =
                FStar_List.fold_left
                  (fun uu____6038 ->
                     fun p2 ->
                       match uu____6038 with
                       | (loc1, env2, annots, pats) ->
                           let uu____6120 = aux loc1 env2 p2 in
                           (match uu____6120 with
                            | (loc2, env3, uu____6164, pat, ans) ->
                                (loc2, env3, (FStar_List.append ans annots),
                                  ((pat, false) :: pats))))
                  (loc, env1, [], []) args in
              (match uu____5979 with
               | (loc1, env2, annots, args1) ->
                   let args2 = FStar_List.rev args1 in
                   let l =
                     if dep
                     then
                       FStar_Parser_Const.mk_dtuple_data_lid
                         (FStar_List.length args2) p1.FStar_Parser_AST.prange
                     else
                       FStar_Parser_Const.mk_tuple_data_lid
                         (FStar_List.length args2) p1.FStar_Parser_AST.prange in
                   let constr =
                     FStar_Syntax_DsEnv.fail_or env2
                       (FStar_Syntax_DsEnv.try_lookup_lid env2) l in
                   let l1 =
                     match constr.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                     | uu____6327 -> failwith "impossible" in
                   let x =
                     let uu____6330 = tun_r p1.FStar_Parser_AST.prange in
                     FStar_Syntax_Syntax.new_bv
                       (FStar_Pervasives_Native.Some
                          (p1.FStar_Parser_AST.prange)) uu____6330 in
                   let uu____6331 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_cons (l1, args2)) in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None)),
                     uu____6331, annots))
          | FStar_Parser_AST.PatRecord [] ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                p1.FStar_Parser_AST.prange
          | FStar_Parser_AST.PatRecord fields ->
              let record =
                check_fields env1 fields p1.FStar_Parser_AST.prange in
              let fields1 =
                FStar_All.pipe_right fields
                  (FStar_List.map
                     (fun uu____6408 ->
                        match uu____6408 with
                        | (f, p2) ->
                            let uu____6419 = FStar_Ident.ident_of_lid f in
                            (uu____6419, p2))) in
              let args =
                FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                  (FStar_List.map
                     (fun uu____6439 ->
                        match uu____6439 with
                        | (f, uu____6445) ->
                            let uu____6446 =
                              FStar_All.pipe_right fields1
                                (FStar_List.tryFind
                                   (fun uu____6474 ->
                                      match uu____6474 with
                                      | (g, uu____6481) ->
                                          let uu____6482 =
                                            FStar_Ident.string_of_id f in
                                          let uu____6484 =
                                            FStar_Ident.string_of_id g in
                                          uu____6482 = uu____6484)) in
                            (match uu____6446 with
                             | FStar_Pervasives_Native.None ->
                                 FStar_Parser_AST.mk_pattern
                                   (FStar_Parser_AST.PatWild
                                      FStar_Pervasives_Native.None)
                                   p1.FStar_Parser_AST.prange
                             | FStar_Pervasives_Native.Some (uu____6491, p2)
                                 -> p2))) in
              let app =
                let uu____6498 =
                  let uu____6499 =
                    let uu____6506 =
                      let uu____6507 =
                        let uu____6508 =
                          let uu____6509 =
                            let uu____6510 =
                              FStar_Ident.ns_of_lid
                                record.FStar_Syntax_DsEnv.typename in
                            FStar_List.append uu____6510
                              [record.FStar_Syntax_DsEnv.constrname] in
                          FStar_Ident.lid_of_ids uu____6509 in
                        FStar_Parser_AST.PatName uu____6508 in
                      FStar_Parser_AST.mk_pattern uu____6507
                        p1.FStar_Parser_AST.prange in
                    (uu____6506, args) in
                  FStar_Parser_AST.PatApp uu____6499 in
                FStar_Parser_AST.mk_pattern uu____6498
                  p1.FStar_Parser_AST.prange in
              let uu____6515 = aux loc env1 app in
              (match uu____6515 with
               | (env2, e, b, p2, annots) ->
                   let p3 =
                     match p2.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_cons (fv, args1) ->
                         let uu____6592 =
                           let uu____6593 =
                             let uu____6607 =
                               let uu___1088_6608 = fv in
                               let uu____6609 =
                                 let uu____6612 =
                                   let uu____6613 =
                                     let uu____6620 =
                                       FStar_All.pipe_right
                                         record.FStar_Syntax_DsEnv.fields
                                         (FStar_List.map
                                            FStar_Pervasives_Native.fst) in
                                     ((record.FStar_Syntax_DsEnv.typename),
                                       uu____6620) in
                                   FStar_Syntax_Syntax.Record_ctor uu____6613 in
                                 FStar_Pervasives_Native.Some uu____6612 in
                               {
                                 FStar_Syntax_Syntax.fv_name =
                                   (uu___1088_6608.FStar_Syntax_Syntax.fv_name);
                                 FStar_Syntax_Syntax.fv_delta =
                                   (uu___1088_6608.FStar_Syntax_Syntax.fv_delta);
                                 FStar_Syntax_Syntax.fv_qual = uu____6609
                               } in
                             (uu____6607, args1) in
                           FStar_Syntax_Syntax.Pat_cons uu____6593 in
                         FStar_All.pipe_left pos uu____6592
                     | uu____6646 -> p2 in
                   (env2, e, b, p3, annots))
        and aux loc env1 p1 = aux' false loc env1 p1 in
        let aux_maybe_or env1 p1 =
          let loc = [] in
          match p1.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOr [] -> failwith "impossible"
          | FStar_Parser_AST.PatOr (p2::ps) ->
              let uu____6730 = aux' true loc env1 p2 in
              (match uu____6730 with
               | (loc1, env2, var, p3, ans) ->
                   let uu____6783 =
                     FStar_List.fold_left
                       (fun uu____6831 ->
                          fun p4 ->
                            match uu____6831 with
                            | (loc2, env3, ps1) ->
                                let uu____6896 = aux' true loc2 env3 p4 in
                                (match uu____6896 with
                                 | (loc3, env4, uu____6934, p5, ans1) ->
                                     (loc3, env4, ((p5, ans1) :: ps1))))
                       (loc1, env2, []) ps in
                   (match uu____6783 with
                    | (loc2, env3, ps1) ->
                        let pats = (p3, ans) :: (FStar_List.rev ps1) in
                        (env3, var, pats)))
          | uu____7095 ->
              let uu____7096 = aux' true loc env1 p1 in
              (match uu____7096 with
               | (loc1, env2, var, pat, ans) -> (env2, var, [(pat, ans)])) in
        let uu____7187 = aux_maybe_or env p in
        match uu____7187 with
        | (env1, b, pats) ->
            ((let uu____7242 =
                FStar_List.map FStar_Pervasives_Native.fst pats in
              check_linear_pattern_variables uu____7242
                p.FStar_Parser_AST.prange);
             (env1, b, pats))
and (desugar_binding_pat_maybe_top :
  Prims.bool ->
    FStar_Syntax_DsEnv.env ->
      FStar_Parser_AST.pattern -> (env_t * bnd * annotated_pat Prims.list))
  =
  fun top ->
    fun env ->
      fun p ->
        if top
        then
          let mklet x ty tacopt =
            let uu____7316 =
              let uu____7317 =
                let uu____7328 = FStar_Syntax_DsEnv.qualify env x in
                (uu____7328, (ty, tacopt)) in
              LetBinder uu____7317 in
            (env, uu____7316, []) in
          let op_to_ident x =
            let uu____7345 =
              let uu____7351 =
                let uu____7353 = FStar_Ident.string_of_id x in
                let uu____7355 = FStar_Ident.range_of_id x in
                FStar_Parser_AST.compile_op Prims.int_zero uu____7353
                  uu____7355 in
              let uu____7357 = FStar_Ident.range_of_id x in
              (uu____7351, uu____7357) in
            FStar_Ident.mk_ident uu____7345 in
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu____7368 = op_to_ident x in
              let uu____7369 =
                let uu____7370 = FStar_Ident.range_of_id x in
                tun_r uu____7370 in
              mklet uu____7368 uu____7369 FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x, uu____7372) ->
              let uu____7377 =
                let uu____7378 = FStar_Ident.range_of_id x in
                tun_r uu____7378 in
              mklet x uu____7377 FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu____7380;_},
               (t, tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env) in
              let uu____7396 = op_to_ident x in
              let uu____7397 = desugar_term env t in
              mklet uu____7396 uu____7397 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x, uu____7399);
                 FStar_Parser_AST.prange = uu____7400;_},
               (t, tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env) in
              let uu____7420 = desugar_term env t in
              mklet x uu____7420 tacopt1
          | uu____7421 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu____7434 = desugar_data_pat true env p in
           match uu____7434 with
           | (env1, binder, p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu____7464;
                      FStar_Syntax_Syntax.p = uu____7465;_},
                    uu____7466)::[] -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu____7479;
                      FStar_Syntax_Syntax.p = uu____7480;_},
                    uu____7481)::[] -> []
                 | uu____7494 -> p1 in
               (env1, binder, p2))
and (desugar_binding_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern -> (env_t * bnd * annotated_pat Prims.list))
  = fun env -> fun p -> desugar_binding_pat_maybe_top false env p
and (desugar_match_pat_maybe_top :
  Prims.bool ->
    env_t -> FStar_Parser_AST.pattern -> (env_t * annotated_pat Prims.list))
  =
  fun uu____7502 ->
    fun env ->
      fun pat ->
        let uu____7506 = desugar_data_pat false env pat in
        match uu____7506 with | (env1, uu____7523, pat1) -> (env1, pat1)
and (desugar_match_pat :
  env_t -> FStar_Parser_AST.pattern -> (env_t * annotated_pat Prims.list)) =
  fun env -> fun p -> desugar_match_pat_maybe_top false env p
and (desugar_term_aq :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.antiquotations))
  =
  fun env ->
    fun e ->
      let env1 = FStar_Syntax_DsEnv.set_expect_typ env false in
      desugar_term_maybe_top false env1 e
and (desugar_term :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun e ->
      let uu____7545 = desugar_term_aq env e in
      match uu____7545 with | (t, aq) -> (check_no_aq aq; t)
and (desugar_typ_aq :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.antiquotations))
  =
  fun env ->
    fun e ->
      let env1 = FStar_Syntax_DsEnv.set_expect_typ env true in
      desugar_term_maybe_top false env1 e
and (desugar_typ :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun e ->
      let uu____7564 = desugar_typ_aq env e in
      match uu____7564 with | (t, aq) -> (check_no_aq aq; t)
and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness * FStar_Const.width) ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun repr ->
      fun uu____7574 ->
        fun range ->
          match uu____7574 with
          | (signedness, width) ->
              let tnm =
                Prims.op_Hat "FStar."
                  (Prims.op_Hat
                     (match signedness with
                      | FStar_Const.Unsigned -> "U"
                      | FStar_Const.Signed -> "")
                     (Prims.op_Hat "Int"
                        (match width with
                         | FStar_Const.Int8 -> "8"
                         | FStar_Const.Int16 -> "16"
                         | FStar_Const.Int32 -> "32"
                         | FStar_Const.Int64 -> "64"))) in
              ((let uu____7596 =
                  let uu____7598 =
                    FStar_Const.within_bounds repr signedness width in
                  Prims.op_Negation uu____7598 in
                if uu____7596
                then
                  let uu____7601 =
                    let uu____7607 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm in
                    (FStar_Errors.Error_OutOfRange, uu____7607) in
                  FStar_Errors.log_issue range uu____7601
                else ());
               (let private_intro_nm =
                  Prims.op_Hat tnm
                    (Prims.op_Hat ".__"
                       (Prims.op_Hat
                          (match signedness with
                           | FStar_Const.Unsigned -> "u"
                           | FStar_Const.Signed -> "") "int_to_t")) in
                let intro_nm =
                  Prims.op_Hat tnm
                    (Prims.op_Hat "."
                       (Prims.op_Hat
                          (match signedness with
                           | FStar_Const.Unsigned -> "u"
                           | FStar_Const.Signed -> "") "int_to_t")) in
                let lid =
                  let uu____7628 = FStar_Ident.path_of_text intro_nm in
                  FStar_Ident.lid_of_path uu____7628 range in
                let lid1 =
                  let uu____7632 = FStar_Syntax_DsEnv.try_lookup_lid env lid in
                  match uu____7632 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____7642 =
                               FStar_Ident.path_of_text private_intro_nm in
                             FStar_Ident.lid_of_path uu____7642 range in
                           let private_fv =
                             let uu____7644 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____7644 fv.FStar_Syntax_Syntax.fv_qual in
                           let uu___1255_7645 = intro_term in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___1255_7645.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1255_7645.FStar_Syntax_Syntax.vars)
                           }
                       | uu____7646 ->
                           failwith
                             (Prims.op_Hat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None ->
                      let uu____7650 =
                        let uu____7656 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____7656) in
                      FStar_Errors.raise_error uu____7650 range in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None))) range in
                let uu____7676 =
                  let uu____7677 =
                    let uu____7694 =
                      let uu____7705 =
                        let uu____7714 =
                          FStar_Syntax_Syntax.as_implicit false in
                        (repr1, uu____7714) in
                      [uu____7705] in
                    (lid1, uu____7694) in
                  FStar_Syntax_Syntax.Tm_app uu____7677 in
                FStar_Syntax_Syntax.mk uu____7676 range))
and (desugar_term_maybe_top :
  Prims.bool ->
    env_t ->
      FStar_Parser_AST.term ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.antiquotations))
  =
  fun top_level ->
    fun env ->
      fun top ->
        let mk e = FStar_Syntax_Syntax.mk e top.FStar_Parser_AST.range in
        let noaqs = [] in
        let join_aqs aqs = FStar_List.flatten aqs in
        let setpos e =
          let uu___1271_7833 = e in
          {
            FStar_Syntax_Syntax.n = (uu___1271_7833.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___1271_7833.FStar_Syntax_Syntax.vars)
          } in
        let uu____7836 =
          let uu____7837 = unparen top in uu____7837.FStar_Parser_AST.tm in
        match uu____7836 with
        | FStar_Parser_AST.Wild -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____7842 ->
            let uu____7851 = desugar_formula env top in (uu____7851, noaqs)
        | FStar_Parser_AST.Requires (t, lopt) ->
            let uu____7860 = desugar_formula env t in (uu____7860, noaqs)
        | FStar_Parser_AST.Ensures (t, lopt) ->
            let uu____7869 = desugar_formula env t in (uu____7869, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i, FStar_Pervasives_Native.Some size)) ->
            let uu____7896 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range in
            (uu____7896, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____7898 = mk (FStar_Syntax_Syntax.Tm_constant c) in
            (uu____7898, noaqs)
        | FStar_Parser_AST.Op (id, args) when
            let uu____7905 = FStar_Ident.string_of_id id in
            uu____7905 = "=!=" ->
            let r = FStar_Ident.range_of_id id in
            let e =
              let uu____7911 =
                let uu____7912 =
                  let uu____7919 = FStar_Ident.mk_ident ("==", r) in
                  (uu____7919, args) in
                FStar_Parser_AST.Op uu____7912 in
              FStar_Parser_AST.mk_term uu____7911 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level in
            let uu____7924 =
              let uu____7925 =
                let uu____7926 =
                  let uu____7933 = FStar_Ident.mk_ident ("~", r) in
                  (uu____7933, [e]) in
                FStar_Parser_AST.Op uu____7926 in
              FStar_Parser_AST.mk_term uu____7925 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level in
            desugar_term_aq env uu____7924
        | FStar_Parser_AST.Op (op_star, lhs::rhs::[]) when
            (let uu____7945 = FStar_Ident.string_of_id op_star in
             uu____7945 = "*") &&
              (let uu____7950 = op_as_term env (Prims.of_int (2)) op_star in
               FStar_All.pipe_right uu____7950 FStar_Option.isNone)
            ->
            let rec flatten t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op (id, t1::t2::[]) when
                  (let uu____7974 = FStar_Ident.string_of_id id in
                   uu____7974 = "*") &&
                    (let uu____7979 =
                       op_as_term env (Prims.of_int (2)) op_star in
                     FStar_All.pipe_right uu____7979 FStar_Option.isNone)
                  ->
                  let uu____7986 = flatten t1 in
                  FStar_List.append uu____7986 [t2]
              | uu____7989 -> [t] in
            let terms = flatten lhs in
            let t =
              let uu___1316_7994 = top in
              let uu____7995 =
                let uu____7996 =
                  let uu____8007 =
                    FStar_List.map
                      (fun uu____8018 -> FStar_Util.Inr uu____8018) terms in
                  (uu____8007, rhs) in
                FStar_Parser_AST.Sum uu____7996 in
              {
                FStar_Parser_AST.tm = uu____7995;
                FStar_Parser_AST.range =
                  (uu___1316_7994.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1316_7994.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env t
        | FStar_Parser_AST.Tvar a ->
            let uu____8026 =
              let uu____8027 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a in
              FStar_All.pipe_left setpos uu____8027 in
            (uu____8026, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____8033 =
              let uu____8039 =
                let uu____8041 =
                  let uu____8043 = FStar_Ident.string_of_id u in
                  Prims.op_Hat uu____8043 " in non-universe context" in
                Prims.op_Hat "Unexpected universe variable " uu____8041 in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____8039) in
            FStar_Errors.raise_error uu____8033 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s, args) ->
            let uu____8058 = op_as_term env (FStar_List.length args) s in
            (match uu____8058 with
             | FStar_Pervasives_Native.None ->
                 let uu____8065 =
                   let uu____8071 =
                     let uu____8073 = FStar_Ident.string_of_id s in
                     Prims.op_Hat "Unexpected or unbound operator: "
                       uu____8073 in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____8071) in
                 FStar_Errors.raise_error uu____8065
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > Prims.int_zero
                 then
                   let uu____8088 =
                     let uu____8113 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t ->
                               let uu____8175 = desugar_term_aq env t in
                               match uu____8175 with
                               | (t', s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1))) in
                     FStar_All.pipe_right uu____8113 FStar_List.unzip in
                   (match uu____8088 with
                    | (args1, aqs) ->
                        let uu____8308 =
                          mk (FStar_Syntax_Syntax.Tm_app (op, args1)) in
                        (uu____8308, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n, (a, uu____8325)::[]) when
            let uu____8340 = FStar_Ident.string_of_lid n in
            uu____8340 = "SMTPat" ->
            let uu____8344 =
              let uu___1345_8345 = top in
              let uu____8346 =
                let uu____8347 =
                  let uu____8354 =
                    let uu___1347_8355 = top in
                    let uu____8356 =
                      let uu____8357 = smt_pat_lid top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____8357 in
                    {
                      FStar_Parser_AST.tm = uu____8356;
                      FStar_Parser_AST.range =
                        (uu___1347_8355.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1347_8355.FStar_Parser_AST.level)
                    } in
                  (uu____8354, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____8347 in
              {
                FStar_Parser_AST.tm = uu____8346;
                FStar_Parser_AST.range =
                  (uu___1345_8345.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1345_8345.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____8344
        | FStar_Parser_AST.Construct (n, (a, uu____8360)::[]) when
            let uu____8375 = FStar_Ident.string_of_lid n in
            uu____8375 = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____8382 =
                let uu___1357_8383 = top in
                let uu____8384 =
                  let uu____8385 =
                    let uu____8392 =
                      let uu___1359_8393 = top in
                      let uu____8394 =
                        let uu____8395 =
                          smt_pat_lid top.FStar_Parser_AST.range in
                        FStar_Parser_AST.Var uu____8395 in
                      {
                        FStar_Parser_AST.tm = uu____8394;
                        FStar_Parser_AST.range =
                          (uu___1359_8393.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___1359_8393.FStar_Parser_AST.level)
                      } in
                    (uu____8392, a, FStar_Parser_AST.Nothing) in
                  FStar_Parser_AST.App uu____8385 in
                {
                  FStar_Parser_AST.tm = uu____8384;
                  FStar_Parser_AST.range =
                    (uu___1357_8383.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___1357_8383.FStar_Parser_AST.level)
                } in
              desugar_term_maybe_top top_level env uu____8382))
        | FStar_Parser_AST.Construct (n, (a, uu____8398)::[]) when
            let uu____8413 = FStar_Ident.string_of_lid n in
            uu____8413 = "SMTPatOr" ->
            let uu____8417 =
              let uu___1368_8418 = top in
              let uu____8419 =
                let uu____8420 =
                  let uu____8427 =
                    let uu___1370_8428 = top in
                    let uu____8429 =
                      let uu____8430 =
                        smt_pat_or_lid top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____8430 in
                    {
                      FStar_Parser_AST.tm = uu____8429;
                      FStar_Parser_AST.range =
                        (uu___1370_8428.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1370_8428.FStar_Parser_AST.level)
                    } in
                  (uu____8427, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____8420 in
              {
                FStar_Parser_AST.tm = uu____8419;
                FStar_Parser_AST.range =
                  (uu___1368_8418.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1368_8418.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____8417
        | FStar_Parser_AST.Name lid when
            let uu____8432 = FStar_Ident.string_of_lid lid in
            uu____8432 = "Type0" ->
            let uu____8436 =
              mk (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero) in
            (uu____8436, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8438 = FStar_Ident.string_of_lid lid in
            uu____8438 = "Type" ->
            let uu____8442 =
              mk (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown) in
            (uu____8442, noaqs)
        | FStar_Parser_AST.Construct (lid, (t, FStar_Parser_AST.UnivApp)::[])
            when
            let uu____8459 = FStar_Ident.string_of_lid lid in
            uu____8459 = "Type" ->
            let uu____8463 =
              let uu____8464 =
                let uu____8465 = desugar_universe t in
                FStar_Syntax_Syntax.Tm_type uu____8465 in
              mk uu____8464 in
            (uu____8463, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8467 = FStar_Ident.string_of_lid lid in
            uu____8467 = "Effect" ->
            let uu____8471 =
              mk (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect) in
            (uu____8471, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8473 = FStar_Ident.string_of_lid lid in
            uu____8473 = "True" ->
            let uu____8477 =
              let uu____8478 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range in
              FStar_Syntax_Syntax.fvar uu____8478
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None in
            (uu____8477, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8480 = FStar_Ident.string_of_lid lid in
            uu____8480 = "False" ->
            let uu____8484 =
              let uu____8485 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range in
              FStar_Syntax_Syntax.fvar uu____8485
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None in
            (uu____8484, noaqs)
        | FStar_Parser_AST.Projector (eff_name, id) when
            (let uu____8490 = FStar_Ident.string_of_id id in
             is_special_effect_combinator uu____8490) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            let txt = FStar_Ident.string_of_id id in
            let uu____8494 =
              FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name in
            (match uu____8494 with
             | FStar_Pervasives_Native.Some ed ->
                 let lid = FStar_Syntax_Util.dm4f_lid ed txt in
                 let uu____8503 =
                   FStar_Syntax_Syntax.fvar lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None in
                 (uu____8503, noaqs)
             | FStar_Pervasives_Native.None ->
                 let uu____8505 =
                   let uu____8507 = FStar_Ident.string_of_lid eff_name in
                   FStar_Util.format2
                     "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                     uu____8507 txt in
                 failwith uu____8505)
        | FStar_Parser_AST.Var l ->
            let uu____8515 = desugar_name mk setpos env true l in
            (uu____8515, noaqs)
        | FStar_Parser_AST.Name l ->
            let uu____8523 = desugar_name mk setpos env true l in
            (uu____8523, noaqs)
        | FStar_Parser_AST.Projector (l, i) ->
            let name =
              let uu____8540 = FStar_Syntax_DsEnv.try_lookup_datacon env l in
              match uu____8540 with
              | FStar_Pervasives_Native.Some uu____8550 ->
                  FStar_Pervasives_Native.Some (true, l)
              | FStar_Pervasives_Native.None ->
                  let uu____8558 =
                    FStar_Syntax_DsEnv.try_lookup_root_effect_name env l in
                  (match uu____8558 with
                   | FStar_Pervasives_Native.Some new_name ->
                       FStar_Pervasives_Native.Some (false, new_name)
                   | uu____8576 -> FStar_Pervasives_Native.None) in
            (match name with
             | FStar_Pervasives_Native.Some (resolve, new_name) ->
                 let uu____8597 =
                   let uu____8598 =
                     FStar_Syntax_Util.mk_field_projector_name_from_ident
                       new_name i in
                   desugar_name mk setpos env resolve uu____8598 in
                 (uu____8597, noaqs)
             | uu____8604 ->
                 let uu____8612 =
                   let uu____8618 =
                     let uu____8620 = FStar_Ident.string_of_lid l in
                     FStar_Util.format1
                       "Data constructor or effect %s not found" uu____8620 in
                   (FStar_Errors.Fatal_EffectNotFound, uu____8618) in
                 FStar_Errors.raise_error uu____8612
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Discrim lid ->
            let uu____8629 = FStar_Syntax_DsEnv.try_lookup_datacon env lid in
            (match uu____8629 with
             | FStar_Pervasives_Native.None ->
                 let uu____8636 =
                   let uu____8642 =
                     let uu____8644 = FStar_Ident.string_of_lid lid in
                     FStar_Util.format1 "Data constructor %s not found"
                       uu____8644 in
                   (FStar_Errors.Fatal_DataContructorNotFound, uu____8642) in
                 FStar_Errors.raise_error uu____8636
                   top.FStar_Parser_AST.range
             | uu____8652 ->
                 let lid' = FStar_Syntax_Util.mk_discriminator lid in
                 let uu____8656 = desugar_name mk setpos env true lid' in
                 (uu____8656, noaqs))
        | FStar_Parser_AST.Construct (l, args) ->
            let uu____8677 = FStar_Syntax_DsEnv.try_lookup_datacon env l in
            (match uu____8677 with
             | FStar_Pervasives_Native.Some head ->
                 let head1 = mk (FStar_Syntax_Syntax.Tm_fvar head) in
                 (match args with
                  | [] -> (head1, noaqs)
                  | uu____8696 ->
                      let uu____8703 =
                        FStar_Util.take
                          (fun uu____8727 ->
                             match uu____8727 with
                             | (uu____8733, imp) ->
                                 imp = FStar_Parser_AST.UnivApp) args in
                      (match uu____8703 with
                       | (universes, args1) ->
                           let universes1 =
                             FStar_List.map
                               (fun x ->
                                  desugar_universe
                                    (FStar_Pervasives_Native.fst x))
                               universes in
                           let uu____8778 =
                             let uu____8803 =
                               FStar_List.map
                                 (fun uu____8846 ->
                                    match uu____8846 with
                                    | (t, imp) ->
                                        let uu____8863 =
                                          desugar_term_aq env t in
                                        (match uu____8863 with
                                         | (te, aq) ->
                                             ((arg_withimp_e imp te), aq)))
                                 args1 in
                             FStar_All.pipe_right uu____8803 FStar_List.unzip in
                           (match uu____8778 with
                            | (args2, aqs) ->
                                let head2 =
                                  if universes1 = []
                                  then head1
                                  else
                                    mk
                                      (FStar_Syntax_Syntax.Tm_uinst
                                         (head1, universes1)) in
                                let uu____9006 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_app
                                       (head2, args2)) in
                                (uu____9006, (join_aqs aqs)))))
             | FStar_Pervasives_Native.None ->
                 let err =
                   let uu____9025 =
                     FStar_Syntax_DsEnv.try_lookup_effect_name env l in
                   match uu____9025 with
                   | FStar_Pervasives_Native.None ->
                       let uu____9033 =
                         let uu____9035 =
                           let uu____9037 = FStar_Ident.string_of_lid l in
                           Prims.op_Hat uu____9037 " not found" in
                         Prims.op_Hat "Constructor " uu____9035 in
                       (FStar_Errors.Fatal_ConstructorNotFound, uu____9033)
                   | FStar_Pervasives_Native.Some uu____9042 ->
                       let uu____9043 =
                         let uu____9045 =
                           let uu____9047 = FStar_Ident.string_of_lid l in
                           Prims.op_Hat uu____9047
                             " used at an unexpected position" in
                         Prims.op_Hat "Effect " uu____9045 in
                       (FStar_Errors.Fatal_UnexpectedEffect, uu____9043) in
                 FStar_Errors.raise_error err top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Sum (binders, t) when
            FStar_Util.for_all
              (fun uu___8_9076 ->
                 match uu___8_9076 with
                 | FStar_Util.Inr uu____9082 -> true
                 | uu____9084 -> false) binders
            ->
            let terms =
              let uu____9093 =
                FStar_All.pipe_right binders
                  (FStar_List.map
                     (fun uu___9_9110 ->
                        match uu___9_9110 with
                        | FStar_Util.Inr x -> x
                        | FStar_Util.Inl uu____9116 -> failwith "Impossible")) in
              FStar_List.append uu____9093 [t] in
            let uu____9118 =
              let uu____9143 =
                FStar_All.pipe_right terms
                  (FStar_List.map
                     (fun t1 ->
                        let uu____9200 = desugar_typ_aq env t1 in
                        match uu____9200 with
                        | (t', aq) ->
                            let uu____9211 = FStar_Syntax_Syntax.as_arg t' in
                            (uu____9211, aq))) in
              FStar_All.pipe_right uu____9143 FStar_List.unzip in
            (match uu____9118 with
             | (targs, aqs) ->
                 let tup =
                   let uu____9321 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____9321 in
                 let uu____9330 =
                   mk (FStar_Syntax_Syntax.Tm_app (tup, targs)) in
                 (uu____9330, (join_aqs aqs)))
        | FStar_Parser_AST.Sum (binders, t) ->
            let uu____9357 =
              let uu____9374 =
                let uu____9381 =
                  let uu____9388 =
                    FStar_All.pipe_left
                      (fun uu____9397 -> FStar_Util.Inl uu____9397)
                      (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                         FStar_Pervasives_Native.None) in
                  [uu____9388] in
                FStar_List.append binders uu____9381 in
              FStar_List.fold_left
                (fun uu____9442 ->
                   fun b ->
                     match uu____9442 with
                     | (env1, tparams, typs) ->
                         let uu____9503 =
                           match b with
                           | FStar_Util.Inl b1 -> desugar_binder env1 b1
                           | FStar_Util.Inr t1 ->
                               let uu____9518 = desugar_typ env1 t1 in
                               (FStar_Pervasives_Native.None, uu____9518) in
                         (match uu____9503 with
                          | (xopt, t1) ->
                              let uu____9543 =
                                match xopt with
                                | FStar_Pervasives_Native.None ->
                                    let uu____9552 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        (setpos FStar_Syntax_Syntax.tun) in
                                    (env1, uu____9552)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x in
                              (match uu____9543 with
                               | (env2, x) ->
                                   let uu____9572 =
                                     let uu____9575 =
                                       let uu____9578 =
                                         let uu____9579 =
                                           no_annot_abs tparams t1 in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____9579 in
                                       [uu____9578] in
                                     FStar_List.append typs uu____9575 in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___1499_9605 = x in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___1499_9605.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___1499_9605.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____9572)))) (env, [], []) uu____9374 in
            (match uu____9357 with
             | (env1, uu____9633, targs) ->
                 let tup =
                   let uu____9656 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____9656 in
                 let uu____9657 =
                   FStar_All.pipe_left mk
                     (FStar_Syntax_Syntax.Tm_app (tup, targs)) in
                 (uu____9657, noaqs))
        | FStar_Parser_AST.Product (binders, t) ->
            let uu____9676 = uncurry binders t in
            (match uu____9676 with
             | (bs, t1) ->
                 let rec aux env1 bs1 uu___10_9720 =
                   match uu___10_9720 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range true env1 t1 in
                       let uu____9737 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod in
                       FStar_All.pipe_left setpos uu____9737
                   | hd::tl ->
                       let bb = desugar_binder env1 hd in
                       let uu____9761 =
                         as_binder env1 hd.FStar_Parser_AST.aqual bb in
                       (match uu____9761 with
                        | (b, env2) -> aux env2 (b :: bs1) tl) in
                 let uu____9794 = aux env [] bs in (uu____9794, noaqs))
        | FStar_Parser_AST.Refine (b, f) ->
            let uu____9803 = desugar_binder env b in
            (match uu____9803 with
             | (FStar_Pervasives_Native.None, uu____9814) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____9829 =
                   as_binder env FStar_Pervasives_Native.None b1 in
                 (match uu____9829 with
                  | ((x, uu____9845), env1) ->
                      let f1 = desugar_formula env1 f in
                      let uu____9858 =
                        let uu____9859 = FStar_Syntax_Util.refine x f1 in
                        FStar_All.pipe_left setpos uu____9859 in
                      (uu____9858, noaqs)))
        | FStar_Parser_AST.Abs (binders, body) ->
            let bvss = FStar_List.map gather_pattern_bound_vars binders in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set::sets2 ->
                    let i = FStar_Util.set_intersect acc set in
                    let uu____9937 = FStar_Util.set_is_empty i in
                    if uu____9937
                    then
                      let uu____9942 = FStar_Util.set_union acc set in
                      aux uu____9942 sets2
                    else
                      (let uu____9947 =
                         let uu____9948 = FStar_Util.set_elements i in
                         FStar_List.hd uu____9948 in
                       FStar_Pervasives_Native.Some uu____9947) in
              let uu____9951 = FStar_Syntax_Syntax.new_id_set () in
              aux uu____9951 sets in
            ((let uu____9955 = check_disjoint bvss in
              match uu____9955 with
              | FStar_Pervasives_Native.None -> ()
              | FStar_Pervasives_Native.Some id ->
                  let uu____9959 =
                    let uu____9965 =
                      let uu____9967 = FStar_Ident.string_of_id id in
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        uu____9967 in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____9965) in
                  let uu____9971 = FStar_Ident.range_of_id id in
                  FStar_Errors.raise_error uu____9959 uu____9971);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern) in
              let uu____9979 =
                FStar_List.fold_left
                  (fun uu____9999 ->
                     fun pat ->
                       match uu____9999 with
                       | (env1, ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____10025,
                                 (t, FStar_Pervasives_Native.None))
                                ->
                                let uu____10035 =
                                  let uu____10038 = free_type_vars env1 t in
                                  FStar_List.append uu____10038 ftvs in
                                (env1, uu____10035)
                            | FStar_Parser_AST.PatAscribed
                                (uu____10043,
                                 (t, FStar_Pervasives_Native.Some tac))
                                ->
                                let uu____10054 =
                                  let uu____10057 = free_type_vars env1 t in
                                  let uu____10060 =
                                    let uu____10063 = free_type_vars env1 tac in
                                    FStar_List.append uu____10063 ftvs in
                                  FStar_List.append uu____10057 uu____10060 in
                                (env1, uu____10054)
                            | uu____10068 -> (env1, ftvs))) (env, [])
                  binders1 in
              match uu____9979 with
              | (uu____10077, ftv) ->
                  let ftv1 = sort_ftv ftv in
                  let binders2 =
                    let uu____10089 =
                      FStar_All.pipe_right ftv1
                        (FStar_List.map
                           (fun a ->
                              FStar_Parser_AST.mk_pattern
                                (FStar_Parser_AST.PatTvar
                                   (a,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Parser_AST.Implicit)))
                                top.FStar_Parser_AST.range)) in
                    FStar_List.append uu____10089 binders1 in
                  let rec aux env1 bs sc_pat_opt pats =
                    match pats with
                    | [] ->
                        let uu____10169 = desugar_term_aq env1 body in
                        (match uu____10169 with
                         | (body1, aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc, pat) ->
                                   let body2 =
                                     let uu____10204 =
                                       let uu____10205 =
                                         FStar_Syntax_Syntax.pat_bvs pat in
                                       FStar_All.pipe_right uu____10205
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder) in
                                     FStar_Syntax_Subst.close uu____10204
                                       body1 in
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_match
                                        (sc,
                                          [(pat,
                                             FStar_Pervasives_Native.None,
                                             body2)]))
                                     body2.FStar_Syntax_Syntax.pos
                               | FStar_Pervasives_Native.None -> body1 in
                             let uu____10274 =
                               let uu____10275 =
                                 no_annot_abs (FStar_List.rev bs) body2 in
                               setpos uu____10275 in
                             (uu____10274, aq))
                    | p::rest ->
                        let uu____10288 = desugar_binding_pat env1 p in
                        (match uu____10288 with
                         | (env2, b, pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1, uu____10320)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____10335 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange in
                             let uu____10344 =
                               match b with
                               | LetBinder uu____10385 ->
                                   failwith "Impossible"
                               | LocalBinder (x, aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None,
                                        uu____10454) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some p1,
                                        FStar_Pervasives_Native.None) ->
                                         let uu____10508 =
                                           let uu____10517 =
                                             FStar_Syntax_Syntax.bv_to_name x in
                                           (uu____10517, p1) in
                                         FStar_Pervasives_Native.Some
                                           uu____10508
                                     | (FStar_Pervasives_Native.Some p1,
                                        FStar_Pervasives_Native.Some
                                        (sc, p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____10579, uu____10580) ->
                                              let tup2 =
                                                let uu____10582 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.of_int (2))
                                                    top.FStar_Parser_AST.range in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10582
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor) in
                                              let sc1 =
                                                let uu____10587 =
                                                  let uu____10588 =
                                                    let uu____10605 =
                                                      mk
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tup2) in
                                                    let uu____10608 =
                                                      let uu____10619 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          sc in
                                                      let uu____10628 =
                                                        let uu____10639 =
                                                          let uu____10648 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____10648 in
                                                        [uu____10639] in
                                                      uu____10619 ::
                                                        uu____10628 in
                                                    (uu____10605,
                                                      uu____10608) in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____10588 in
                                                FStar_Syntax_Syntax.mk
                                                  uu____10587
                                                  top.FStar_Parser_AST.range in
                                              let p2 =
                                                let uu____10696 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____10696 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____10747, args),
                                             FStar_Syntax_Syntax.Pat_cons
                                             (uu____10749, pats1)) ->
                                              let tupn =
                                                let uu____10794 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.int_one +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10794
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor) in
                                              let sc1 =
                                                let uu____10807 =
                                                  let uu____10808 =
                                                    let uu____10825 =
                                                      mk
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn) in
                                                    let uu____10828 =
                                                      let uu____10839 =
                                                        let uu____10850 =
                                                          let uu____10859 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____10859 in
                                                        [uu____10850] in
                                                      FStar_List.append args
                                                        uu____10839 in
                                                    (uu____10825,
                                                      uu____10828) in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____10808 in
                                                mk uu____10807 in
                                              let p2 =
                                                let uu____10907 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats1 [(p1, false)])))
                                                  uu____10907 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____10954 ->
                                              failwith "Impossible") in
                                   ((x, aq), sc_pat_opt1) in
                             (match uu____10344 with
                              | (b1, sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest)) in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____11046, uu____11047, FStar_Parser_AST.UnivApp) ->
            let rec aux universes e =
              let uu____11069 =
                let uu____11070 = unparen e in
                uu____11070.FStar_Parser_AST.tm in
              match uu____11069 with
              | FStar_Parser_AST.App (e1, t, FStar_Parser_AST.UnivApp) ->
                  let univ_arg = desugar_universe t in
                  aux (univ_arg :: universes) e1
              | uu____11080 ->
                  let uu____11081 = desugar_term_aq env e in
                  (match uu____11081 with
                   | (head, aq) ->
                       let uu____11094 =
                         mk (FStar_Syntax_Syntax.Tm_uinst (head, universes)) in
                       (uu____11094, aq)) in
            aux [] top
        | FStar_Parser_AST.App uu____11101 ->
            let rec aux args aqs e =
              let uu____11178 =
                let uu____11179 = unparen e in
                uu____11179.FStar_Parser_AST.tm in
              match uu____11178 with
              | FStar_Parser_AST.App (e1, t, imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____11197 = desugar_term_aq env t in
                  (match uu____11197 with
                   | (t1, aq) ->
                       let arg = arg_withimp_e imp t1 in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____11245 ->
                  let uu____11246 = desugar_term_aq env e in
                  (match uu____11246 with
                   | (head, aq) ->
                       let uu____11267 =
                         mk (FStar_Syntax_Syntax.Tm_app (head, args)) in
                       (uu____11267, (join_aqs (aq :: aqs)))) in
            aux [] [] top
        | FStar_Parser_AST.Bind (x, t1, t2) ->
            let xpat =
              let uu____11320 = FStar_Ident.range_of_id x in
              FStar_Parser_AST.mk_pattern
                (FStar_Parser_AST.PatVar (x, FStar_Pervasives_Native.None))
                uu____11320 in
            let k =
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Abs ([xpat], t2))
                t2.FStar_Parser_AST.range t2.FStar_Parser_AST.level in
            let bind_lid =
              let uu____11327 = FStar_Ident.range_of_id x in
              FStar_Ident.lid_of_path ["bind"] uu____11327 in
            let bind =
              let uu____11332 = FStar_Ident.range_of_id x in
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Var bind_lid)
                uu____11332 FStar_Parser_AST.Expr in
            let uu____11333 =
              FStar_Parser_AST.mkExplicitApp bind [t1; k]
                top.FStar_Parser_AST.range in
            desugar_term_aq env uu____11333
        | FStar_Parser_AST.Seq (t1, t2) ->
            let t =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Let
                   (FStar_Parser_AST.NoLetQualifier,
                     [(FStar_Pervasives_Native.None,
                        ((FStar_Parser_AST.mk_pattern
                            (FStar_Parser_AST.PatWild
                               FStar_Pervasives_Native.None)
                            t1.FStar_Parser_AST.range), t1))], t2))
                top.FStar_Parser_AST.range FStar_Parser_AST.Expr in
            let uu____11385 = desugar_term_aq env t in
            (match uu____11385 with
             | (tm, s) ->
                 let uu____11396 =
                   mk
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence))) in
                 (uu____11396, s))
        | FStar_Parser_AST.LetOpen (lid, e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid in
            let uu____11402 =
              let uu____11415 = FStar_Syntax_DsEnv.expect_typ env1 in
              if uu____11415 then desugar_typ_aq else desugar_term_aq in
            uu____11402 env1 e
        | FStar_Parser_AST.Let (qual, lbs, body) ->
            let is_rec = qual = FStar_Parser_AST.Rec in
            let ds_let_rec_or_app uu____11482 =
              let bindings = lbs in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____11625 ->
                        match uu____11625 with
                        | (attr_opt, (p, def)) ->
                            let uu____11683 = is_app_pattern p in
                            if uu____11683
                            then
                              let uu____11716 =
                                destruct_app_pattern env top_level p in
                              (attr_opt, uu____11716, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1, def1) ->
                                   let uu____11799 =
                                     destruct_app_pattern env top_level p1 in
                                   (attr_opt, uu____11799, def1)
                               | uu____11844 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id, uu____11882);
                                           FStar_Parser_AST.prange =
                                             uu____11883;_},
                                         t)
                                        ->
                                        if top_level
                                        then
                                          let uu____11932 =
                                            let uu____11953 =
                                              let uu____11958 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id in
                                              FStar_Util.Inr uu____11958 in
                                            (uu____11953, [],
                                              (FStar_Pervasives_Native.Some t)) in
                                          (attr_opt, uu____11932, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id, uu____12050) ->
                                        if top_level
                                        then
                                          let uu____12086 =
                                            let uu____12107 =
                                              let uu____12112 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id in
                                              FStar_Util.Inr uu____12112 in
                                            (uu____12107, [],
                                              FStar_Pervasives_Native.None) in
                                          (attr_opt, uu____12086, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____12203 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange)))) in
              let uu____12236 =
                FStar_List.fold_left
                  (fun uu____12325 ->
                     fun uu____12326 ->
                       match (uu____12325, uu____12326) with
                       | ((env1, fnames, rec_bindings, used_markers),
                          (_attr_opt, (f, uu____12456, uu____12457),
                           uu____12458)) ->
                           let uu____12592 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____12632 =
                                   FStar_Syntax_DsEnv.push_bv' env1 x in
                                 (match uu____12632 with
                                  | (env2, xx, used_marker) ->
                                      let dummy_ref = FStar_Util.mk_ref true in
                                      let uu____12667 =
                                        let uu____12670 =
                                          FStar_Syntax_Syntax.mk_binder xx in
                                        uu____12670 :: rec_bindings in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____12667, (used_marker ::
                                        used_markers)))
                             | FStar_Util.Inr l ->
                                 let uu____12686 =
                                   let uu____12694 =
                                     FStar_Ident.ident_of_lid l in
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 uu____12694
                                     FStar_Syntax_Syntax.delta_equational in
                                 (match uu____12686 with
                                  | (env2, used_marker) ->
                                      (env2, (FStar_Util.Inr l),
                                        rec_bindings, (used_marker ::
                                        used_markers))) in
                           (match uu____12592 with
                            | (env2, lbname, rec_bindings1, used_markers1) ->
                                (env2, (lbname :: fnames), rec_bindings1,
                                  used_markers1))) (env, [], [], []) funs in
              match uu____12236 with
              | (env', fnames, rec_bindings, used_markers) ->
                  let fnames1 = FStar_List.rev fnames in
                  let rec_bindings1 = FStar_List.rev rec_bindings in
                  let used_markers1 = FStar_List.rev used_markers in
                  let desugar_one_def env1 lbname uu____12940 =
                    match uu____12940 with
                    | (attrs_opt, (uu____12980, args, result_t), def) ->
                        let args1 =
                          FStar_All.pipe_right args
                            (FStar_List.map replace_unit_pattern) in
                        let pos = def.FStar_Parser_AST.range in
                        let def1 =
                          match result_t with
                          | FStar_Pervasives_Native.None -> def
                          | FStar_Pervasives_Native.Some (t, tacopt) ->
                              let t1 =
                                let uu____13072 = is_comp_type env1 t in
                                if uu____13072
                                then
                                  ((let uu____13076 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x ->
                                              let uu____13086 =
                                                is_var_pattern x in
                                              Prims.op_Negation uu____13086)) in
                                    match uu____13076 with
                                    | FStar_Pervasives_Native.None -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____13093 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____13096 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid in
                                         FStar_Option.isSome uu____13096))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             Prims.int_zero)) in
                                   if uu____13093
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t) in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed (def, t1, tacopt))
                                def.FStar_Parser_AST.range
                                FStar_Parser_AST.Expr in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____13107 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level in
                        let uu____13110 = desugar_term_aq env1 def2 in
                        (match uu____13110 with
                         | (body1, aq) ->
                             let lbname1 =
                               match lbname with
                               | FStar_Util.Inl x -> FStar_Util.Inl x
                               | FStar_Util.Inr l ->
                                   let uu____13132 =
                                     let uu____13133 =
                                       FStar_Syntax_Util.incr_delta_qualifier
                                         body1 in
                                     FStar_Syntax_Syntax.lid_as_fv l
                                       uu____13133
                                       FStar_Pervasives_Native.None in
                                   FStar_Util.Inr uu____13132 in
                             let body2 =
                               if is_rec
                               then
                                 FStar_Syntax_Subst.close rec_bindings1 body1
                               else body1 in
                             let attrs =
                               match attrs_opt with
                               | FStar_Pervasives_Native.None -> []
                               | FStar_Pervasives_Native.Some l ->
                                   FStar_List.map (desugar_term env1) l in
                             ((mk_lb
                                 (attrs, lbname1,
                                   (setpos FStar_Syntax_Syntax.tun), body2,
                                   pos)), aq)) in
                  let uu____13174 =
                    let uu____13191 =
                      FStar_List.map2
                        (desugar_one_def (if is_rec then env' else env))
                        fnames1 funs in
                    FStar_All.pipe_right uu____13191 FStar_List.unzip in
                  (match uu____13174 with
                   | (lbs1, aqss) ->
                       let uu____13333 = desugar_term_aq env' body in
                       (match uu____13333 with
                        | (body1, aq) ->
                            (if is_rec
                             then
                               FStar_List.iter2
                                 (fun uu____13439 ->
                                    fun used_marker ->
                                      match uu____13439 with
                                      | (_attr_opt,
                                         (f, uu____13513, uu____13514),
                                         uu____13515) ->
                                          let uu____13572 =
                                            let uu____13574 =
                                              FStar_ST.op_Bang used_marker in
                                            Prims.op_Negation uu____13574 in
                                          if uu____13572
                                          then
                                            let uu____13598 =
                                              match f with
                                              | FStar_Util.Inl x ->
                                                  let uu____13616 =
                                                    FStar_Ident.string_of_id
                                                      x in
                                                  let uu____13618 =
                                                    FStar_Ident.range_of_id x in
                                                  (uu____13616, "Local",
                                                    uu____13618)
                                              | FStar_Util.Inr l ->
                                                  let uu____13623 =
                                                    FStar_Ident.string_of_lid
                                                      l in
                                                  let uu____13625 =
                                                    FStar_Ident.range_of_lid
                                                      l in
                                                  (uu____13623, "Global",
                                                    uu____13625) in
                                            (match uu____13598 with
                                             | (nm, gl, rng) ->
                                                 let uu____13636 =
                                                   let uu____13642 =
                                                     FStar_Util.format2
                                                       "%s binding %s is recursive but not used in its body"
                                                       gl nm in
                                                   (FStar_Errors.Warning_UnusedLetRec,
                                                     uu____13642) in
                                                 FStar_Errors.log_issue rng
                                                   uu____13636)
                                          else ()) funs used_markers1
                             else ();
                             (let uu____13650 =
                                let uu____13653 =
                                  let uu____13654 =
                                    let uu____13668 =
                                      FStar_Syntax_Subst.close rec_bindings1
                                        body1 in
                                    ((is_rec, lbs1), uu____13668) in
                                  FStar_Syntax_Syntax.Tm_let uu____13654 in
                                FStar_All.pipe_left mk uu____13653 in
                              (uu____13650,
                                (FStar_List.append aq
                                   (FStar_List.flatten aqss))))))) in
            let ds_non_rec attrs_opt pat t1 t2 =
              let attrs =
                match attrs_opt with
                | FStar_Pervasives_Native.None -> []
                | FStar_Pervasives_Native.Some l ->
                    FStar_List.map (desugar_term env) l in
              let uu____13770 = desugar_term_aq env t1 in
              match uu____13770 with
              | (t11, aq0) ->
                  let uu____13791 =
                    desugar_binding_pat_maybe_top top_level env pat in
                  (match uu____13791 with
                   | (env1, binder, pat1) ->
                       let uu____13821 =
                         match binder with
                         | LetBinder (l, (t, _tacopt)) ->
                             let uu____13863 = desugar_term_aq env1 t2 in
                             (match uu____13863 with
                              | (body1, aq) ->
                                  let fv =
                                    let uu____13885 =
                                      FStar_Syntax_Util.incr_delta_qualifier
                                        t11 in
                                    FStar_Syntax_Syntax.lid_as_fv l
                                      uu____13885
                                      FStar_Pervasives_Native.None in
                                  let uu____13886 =
                                    FStar_All.pipe_left mk
                                      (FStar_Syntax_Syntax.Tm_let
                                         ((false,
                                            [mk_lb
                                               (attrs, (FStar_Util.Inr fv),
                                                 t, t11,
                                                 (t11.FStar_Syntax_Syntax.pos))]),
                                           body1)) in
                                  (uu____13886, aq))
                         | LocalBinder (x, uu____13927) ->
                             let uu____13928 = desugar_term_aq env1 t2 in
                             (match uu____13928 with
                              | (body1, aq) ->
                                  let body2 =
                                    match pat1 with
                                    | [] -> body1
                                    | ({
                                         FStar_Syntax_Syntax.v =
                                           FStar_Syntax_Syntax.Pat_wild
                                           uu____13950;
                                         FStar_Syntax_Syntax.p = uu____13951;_},
                                       uu____13952)::[] -> body1
                                    | uu____13965 ->
                                        let uu____13968 =
                                          let uu____13969 =
                                            let uu____13992 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x in
                                            let uu____13995 =
                                              desugar_disjunctive_pattern
                                                pat1
                                                FStar_Pervasives_Native.None
                                                body1 in
                                            (uu____13992, uu____13995) in
                                          FStar_Syntax_Syntax.Tm_match
                                            uu____13969 in
                                        FStar_Syntax_Syntax.mk uu____13968
                                          top.FStar_Parser_AST.range in
                                  let uu____14032 =
                                    let uu____14035 =
                                      let uu____14036 =
                                        let uu____14050 =
                                          let uu____14053 =
                                            let uu____14054 =
                                              FStar_Syntax_Syntax.mk_binder x in
                                            [uu____14054] in
                                          FStar_Syntax_Subst.close
                                            uu____14053 body2 in
                                        ((false,
                                           [mk_lb
                                              (attrs, (FStar_Util.Inl x),
                                                (x.FStar_Syntax_Syntax.sort),
                                                t11,
                                                (t11.FStar_Syntax_Syntax.pos))]),
                                          uu____14050) in
                                      FStar_Syntax_Syntax.Tm_let uu____14036 in
                                    FStar_All.pipe_left mk uu____14035 in
                                  (uu____14032, aq)) in
                       (match uu____13821 with
                        | (tm, aq1) -> (tm, (FStar_List.append aq0 aq1)))) in
            let uu____14162 = FStar_List.hd lbs in
            (match uu____14162 with
             | (attrs, (head_pat, defn)) ->
                 let uu____14206 = is_rec || (is_app_pattern head_pat) in
                 if uu____14206
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1, t2, t3) ->
            let x =
              let uu____14219 = tun_r t3.FStar_Parser_AST.range in
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                uu____14219 in
            let t_bool =
              let uu____14223 =
                let uu____14224 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None in
                FStar_Syntax_Syntax.Tm_fvar uu____14224 in
              mk uu____14223 in
            let uu____14225 = desugar_term_aq env t1 in
            (match uu____14225 with
             | (t1', aq1) ->
                 let uu____14236 = desugar_term_aq env t2 in
                 (match uu____14236 with
                  | (t2', aq2) ->
                      let uu____14247 = desugar_term_aq env t3 in
                      (match uu____14247 with
                       | (t3', aq3) ->
                           let uu____14258 =
                             let uu____14259 =
                               let uu____14260 =
                                 let uu____14283 =
                                   let uu____14300 =
                                     let uu____14315 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t1.FStar_Parser_AST.range in
                                     (uu____14315,
                                       FStar_Pervasives_Native.None, t2') in
                                   let uu____14329 =
                                     let uu____14346 =
                                       let uu____14361 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t1.FStar_Parser_AST.range in
                                       (uu____14361,
                                         FStar_Pervasives_Native.None, t3') in
                                     [uu____14346] in
                                   uu____14300 :: uu____14329 in
                                 (t1', uu____14283) in
                               FStar_Syntax_Syntax.Tm_match uu____14260 in
                             mk uu____14259 in
                           (uu____14258, (join_aqs [aq1; aq2; aq3])))))
        | FStar_Parser_AST.TryWith (e, branches) ->
            let r = top.FStar_Parser_AST.range in
            let handler = FStar_Parser_AST.mk_function branches r r in
            let body =
              FStar_Parser_AST.mk_function
                [((FStar_Parser_AST.mk_pattern
                     (FStar_Parser_AST.PatConst FStar_Const.Const_unit) r),
                   FStar_Pervasives_Native.None, e)] r r in
            let try_with_lid = FStar_Ident.lid_of_path ["try_with"] r in
            let try_with =
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Var try_with_lid) r
                FStar_Parser_AST.Expr in
            let a1 =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   (try_with, body, FStar_Parser_AST.Nothing)) r
                top.FStar_Parser_AST.level in
            let a2 =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App (a1, handler, FStar_Parser_AST.Nothing))
                r top.FStar_Parser_AST.level in
            desugar_term_aq env a2
        | FStar_Parser_AST.Match (e, branches) ->
            let desugar_branch uu____14557 =
              match uu____14557 with
              | (pat, wopt, b) ->
                  let uu____14579 = desugar_match_pat env pat in
                  (match uu____14579 with
                   | (env1, pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____14610 = desugar_term env1 e1 in
                             FStar_Pervasives_Native.Some uu____14610 in
                       let uu____14615 = desugar_term_aq env1 b in
                       (match uu____14615 with
                        | (b1, aq) ->
                            let uu____14628 =
                              desugar_disjunctive_pattern pat1 wopt1 b1 in
                            (uu____14628, aq))) in
            let uu____14633 = desugar_term_aq env e in
            (match uu____14633 with
             | (e1, aq) ->
                 let uu____14644 =
                   let uu____14675 =
                     let uu____14708 = FStar_List.map desugar_branch branches in
                     FStar_All.pipe_right uu____14708 FStar_List.unzip in
                   FStar_All.pipe_right uu____14675
                     (fun uu____14926 ->
                        match uu____14926 with
                        | (x, y) -> ((FStar_List.flatten x), y)) in
                 (match uu____14644 with
                  | (brs, aqs) ->
                      let uu____15145 =
                        FStar_All.pipe_left mk
                          (FStar_Syntax_Syntax.Tm_match (e1, brs)) in
                      (uu____15145, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e, t, tac_opt) ->
            let uu____15179 =
              let uu____15200 = is_comp_type env t in
              if uu____15200
              then
                let comp = desugar_comp t.FStar_Parser_AST.range true env t in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____15255 = desugar_term_aq env t in
                 match uu____15255 with
                 | (tm, aq) -> ((FStar_Util.Inl tm), aq)) in
            (match uu____15179 with
             | (annot, aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env) in
                 let uu____15347 = desugar_term_aq env e in
                 (match uu____15347 with
                  | (e1, aq) ->
                      let uu____15358 =
                        FStar_All.pipe_left mk
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None)) in
                      (uu____15358, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____15397, []) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt, fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range in
            let user_ns =
              let uu____15440 = FStar_List.hd fields in
              match uu____15440 with
              | (f, uu____15452) -> FStar_Ident.ns_of_lid f in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____15500 ->
                        match uu____15500 with
                        | (g, uu____15507) ->
                            let uu____15508 = FStar_Ident.string_of_id f in
                            let uu____15510 =
                              let uu____15512 = FStar_Ident.ident_of_lid g in
                              FStar_Ident.string_of_id uu____15512 in
                            uu____15508 = uu____15510)) in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f]) in
              match found with
              | FStar_Pervasives_Native.Some (uu____15519, e) -> (fn, e)
              | FStar_Pervasives_Native.None ->
                  (match xopt with
                   | FStar_Pervasives_Native.None ->
                       let uu____15533 =
                         let uu____15539 =
                           let uu____15541 = FStar_Ident.string_of_id f in
                           let uu____15543 =
                             FStar_Ident.string_of_lid
                               record.FStar_Syntax_DsEnv.typename in
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             uu____15541 uu____15543 in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____15539) in
                       FStar_Errors.raise_error uu____15533
                         top.FStar_Parser_AST.range
                   | FStar_Pervasives_Native.Some x ->
                       (fn,
                         (FStar_Parser_AST.mk_term
                            (FStar_Parser_AST.Project (x, fn))
                            x.FStar_Parser_AST.range x.FStar_Parser_AST.level))) in
            let user_constrname =
              FStar_Ident.lid_of_ids
                (FStar_List.append user_ns
                   [record.FStar_Syntax_DsEnv.constrname]) in
            let recterm =
              match eopt with
              | FStar_Pervasives_Native.None ->
                  let uu____15554 =
                    let uu____15565 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____15596 ->
                              match uu____15596 with
                              | (f, uu____15606) ->
                                  let uu____15607 =
                                    let uu____15608 =
                                      get_field FStar_Pervasives_Native.None
                                        f in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____15608 in
                                  (uu____15607, FStar_Parser_AST.Nothing))) in
                    (user_constrname, uu____15565) in
                  FStar_Parser_AST.Construct uu____15554
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range in
                  let xterm =
                    let uu____15626 =
                      let uu____15627 = FStar_Ident.lid_of_ids [x] in
                      FStar_Parser_AST.Var uu____15627 in
                    let uu____15628 = FStar_Ident.range_of_id x in
                    FStar_Parser_AST.mk_term uu____15626 uu____15628
                      FStar_Parser_AST.Expr in
                  let record1 =
                    let uu____15630 =
                      let uu____15643 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____15673 ->
                                match uu____15673 with
                                | (f, uu____15683) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f)) in
                      (FStar_Pervasives_Native.None, uu____15643) in
                    FStar_Parser_AST.Record uu____15630 in
                  let uu____15692 =
                    let uu____15713 =
                      let uu____15728 =
                        let uu____15741 =
                          let uu____15746 =
                            let uu____15747 = FStar_Ident.range_of_id x in
                            FStar_Parser_AST.mk_pattern
                              (FStar_Parser_AST.PatVar
                                 (x, FStar_Pervasives_Native.None))
                              uu____15747 in
                          (uu____15746, e) in
                        (FStar_Pervasives_Native.None, uu____15741) in
                      [uu____15728] in
                    (FStar_Parser_AST.NoLetQualifier, uu____15713,
                      (FStar_Parser_AST.mk_term record1
                         top.FStar_Parser_AST.range
                         top.FStar_Parser_AST.level)) in
                  FStar_Parser_AST.Let uu____15692 in
            let recterm1 =
              FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level in
            let uu____15799 = desugar_term_aq env recterm1 in
            (match uu____15799 with
             | (e, s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____15815;
                         FStar_Syntax_Syntax.vars = uu____15816;_},
                       args)
                      ->
                      let uu____15842 =
                        let uu____15843 =
                          let uu____15844 =
                            let uu____15861 =
                              let uu____15864 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos in
                              let uu____15865 =
                                let uu____15868 =
                                  let uu____15869 =
                                    let uu____15876 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst) in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____15876) in
                                  FStar_Syntax_Syntax.Record_ctor uu____15869 in
                                FStar_Pervasives_Native.Some uu____15868 in
                              FStar_Syntax_Syntax.fvar uu____15864
                                FStar_Syntax_Syntax.delta_constant
                                uu____15865 in
                            (uu____15861, args) in
                          FStar_Syntax_Syntax.Tm_app uu____15844 in
                        FStar_All.pipe_left mk uu____15843 in
                      (uu____15842, s)
                  | uu____15905 -> (e, s)))
        | FStar_Parser_AST.Project (e, f) ->
            let uu____15908 =
              FStar_Syntax_DsEnv.fail_or env
                (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f in
            (match uu____15908 with
             | (constrname, is_rec) ->
                 let uu____15927 = desugar_term_aq env e in
                 (match uu____15927 with
                  | (e1, s) ->
                      let projname =
                        let uu____15939 = FStar_Ident.ident_of_lid f in
                        FStar_Syntax_Util.mk_field_projector_name_from_ident
                          constrname uu____15939 in
                      let qual =
                        if is_rec
                        then
                          let uu____15946 =
                            let uu____15947 =
                              let uu____15952 = FStar_Ident.ident_of_lid f in
                              (constrname, uu____15952) in
                            FStar_Syntax_Syntax.Record_projector uu____15947 in
                          FStar_Pervasives_Native.Some uu____15946
                        else FStar_Pervasives_Native.None in
                      let uu____15955 =
                        let uu____15956 =
                          let uu____15957 =
                            let uu____15974 =
                              let uu____15977 =
                                FStar_Ident.set_lid_range projname
                                  top.FStar_Parser_AST.range in
                              FStar_Syntax_Syntax.fvar uu____15977
                                (FStar_Syntax_Syntax.Delta_equational_at_level
                                   Prims.int_one) qual in
                            let uu____15979 =
                              let uu____15990 = FStar_Syntax_Syntax.as_arg e1 in
                              [uu____15990] in
                            (uu____15974, uu____15979) in
                          FStar_Syntax_Syntax.Tm_app uu____15957 in
                        FStar_All.pipe_left mk uu____15956 in
                      (uu____15955, s)))
        | FStar_Parser_AST.NamedTyp (n, e) ->
            ((let uu____16030 = FStar_Ident.range_of_id n in
              FStar_Errors.log_issue uu____16030
                (FStar_Errors.Warning_IgnoredBinding,
                  "This name is being ignored"));
             desugar_term_aq env e)
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e in
            let uu____16041 =
              let uu____16042 = FStar_Syntax_Subst.compress tm in
              uu____16042.FStar_Syntax_Syntax.n in
            (match uu____16041 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____16050 =
                   let uu___2067_16051 =
                     let uu____16052 =
                       let uu____16054 = FStar_Syntax_Syntax.lid_of_fv fv in
                       FStar_Ident.string_of_lid uu____16054 in
                     FStar_Syntax_Util.exp_string uu____16052 in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___2067_16051.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___2067_16051.FStar_Syntax_Syntax.vars)
                   } in
                 (uu____16050, noaqs)
             | uu____16055 ->
                 let uu____16056 =
                   let uu____16062 =
                     let uu____16064 = FStar_Syntax_Print.term_to_string tm in
                     Prims.op_Hat "VQuote, expected an fvar, got: "
                       uu____16064 in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____16062) in
                 FStar_Errors.raise_error uu____16056
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e, FStar_Parser_AST.Static) ->
            let uu____16073 = desugar_term_aq env e in
            (match uu____16073 with
             | (tm, vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   } in
                 let uu____16085 =
                   FStar_All.pipe_left mk
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi)) in
                 (uu____16085, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun in
            let uu____16090 = FStar_Syntax_Syntax.bv_to_name bv in
            let uu____16091 =
              let uu____16092 =
                let uu____16099 = desugar_term env e in (bv, uu____16099) in
              [uu____16092] in
            (uu____16090, uu____16091)
        | FStar_Parser_AST.Quote (e, FStar_Parser_AST.Dynamic) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              } in
            let uu____16124 =
              let uu____16125 =
                let uu____16126 =
                  let uu____16133 = desugar_term env e in (uu____16133, qi) in
                FStar_Syntax_Syntax.Tm_quoted uu____16126 in
              FStar_All.pipe_left mk uu____16125 in
            (uu____16124, noaqs)
        | FStar_Parser_AST.CalcProof (rel, init_expr, steps) ->
            let is_impl rel1 =
              let is_impl_t t =
                match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.imp_lid
                | uu____16162 -> false in
              let uu____16164 =
                let uu____16165 = unparen rel1 in
                uu____16165.FStar_Parser_AST.tm in
              match uu____16164 with
              | FStar_Parser_AST.Op (id, uu____16168) ->
                  let uu____16173 = op_as_term env (Prims.of_int (2)) id in
                  (match uu____16173 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None -> false)
              | FStar_Parser_AST.Var lid ->
                  let uu____16181 = desugar_name' (fun x -> x) env true lid in
                  (match uu____16181 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None -> false)
              | FStar_Parser_AST.Tvar id ->
                  let uu____16192 = FStar_Syntax_DsEnv.try_lookup_id env id in
                  (match uu____16192 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None -> false)
              | uu____16198 -> false in
            let eta_and_annot rel1 =
              let x = FStar_Ident.gen' "x" rel1.FStar_Parser_AST.range in
              let y = FStar_Ident.gen' "y" rel1.FStar_Parser_AST.range in
              let xt =
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar x)
                  rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr in
              let yt =
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar y)
                  rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr in
              let pats =
                [FStar_Parser_AST.mk_pattern
                   (FStar_Parser_AST.PatVar (x, FStar_Pervasives_Native.None))
                   rel1.FStar_Parser_AST.range;
                FStar_Parser_AST.mk_pattern
                  (FStar_Parser_AST.PatVar (y, FStar_Pervasives_Native.None))
                  rel1.FStar_Parser_AST.range] in
              let uu____16219 =
                let uu____16220 =
                  let uu____16227 =
                    let uu____16228 =
                      let uu____16229 =
                        let uu____16238 =
                          FStar_Parser_AST.mkApp rel1
                            [(xt, FStar_Parser_AST.Nothing);
                            (yt, FStar_Parser_AST.Nothing)]
                            rel1.FStar_Parser_AST.range in
                        let uu____16251 =
                          let uu____16252 =
                            let uu____16253 = FStar_Ident.lid_of_str "Type0" in
                            FStar_Parser_AST.Name uu____16253 in
                          FStar_Parser_AST.mk_term uu____16252
                            rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr in
                        (uu____16238, uu____16251,
                          FStar_Pervasives_Native.None) in
                      FStar_Parser_AST.Ascribed uu____16229 in
                    FStar_Parser_AST.mk_term uu____16228
                      rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr in
                  (pats, uu____16227) in
                FStar_Parser_AST.Abs uu____16220 in
              FStar_Parser_AST.mk_term uu____16219
                rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr in
            let rel1 = eta_and_annot rel in
            let wild r =
              FStar_Parser_AST.mk_term FStar_Parser_AST.Wild r
                FStar_Parser_AST.Expr in
            let init =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Var FStar_Parser_Const.calc_init_lid)
                init_expr.FStar_Parser_AST.range FStar_Parser_AST.Expr in
            let push_impl r =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Var FStar_Parser_Const.calc_push_impl_lid)
                r FStar_Parser_AST.Expr in
            let last_expr =
              let uu____16274 = FStar_List.last steps in
              match uu____16274 with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.CalcStep
                  (uu____16277, uu____16278, last_expr)) -> last_expr
              | FStar_Pervasives_Native.None -> init_expr in
            let step r =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Var FStar_Parser_Const.calc_step_lid) r
                FStar_Parser_AST.Expr in
            let finish =
              FStar_Parser_AST.mkApp
                (FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Var FStar_Parser_Const.calc_finish_lid)
                   top.FStar_Parser_AST.range FStar_Parser_AST.Expr)
                [(rel1, FStar_Parser_AST.Nothing)] top.FStar_Parser_AST.range in
            let e =
              FStar_Parser_AST.mkApp init
                [(init_expr, FStar_Parser_AST.Nothing)]
                init_expr.FStar_Parser_AST.range in
            let uu____16304 =
              FStar_List.fold_left
                (fun uu____16322 ->
                   fun uu____16323 ->
                     match (uu____16322, uu____16323) with
                     | ((e1, prev), FStar_Parser_AST.CalcStep
                        (rel2, just, next_expr)) ->
                         let just1 =
                           let uu____16346 = is_impl rel2 in
                           if uu____16346
                           then
                             let uu____16349 =
                               let uu____16356 =
                                 let uu____16361 =
                                   FStar_Parser_AST.thunk just in
                                 (uu____16361, FStar_Parser_AST.Nothing) in
                               [uu____16356] in
                             FStar_Parser_AST.mkApp
                               (push_impl just.FStar_Parser_AST.range)
                               uu____16349 just.FStar_Parser_AST.range
                           else just in
                         let pf =
                           let uu____16373 =
                             let uu____16380 =
                               let uu____16387 =
                                 let uu____16394 =
                                   let uu____16401 =
                                     let uu____16406 = eta_and_annot rel2 in
                                     (uu____16406, FStar_Parser_AST.Nothing) in
                                   let uu____16407 =
                                     let uu____16414 =
                                       let uu____16421 =
                                         let uu____16426 =
                                           FStar_Parser_AST.thunk e1 in
                                         (uu____16426,
                                           FStar_Parser_AST.Nothing) in
                                       let uu____16427 =
                                         let uu____16434 =
                                           let uu____16439 =
                                             FStar_Parser_AST.thunk just1 in
                                           (uu____16439,
                                             FStar_Parser_AST.Nothing) in
                                         [uu____16434] in
                                       uu____16421 :: uu____16427 in
                                     (next_expr, FStar_Parser_AST.Nothing) ::
                                       uu____16414 in
                                   uu____16401 :: uu____16407 in
                                 (prev, FStar_Parser_AST.Hash) :: uu____16394 in
                               (init_expr, FStar_Parser_AST.Hash) ::
                                 uu____16387 in
                             ((wild rel2.FStar_Parser_AST.range),
                               FStar_Parser_AST.Hash) :: uu____16380 in
                           FStar_Parser_AST.mkApp
                             (step rel2.FStar_Parser_AST.range) uu____16373
                             FStar_Range.dummyRange in
                         (pf, next_expr)) (e, init_expr) steps in
            (match uu____16304 with
             | (e1, uu____16477) ->
                 let e2 =
                   let uu____16479 =
                     let uu____16486 =
                       let uu____16493 =
                         let uu____16500 =
                           let uu____16505 = FStar_Parser_AST.thunk e1 in
                           (uu____16505, FStar_Parser_AST.Nothing) in
                         [uu____16500] in
                       (last_expr, FStar_Parser_AST.Hash) :: uu____16493 in
                     (init_expr, FStar_Parser_AST.Hash) :: uu____16486 in
                   FStar_Parser_AST.mkApp finish uu____16479
                     top.FStar_Parser_AST.range in
                 desugar_term_maybe_top top_level env e2)
        | uu____16522 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____16523 = desugar_formula env top in (uu____16523, noaqs)
        | uu____16524 ->
            let uu____16525 =
              let uu____16531 =
                let uu____16533 = FStar_Parser_AST.term_to_string top in
                Prims.op_Hat "Unexpected term: " uu____16533 in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____16531) in
            FStar_Errors.raise_error uu____16525 top.FStar_Parser_AST.range
and (desugar_args :
  FStar_Syntax_DsEnv.env ->
    (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list)
  =
  fun env ->
    fun args ->
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____16577 ->
              match uu____16577 with
              | (a, imp) ->
                  let uu____16590 = desugar_term env a in
                  arg_withimp_e imp uu____16590))
and (desugar_comp :
  FStar_Range.range ->
    Prims.bool ->
      FStar_Syntax_DsEnv.env ->
        FStar_Parser_AST.term ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun r ->
    fun allow_type_promotion ->
      fun env ->
        fun t ->
          let fail err = FStar_Errors.raise_error err r in
          let is_requires uu____16627 =
            match uu____16627 with
            | (t1, uu____16634) ->
                let uu____16635 =
                  let uu____16636 = unparen t1 in
                  uu____16636.FStar_Parser_AST.tm in
                (match uu____16635 with
                 | FStar_Parser_AST.Requires uu____16638 -> true
                 | uu____16647 -> false) in
          let is_ensures uu____16659 =
            match uu____16659 with
            | (t1, uu____16666) ->
                let uu____16667 =
                  let uu____16668 = unparen t1 in
                  uu____16668.FStar_Parser_AST.tm in
                (match uu____16667 with
                 | FStar_Parser_AST.Ensures uu____16670 -> true
                 | uu____16679 -> false) in
          let is_app head uu____16697 =
            match uu____16697 with
            | (t1, uu____16705) ->
                let uu____16706 =
                  let uu____16707 = unparen t1 in
                  uu____16707.FStar_Parser_AST.tm in
                (match uu____16706 with
                 | FStar_Parser_AST.App
                     ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                        FStar_Parser_AST.range = uu____16710;
                        FStar_Parser_AST.level = uu____16711;_},
                      uu____16712, uu____16713)
                     ->
                     let uu____16714 =
                       let uu____16716 = FStar_Ident.ident_of_lid d in
                       FStar_Ident.string_of_id uu____16716 in
                     uu____16714 = head
                 | uu____16718 -> false) in
          let is_smt_pat uu____16730 =
            match uu____16730 with
            | (t1, uu____16737) ->
                let uu____16738 =
                  let uu____16739 = unparen t1 in
                  uu____16739.FStar_Parser_AST.tm in
                (match uu____16738 with
                 | FStar_Parser_AST.Construct
                     (cons,
                      ({
                         FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                           (smtpat, uu____16743);
                         FStar_Parser_AST.range = uu____16744;
                         FStar_Parser_AST.level = uu____16745;_},
                       uu____16746)::uu____16747::[])
                     ->
                     (FStar_Ident.lid_equals cons FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s ->
                             let uu____16787 =
                               FStar_Ident.string_of_lid smtpat in
                             uu____16787 = s)
                          ["SMTPat"; "SMTPatT"; "SMTPatOr"])
                 | FStar_Parser_AST.Construct
                     (cons,
                      ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var smtpat;
                         FStar_Parser_AST.range = uu____16799;
                         FStar_Parser_AST.level = uu____16800;_},
                       uu____16801)::uu____16802::[])
                     ->
                     (FStar_Ident.lid_equals cons FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s ->
                             let uu____16830 =
                               FStar_Ident.string_of_lid smtpat in
                             uu____16830 = s) ["smt_pat"; "smt_pat_or"])
                 | uu____16838 -> false) in
          let is_decreases = is_app "decreases" in
          let pre_process_comp_typ t1 =
            let uu____16873 = head_and_args t1 in
            match uu____16873 with
            | (head, args) ->
                (match head.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Name lemma when
                     let uu____16931 =
                       let uu____16933 = FStar_Ident.ident_of_lid lemma in
                       FStar_Ident.string_of_id uu____16933 in
                     uu____16931 = "Lemma" ->
                     let unit_tm =
                       ((FStar_Parser_AST.mk_term
                           (FStar_Parser_AST.Name FStar_Parser_Const.unit_lid)
                           t1.FStar_Parser_AST.range
                           FStar_Parser_AST.Type_level),
                         FStar_Parser_AST.Nothing) in
                     let nil_pat =
                       ((FStar_Parser_AST.mk_term
                           (FStar_Parser_AST.Name FStar_Parser_Const.nil_lid)
                           t1.FStar_Parser_AST.range FStar_Parser_AST.Expr),
                         FStar_Parser_AST.Nothing) in
                     let req_true =
                       let req =
                         FStar_Parser_AST.Requires
                           ((FStar_Parser_AST.mk_term
                               (FStar_Parser_AST.Name
                                  FStar_Parser_Const.true_lid)
                               t1.FStar_Parser_AST.range
                               FStar_Parser_AST.Formula),
                             FStar_Pervasives_Native.None) in
                       ((FStar_Parser_AST.mk_term req
                           t1.FStar_Parser_AST.range
                           FStar_Parser_AST.Type_level),
                         FStar_Parser_AST.Nothing) in
                     let thunk_ens uu____16969 =
                       match uu____16969 with
                       | (e, i) ->
                           let uu____16980 = FStar_Parser_AST.thunk e in
                           (uu____16980, i) in
                     let fail_lemma uu____16992 =
                       let expected_one_of =
                         ["Lemma post";
                         "Lemma (ensures post)";
                         "Lemma (requires pre) (ensures post)";
                         "Lemma post [SMTPat ...]";
                         "Lemma (ensures post) [SMTPat ...]";
                         "Lemma (ensures post) (decreases d)";
                         "Lemma (ensures post) (decreases d) [SMTPat ...]";
                         "Lemma (requires pre) (ensures post) (decreases d)";
                         "Lemma (requires pre) (ensures post) [SMTPat ...]";
                         "Lemma (requires pre) (ensures post) (decreases d) [SMTPat ...]"] in
                       let msg = FStar_String.concat "\n\t" expected_one_of in
                       FStar_Errors.raise_error
                         (FStar_Errors.Fatal_InvalidLemmaArgument,
                           (Prims.op_Hat
                              "Invalid arguments to 'Lemma'; expected one of the following:\n\t"
                              msg)) t1.FStar_Parser_AST.range in
                     let args1 =
                       match args with
                       | [] -> fail_lemma ()
                       | req::[] when is_requires req -> fail_lemma ()
                       | smtpat::[] when is_smt_pat smtpat -> fail_lemma ()
                       | dec::[] when is_decreases dec -> fail_lemma ()
                       | ens::[] ->
                           let uu____17098 =
                             let uu____17105 =
                               let uu____17112 = thunk_ens ens in
                               [uu____17112; nil_pat] in
                             req_true :: uu____17105 in
                           unit_tm :: uu____17098
                       | req::ens::[] when
                           (is_requires req) && (is_ensures ens) ->
                           let uu____17159 =
                             let uu____17166 =
                               let uu____17173 = thunk_ens ens in
                               [uu____17173; nil_pat] in
                             req :: uu____17166 in
                           unit_tm :: uu____17159
                       | ens::smtpat::[] when
                           (((let uu____17222 = is_requires ens in
                              Prims.op_Negation uu____17222) &&
                               (let uu____17225 = is_smt_pat ens in
                                Prims.op_Negation uu____17225))
                              &&
                              (let uu____17228 = is_decreases ens in
                               Prims.op_Negation uu____17228))
                             && (is_smt_pat smtpat)
                           ->
                           let uu____17230 =
                             let uu____17237 =
                               let uu____17244 = thunk_ens ens in
                               [uu____17244; smtpat] in
                             req_true :: uu____17237 in
                           unit_tm :: uu____17230
                       | ens::dec::[] when
                           (is_ensures ens) && (is_decreases dec) ->
                           let uu____17291 =
                             let uu____17298 =
                               let uu____17305 = thunk_ens ens in
                               [uu____17305; nil_pat; dec] in
                             req_true :: uu____17298 in
                           unit_tm :: uu____17291
                       | ens::dec::smtpat::[] when
                           ((is_ensures ens) && (is_decreases dec)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____17365 =
                             let uu____17372 =
                               let uu____17379 = thunk_ens ens in
                               [uu____17379; smtpat; dec] in
                             req_true :: uu____17372 in
                           unit_tm :: uu____17365
                       | req::ens::dec::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_decreases dec)
                           ->
                           let uu____17439 =
                             let uu____17446 =
                               let uu____17453 = thunk_ens ens in
                               [uu____17453; nil_pat; dec] in
                             req :: uu____17446 in
                           unit_tm :: uu____17439
                       | req::ens::smtpat::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____17513 =
                             let uu____17520 =
                               let uu____17527 = thunk_ens ens in
                               [uu____17527; smtpat] in
                             req :: uu____17520 in
                           unit_tm :: uu____17513
                       | req::ens::dec::smtpat::[] when
                           (((is_requires req) && (is_ensures ens)) &&
                              (is_smt_pat smtpat))
                             && (is_decreases dec)
                           ->
                           let uu____17592 =
                             let uu____17599 =
                               let uu____17606 = thunk_ens ens in
                               [uu____17606; dec; smtpat] in
                             req :: uu____17599 in
                           unit_tm :: uu____17592
                       | _other -> fail_lemma () in
                     let head_and_attributes =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) lemma in
                     (head_and_attributes, args1)
                 | FStar_Parser_AST.Name l when
                     FStar_Syntax_DsEnv.is_effect_name env l ->
                     let uu____17668 =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) l in
                     (uu____17668, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____17696 = FStar_Syntax_DsEnv.current_module env in
                      FStar_Ident.lid_equals uu____17696
                        FStar_Parser_Const.prims_lid)
                       &&
                       (let uu____17698 =
                          let uu____17700 = FStar_Ident.ident_of_lid l in
                          FStar_Ident.string_of_id uu____17700 in
                        uu____17698 = "Tot")
                     ->
                     let uu____17703 =
                       let uu____17710 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head.FStar_Parser_AST.range in
                       (uu____17710, []) in
                     (uu____17703, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____17728 = FStar_Syntax_DsEnv.current_module env in
                      FStar_Ident.lid_equals uu____17728
                        FStar_Parser_Const.prims_lid)
                       &&
                       (let uu____17730 =
                          let uu____17732 = FStar_Ident.ident_of_lid l in
                          FStar_Ident.string_of_id uu____17732 in
                        uu____17730 = "GTot")
                     ->
                     let uu____17735 =
                       let uu____17742 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_GTot_lid
                           head.FStar_Parser_AST.range in
                       (uu____17742, []) in
                     (uu____17735, args)
                 | FStar_Parser_AST.Name l when
                     ((let uu____17760 =
                         let uu____17762 = FStar_Ident.ident_of_lid l in
                         FStar_Ident.string_of_id uu____17762 in
                       uu____17760 = "Type") ||
                        (let uu____17766 =
                           let uu____17768 = FStar_Ident.ident_of_lid l in
                           FStar_Ident.string_of_id uu____17768 in
                         uu____17766 = "Type0"))
                       ||
                       (let uu____17772 =
                          let uu____17774 = FStar_Ident.ident_of_lid l in
                          FStar_Ident.string_of_id uu____17774 in
                        uu____17772 = "Effect")
                     ->
                     let uu____17777 =
                       let uu____17784 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head.FStar_Parser_AST.range in
                       (uu____17784, []) in
                     (uu____17777, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17807 when allow_type_promotion ->
                     let default_effect =
                       let uu____17809 = FStar_Options.ml_ish () in
                       if uu____17809
                       then FStar_Parser_Const.effect_ML_lid
                       else
                         ((let uu____17815 =
                             FStar_Options.warn_default_effects () in
                           if uu____17815
                           then
                             FStar_Errors.log_issue
                               head.FStar_Parser_AST.range
                               (FStar_Errors.Warning_UseDefaultEffect,
                                 "Using default effect Tot")
                           else ());
                          FStar_Parser_Const.effect_Tot_lid) in
                     let uu____17822 =
                       let uu____17829 =
                         FStar_Ident.set_lid_range default_effect
                           head.FStar_Parser_AST.range in
                       (uu____17829, []) in
                     (uu____17822, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17852 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_EffectNotFound,
                         "Expected an effect constructor")
                       t1.FStar_Parser_AST.range) in
          let uu____17871 = pre_process_comp_typ t in
          match uu____17871 with
          | ((eff, cattributes), args) ->
              (if (FStar_List.length args) = Prims.int_zero
               then
                 (let uu____17923 =
                    let uu____17929 =
                      let uu____17931 = FStar_Syntax_Print.lid_to_string eff in
                      FStar_Util.format1 "Not enough args to effect %s"
                        uu____17931 in
                    (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____17929) in
                  fail uu____17923)
               else ();
               (let is_universe uu____17947 =
                  match uu____17947 with
                  | (uu____17953, imp) -> imp = FStar_Parser_AST.UnivApp in
                let uu____17955 = FStar_Util.take is_universe args in
                match uu____17955 with
                | (universes, args1) ->
                    let universes1 =
                      FStar_List.map
                        (fun uu____18014 ->
                           match uu____18014 with
                           | (u, imp) -> desugar_universe u) universes in
                    let uu____18021 =
                      let uu____18036 = FStar_List.hd args1 in
                      let uu____18045 = FStar_List.tl args1 in
                      (uu____18036, uu____18045) in
                    (match uu____18021 with
                     | (result_arg, rest) ->
                         let result_typ =
                           desugar_typ env
                             (FStar_Pervasives_Native.fst result_arg) in
                         let rest1 = desugar_args env rest in
                         let uu____18100 =
                           let is_decrease uu____18139 =
                             match uu____18139 with
                             | (t1, uu____18150) ->
                                 (match t1.FStar_Syntax_Syntax.n with
                                  | FStar_Syntax_Syntax.Tm_app
                                      ({
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_fvar fv;
                                         FStar_Syntax_Syntax.pos =
                                           uu____18161;
                                         FStar_Syntax_Syntax.vars =
                                           uu____18162;_},
                                       uu____18163::[])
                                      ->
                                      FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Parser_Const.decreases_lid
                                  | uu____18202 -> false) in
                           FStar_All.pipe_right rest1
                             (FStar_List.partition is_decrease) in
                         (match uu____18100 with
                          | (dec, rest2) ->
                              let decreases_clause =
                                FStar_All.pipe_right dec
                                  (FStar_List.map
                                     (fun uu____18319 ->
                                        match uu____18319 with
                                        | (t1, uu____18329) ->
                                            (match t1.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____18338,
                                                  (arg, uu____18340)::[])
                                                 ->
                                                 FStar_Syntax_Syntax.DECREASES
                                                   arg
                                             | uu____18379 ->
                                                 failwith "impos"))) in
                              let no_additional_args =
                                let is_empty l =
                                  match l with
                                  | [] -> true
                                  | uu____18400 -> false in
                                (((is_empty decreases_clause) &&
                                    (is_empty rest2))
                                   && (is_empty cattributes))
                                  && (is_empty universes1) in
                              let uu____18412 =
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_Tot_lid) in
                              if uu____18412
                              then FStar_Syntax_Syntax.mk_Total result_typ
                              else
                                (let uu____18419 =
                                   no_additional_args &&
                                     (FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_GTot_lid) in
                                 if uu____18419
                                 then
                                   FStar_Syntax_Syntax.mk_GTotal result_typ
                                 else
                                   (let flags =
                                      let uu____18429 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid in
                                      if uu____18429
                                      then [FStar_Syntax_Syntax.LEMMA]
                                      else
                                        (let uu____18436 =
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_Tot_lid in
                                         if uu____18436
                                         then [FStar_Syntax_Syntax.TOTAL]
                                         else
                                           (let uu____18443 =
                                              FStar_Ident.lid_equals eff
                                                FStar_Parser_Const.effect_ML_lid in
                                            if uu____18443
                                            then
                                              [FStar_Syntax_Syntax.MLEFFECT]
                                            else
                                              (let uu____18450 =
                                                 FStar_Ident.lid_equals eff
                                                   FStar_Parser_Const.effect_GTot_lid in
                                               if uu____18450
                                               then
                                                 [FStar_Syntax_Syntax.SOMETRIVIAL]
                                               else []))) in
                                    let flags1 =
                                      FStar_List.append flags cattributes in
                                    let rest3 =
                                      let uu____18471 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid in
                                      if uu____18471
                                      then
                                        match rest2 with
                                        | req::ens::(pat, aq)::[] ->
                                            let pat1 =
                                              match pat.FStar_Syntax_Syntax.n
                                              with
                                              | FStar_Syntax_Syntax.Tm_fvar
                                                  fv when
                                                  FStar_Syntax_Syntax.fv_eq_lid
                                                    fv
                                                    FStar_Parser_Const.nil_lid
                                                  ->
                                                  let nil =
                                                    FStar_Syntax_Syntax.mk_Tm_uinst
                                                      pat
                                                      [FStar_Syntax_Syntax.U_zero] in
                                                  let pattern =
                                                    let uu____18562 =
                                                      FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos in
                                                    FStar_Syntax_Syntax.fvar
                                                      uu____18562
                                                      FStar_Syntax_Syntax.delta_constant
                                                      FStar_Pervasives_Native.None in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    nil
                                                    [(pattern,
                                                       (FStar_Pervasives_Native.Some
                                                          FStar_Syntax_Syntax.imp_tag))]
                                                    pat.FStar_Syntax_Syntax.pos
                                              | uu____18583 -> pat in
                                            let uu____18584 =
                                              let uu____18595 =
                                                let uu____18606 =
                                                  let uu____18615 =
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (pat1,
                                                           (FStar_Syntax_Syntax.Meta_desugared
                                                              FStar_Syntax_Syntax.Meta_smt_pat)))
                                                      pat1.FStar_Syntax_Syntax.pos in
                                                  (uu____18615, aq) in
                                                [uu____18606] in
                                              ens :: uu____18595 in
                                            req :: uu____18584
                                        | uu____18656 -> rest2
                                      else rest2 in
                                    FStar_Syntax_Syntax.mk_Comp
                                      {
                                        FStar_Syntax_Syntax.comp_univs =
                                          universes1;
                                        FStar_Syntax_Syntax.effect_name = eff;
                                        FStar_Syntax_Syntax.result_typ =
                                          result_typ;
                                        FStar_Syntax_Syntax.effect_args =
                                          rest3;
                                        FStar_Syntax_Syntax.flags =
                                          (FStar_List.append flags1
                                             decreases_clause)
                                      }))))))
and (desugar_formula :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun f ->
      let mk t = FStar_Syntax_Syntax.mk t f.FStar_Parser_AST.range in
      let setpos t =
        let uu___2392_18691 = t in
        {
          FStar_Syntax_Syntax.n = (uu___2392_18691.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___2392_18691.FStar_Syntax_Syntax.vars)
        } in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___2399_18745 = b in
             {
               FStar_Parser_AST.b = (uu___2399_18745.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___2399_18745.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___2399_18745.FStar_Parser_AST.aqual)
             }) in
        let with_pats env1 uu____18774 body1 =
          match uu____18774 with
          | (names, pats1) ->
              (match (names, pats1) with
               | ([], []) -> body1
               | ([], uu____18820::uu____18821) ->
                   failwith
                     "Impossible: Annotated pattern without binders in scope"
               | uu____18839 ->
                   let names1 =
                     FStar_All.pipe_right names
                       (FStar_List.map
                          (fun i ->
                             let uu___2418_18867 =
                               FStar_Syntax_DsEnv.fail_or2
                                 (FStar_Syntax_DsEnv.try_lookup_id env1) i in
                             let uu____18868 = FStar_Ident.range_of_id i in
                             {
                               FStar_Syntax_Syntax.n =
                                 (uu___2418_18867.FStar_Syntax_Syntax.n);
                               FStar_Syntax_Syntax.pos = uu____18868;
                               FStar_Syntax_Syntax.vars =
                                 (uu___2418_18867.FStar_Syntax_Syntax.vars)
                             })) in
                   let pats2 =
                     FStar_All.pipe_right pats1
                       (FStar_List.map
                          (fun es ->
                             FStar_All.pipe_right es
                               (FStar_List.map
                                  (fun e ->
                                     let uu____18931 = desugar_term env1 e in
                                     FStar_All.pipe_left
                                       (arg_withimp_t
                                          FStar_Parser_AST.Nothing)
                                       uu____18931)))) in
                   mk
                     (FStar_Syntax_Syntax.Tm_meta
                        (body1,
                          (FStar_Syntax_Syntax.Meta_pattern (names1, pats2))))) in
        match tk with
        | (FStar_Pervasives_Native.Some a, k) ->
            let uu____18962 = FStar_Syntax_DsEnv.push_bv env a in
            (match uu____18962 with
             | (env1, a1) ->
                 let a2 =
                   let uu___2431_18972 = a1 in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___2431_18972.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___2431_18972.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   } in
                 let body1 = desugar_formula env1 body in
                 let body2 = with_pats env1 pats body1 in
                 let body3 =
                   let uu____18978 =
                     let uu____18981 =
                       let uu____18982 = FStar_Syntax_Syntax.mk_binder a2 in
                       [uu____18982] in
                     no_annot_abs uu____18981 body2 in
                   FStar_All.pipe_left setpos uu____18978 in
                 let uu____19003 =
                   let uu____19004 =
                     let uu____19021 =
                       let uu____19024 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange in
                       FStar_Syntax_Syntax.fvar uu____19024
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            Prims.int_one) FStar_Pervasives_Native.None in
                     let uu____19026 =
                       let uu____19037 = FStar_Syntax_Syntax.as_arg body3 in
                       [uu____19037] in
                     (uu____19021, uu____19026) in
                   FStar_Syntax_Syntax.Tm_app uu____19004 in
                 FStar_All.pipe_left mk uu____19003)
        | uu____19076 -> failwith "impossible" in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest in
            let body1 =
              let uu____19141 = q (rest, pats, body) in
              let uu____19144 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range in
              FStar_Parser_AST.mk_term uu____19141 uu____19144
                FStar_Parser_AST.Formula in
            let uu____19145 = q ([b], ([], []), body1) in
            FStar_Parser_AST.mk_term uu____19145 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____19156 -> failwith "impossible" in
      let uu____19160 =
        let uu____19161 = unparen f in uu____19161.FStar_Parser_AST.tm in
      match uu____19160 with
      | FStar_Parser_AST.Labeled (f1, l, p) ->
          let f2 = desugar_formula env f1 in
          FStar_All.pipe_left mk
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([], uu____19174, uu____19175) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([], uu____19199, uu____19200) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3, pats, body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____19256 =
            push_quant (fun x -> FStar_Parser_AST.QForall x) binders pats
              body in
          desugar_formula env uu____19256
      | FStar_Parser_AST.QExists (_1::_2::_3, pats, body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____19300 =
            push_quant (fun x -> FStar_Parser_AST.QExists x) binders pats
              body in
          desugar_formula env uu____19300
      | FStar_Parser_AST.QForall (b::[], pats, body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[], pats, body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____19364 -> desugar_term env f
and (desugar_binder :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Ident.ident FStar_Pervasives_Native.option *
        FStar_Syntax_Syntax.term))
  =
  fun env ->
    fun b ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.TAnnotated (x, t) ->
          let uu____19375 = desugar_typ env t in
          ((FStar_Pervasives_Native.Some x), uu____19375)
      | FStar_Parser_AST.Annotated (x, t) ->
          let uu____19380 = desugar_typ env t in
          ((FStar_Pervasives_Native.Some x), uu____19380)
      | FStar_Parser_AST.TVariable x ->
          let uu____19384 =
            let uu____19385 = FStar_Ident.range_of_id x in
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              uu____19385 in
          ((FStar_Pervasives_Native.Some x), uu____19384)
      | FStar_Parser_AST.NoName t ->
          let uu____19389 = desugar_typ env t in
          (FStar_Pervasives_Native.None, uu____19389)
      | FStar_Parser_AST.Variable x ->
          let uu____19393 =
            let uu____19394 = FStar_Ident.range_of_id x in tun_r uu____19394 in
          ((FStar_Pervasives_Native.Some x), uu____19393)
and (as_binder :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      (FStar_Ident.ident FStar_Pervasives_Native.option *
        FStar_Syntax_Syntax.term) ->
        ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option) * FStar_Syntax_DsEnv.env))
  =
  fun env ->
    fun imp ->
      fun uu___11_19399 ->
        match uu___11_19399 with
        | (FStar_Pervasives_Native.None, k) ->
            let uu____19421 = FStar_Syntax_Syntax.null_binder k in
            (uu____19421, env)
        | (FStar_Pervasives_Native.Some a, k) ->
            let uu____19438 = FStar_Syntax_DsEnv.push_bv env a in
            (match uu____19438 with
             | (env1, a1) ->
                 let uu____19455 =
                   let uu____19462 = trans_aqual env1 imp in
                   ((let uu___2531_19468 = a1 in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___2531_19468.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___2531_19468.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____19462) in
                 (uu____19455, env1))
and (trans_aqual :
  env_t ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env ->
    fun uu___12_19476 ->
      match uu___12_19476 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta
          (FStar_Parser_AST.Arg_qualifier_meta_tac t)) ->
          let uu____19480 =
            let uu____19481 =
              let uu____19482 = desugar_term env t in
              FStar_Syntax_Syntax.Arg_qualifier_meta_tac uu____19482 in
            FStar_Syntax_Syntax.Meta uu____19481 in
          FStar_Pervasives_Native.Some uu____19480
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta
          (FStar_Parser_AST.Arg_qualifier_meta_attr t)) ->
          let t1 = desugar_term env t in
          (FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos
             (FStar_Errors.Warning_BleedingEdge_Feature,
               "Associating attributes with a binder is an experimental feature---expect its behavior to change");
           FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Meta
                (FStar_Syntax_Syntax.Arg_qualifier_meta_attr t1)))
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.aqual) Prims.list))
  =
  fun env ->
    fun bs ->
      let uu____19515 =
        FStar_List.fold_left
          (fun uu____19548 ->
             fun b ->
               match uu____19548 with
               | (env1, out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___2556_19592 = b in
                        {
                          FStar_Parser_AST.b =
                            (uu___2556_19592.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___2556_19592.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___2556_19592.FStar_Parser_AST.aqual)
                        }) in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a, k) ->
                        let uu____19607 = FStar_Syntax_DsEnv.push_bv env1 a in
                        (match uu____19607 with
                         | (env2, a1) ->
                             let a2 =
                               let uu___2566_19625 = a1 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2566_19625.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2566_19625.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               } in
                             let uu____19626 =
                               let uu____19633 =
                                 let uu____19638 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual in
                                 (a2, uu____19638) in
                               uu____19633 :: out in
                             (env2, uu____19626))
                    | uu____19649 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs in
      match uu____19515 with
      | (env1, tpars) -> (env1, (FStar_List.rev tpars))
let (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun env ->
    fun cattributes ->
      let desugar_attribute t =
        let uu____19737 =
          let uu____19738 = unparen t in uu____19738.FStar_Parser_AST.tm in
        match uu____19737 with
        | FStar_Parser_AST.Var lid when
            let uu____19740 = FStar_Ident.string_of_lid lid in
            uu____19740 = "cps" -> FStar_Syntax_Syntax.CPS
        | uu____19744 ->
            let uu____19745 =
              let uu____19751 =
                let uu____19753 = FStar_Parser_AST.term_to_string t in
                Prims.op_Hat "Unknown attribute " uu____19753 in
              (FStar_Errors.Fatal_UnknownAttribute, uu____19751) in
            FStar_Errors.raise_error uu____19745 t.FStar_Parser_AST.range in
      FStar_List.map desugar_attribute cattributes
let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x, uu____19770) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x, uu____19772) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu____19775 -> FStar_Pervasives_Native.None
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs ->
    FStar_List.collect
      (fun b ->
         let uu____19793 = binder_ident b in
         FStar_Common.list_of_option uu____19793) bs
let (mk_data_discriminators :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_DsEnv.env ->
      FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun quals ->
    fun env ->
      fun datas ->
        let quals1 =
          FStar_All.pipe_right quals
            (FStar_List.filter
               (fun uu___13_19830 ->
                  match uu___13_19830 with
                  | FStar_Syntax_Syntax.NoExtract -> true
                  | FStar_Syntax_Syntax.Abstract -> true
                  | FStar_Syntax_Syntax.Private -> true
                  | uu____19835 -> false)) in
        let quals2 q =
          let uu____19849 =
            (let uu____19853 = FStar_Syntax_DsEnv.iface env in
             Prims.op_Negation uu____19853) ||
              (FStar_Syntax_DsEnv.admitted_iface env) in
          if uu____19849
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1 in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d in
                let uu____19870 = FStar_Ident.range_of_lid disc_name in
                let uu____19871 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d] in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____19870;
                  FStar_Syntax_Syntax.sigquals = uu____19871;
                  FStar_Syntax_Syntax.sigmeta =
                    FStar_Syntax_Syntax.default_sigmeta;
                  FStar_Syntax_Syntax.sigattrs = [];
                  FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
                }))
let (mk_indexed_projector_names :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.fv_qual ->
      FStar_Syntax_DsEnv.env ->
        FStar_Ident.lident ->
          FStar_Syntax_Syntax.binder Prims.list ->
            FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun iquals ->
    fun fvq ->
      fun env ->
        fun lid ->
          fun fields ->
            let p = FStar_Ident.range_of_lid lid in
            let uu____19911 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i ->
                      fun uu____19947 ->
                        match uu____19947 with
                        | (x, uu____19958) ->
                            let field_name =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i in
                            let only_decl =
                              ((let uu____19968 =
                                  FStar_Syntax_DsEnv.current_module env in
                                FStar_Ident.lid_equals
                                  FStar_Parser_Const.prims_lid uu____19968)
                                 || (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                ||
                                (let uu____19970 =
                                   let uu____19972 =
                                     FStar_Syntax_DsEnv.current_module env in
                                   FStar_Ident.string_of_lid uu____19972 in
                                 FStar_Options.dont_gen_projectors
                                   uu____19970) in
                            let no_decl =
                              FStar_Syntax_Syntax.is_type
                                x.FStar_Syntax_Syntax.sort in
                            let quals q =
                              if only_decl
                              then
                                let uu____19990 =
                                  FStar_List.filter
                                    (fun uu___14_19994 ->
                                       match uu___14_19994 with
                                       | FStar_Syntax_Syntax.Abstract ->
                                           false
                                       | uu____19997 -> true) q in
                                FStar_Syntax_Syntax.Assumption :: uu____19990
                              else q in
                            let quals1 =
                              let iquals1 =
                                FStar_All.pipe_right iquals
                                  (FStar_List.filter
                                     (fun uu___15_20012 ->
                                        match uu___15_20012 with
                                        | FStar_Syntax_Syntax.NoExtract ->
                                            true
                                        | FStar_Syntax_Syntax.Abstract ->
                                            true
                                        | FStar_Syntax_Syntax.Private -> true
                                        | uu____20017 -> false)) in
                              quals (FStar_Syntax_Syntax.OnlyName ::
                                (FStar_Syntax_Syntax.Projector
                                   (lid, (x.FStar_Syntax_Syntax.ppname))) ::
                                iquals1) in
                            let decl =
                              let uu____20020 =
                                FStar_Ident.range_of_lid field_name in
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_declare_typ
                                     (field_name, [],
                                       FStar_Syntax_Syntax.tun));
                                FStar_Syntax_Syntax.sigrng = uu____20020;
                                FStar_Syntax_Syntax.sigquals = quals1;
                                FStar_Syntax_Syntax.sigmeta =
                                  FStar_Syntax_Syntax.default_sigmeta;
                                FStar_Syntax_Syntax.sigattrs = [];
                                FStar_Syntax_Syntax.sigopts =
                                  FStar_Pervasives_Native.None
                              } in
                            if only_decl
                            then [decl]
                            else
                              (let dd =
                                 let uu____20027 =
                                   FStar_All.pipe_right quals1
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Abstract) in
                                 if uu____20027
                                 then
                                   FStar_Syntax_Syntax.Delta_abstract
                                     (FStar_Syntax_Syntax.Delta_equational_at_level
                                        Prims.int_one)
                                 else
                                   FStar_Syntax_Syntax.Delta_equational_at_level
                                     Prims.int_one in
                               let lb =
                                 let uu____20038 =
                                   let uu____20043 =
                                     FStar_Syntax_Syntax.lid_as_fv field_name
                                       dd FStar_Pervasives_Native.None in
                                   FStar_Util.Inr uu____20043 in
                                 {
                                   FStar_Syntax_Syntax.lbname = uu____20038;
                                   FStar_Syntax_Syntax.lbunivs = [];
                                   FStar_Syntax_Syntax.lbtyp =
                                     FStar_Syntax_Syntax.tun;
                                   FStar_Syntax_Syntax.lbeff =
                                     FStar_Parser_Const.effect_Tot_lid;
                                   FStar_Syntax_Syntax.lbdef =
                                     FStar_Syntax_Syntax.tun;
                                   FStar_Syntax_Syntax.lbattrs = [];
                                   FStar_Syntax_Syntax.lbpos =
                                     FStar_Range.dummyRange
                                 } in
                               let impl =
                                 let uu____20047 =
                                   let uu____20048 =
                                     let uu____20055 =
                                       let uu____20058 =
                                         let uu____20059 =
                                           FStar_All.pipe_right
                                             lb.FStar_Syntax_Syntax.lbname
                                             FStar_Util.right in
                                         FStar_All.pipe_right uu____20059
                                           (fun fv ->
                                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                       [uu____20058] in
                                     ((false, [lb]), uu____20055) in
                                   FStar_Syntax_Syntax.Sig_let uu____20048 in
                                 {
                                   FStar_Syntax_Syntax.sigel = uu____20047;
                                   FStar_Syntax_Syntax.sigrng = p;
                                   FStar_Syntax_Syntax.sigquals = quals1;
                                   FStar_Syntax_Syntax.sigmeta =
                                     FStar_Syntax_Syntax.default_sigmeta;
                                   FStar_Syntax_Syntax.sigattrs = [];
                                   FStar_Syntax_Syntax.sigopts =
                                     FStar_Pervasives_Native.None
                                 } in
                               if no_decl then [impl] else [decl; impl]))) in
            FStar_All.pipe_right uu____19911 FStar_List.flatten
let (mk_data_projector_names :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_DsEnv.env ->
      FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun iquals ->
    fun env ->
      fun se ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_datacon
            (lid, uu____20108, t, uu____20110, n, uu____20112) when
            let uu____20119 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid in
            Prims.op_Negation uu____20119 ->
            let uu____20121 = FStar_Syntax_Util.arrow_formals t in
            (match uu____20121 with
             | (formals, uu____20131) ->
                 (match formals with
                  | [] -> []
                  | uu____20144 ->
                      let filter_records uu___16_20152 =
                        match uu___16_20152 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____20155, fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____20167 -> FStar_Pervasives_Native.None in
                      let fv_qual =
                        let uu____20169 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records in
                        match uu____20169 with
                        | FStar_Pervasives_Native.None ->
                            FStar_Syntax_Syntax.Data_ctor
                        | FStar_Pervasives_Native.Some q -> q in
                      let iquals1 =
                        if
                          (FStar_List.contains FStar_Syntax_Syntax.Abstract
                             iquals)
                            &&
                            (Prims.op_Negation
                               (FStar_List.contains
                                  FStar_Syntax_Syntax.Private iquals))
                        then FStar_Syntax_Syntax.Private :: iquals
                        else iquals in
                      let uu____20181 = FStar_Util.first_N n formals in
                      (match uu____20181 with
                       | (uu____20210, rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____20244 -> []
let (mk_typ_abbrev :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.decl ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.univ_name Prims.list ->
          (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
            FStar_Pervasives_Native.option) Prims.list ->
            FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
              FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
                FStar_Ident.lident Prims.list ->
                  FStar_Syntax_Syntax.qualifier Prims.list ->
                    FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun env ->
    fun d ->
      fun lid ->
        fun uvs ->
          fun typars ->
            fun kopt ->
              fun t ->
                fun lids ->
                  fun quals ->
                    fun rng ->
                      let attrs =
                        FStar_List.map (desugar_term env)
                          d.FStar_Parser_AST.attrs in
                      let val_attrs =
                        let uu____20338 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env lid in
                        FStar_All.pipe_right uu____20338
                          FStar_Pervasives_Native.snd in
                      let dd =
                        let uu____20362 =
                          FStar_All.pipe_right quals
                            (FStar_List.contains FStar_Syntax_Syntax.Abstract) in
                        if uu____20362
                        then
                          let uu____20368 =
                            FStar_Syntax_Util.incr_delta_qualifier t in
                          FStar_Syntax_Syntax.Delta_abstract uu____20368
                        else FStar_Syntax_Util.incr_delta_qualifier t in
                      let lb =
                        let uu____20372 =
                          let uu____20377 =
                            FStar_Syntax_Syntax.lid_as_fv lid dd
                              FStar_Pervasives_Native.None in
                          FStar_Util.Inr uu____20377 in
                        let uu____20378 =
                          if FStar_Util.is_some kopt
                          then
                            let uu____20384 =
                              let uu____20387 =
                                FStar_All.pipe_right kopt FStar_Util.must in
                              FStar_Syntax_Syntax.mk_Total uu____20387 in
                            FStar_Syntax_Util.arrow typars uu____20384
                          else FStar_Syntax_Syntax.tun in
                        let uu____20392 = no_annot_abs typars t in
                        {
                          FStar_Syntax_Syntax.lbname = uu____20372;
                          FStar_Syntax_Syntax.lbunivs = uvs;
                          FStar_Syntax_Syntax.lbtyp = uu____20378;
                          FStar_Syntax_Syntax.lbeff =
                            FStar_Parser_Const.effect_Tot_lid;
                          FStar_Syntax_Syntax.lbdef = uu____20392;
                          FStar_Syntax_Syntax.lbattrs = [];
                          FStar_Syntax_Syntax.lbpos = rng
                        } in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (FStar_Syntax_Syntax.Sig_let ((false, [lb]), lids));
                        FStar_Syntax_Syntax.sigrng = rng;
                        FStar_Syntax_Syntax.sigquals = quals;
                        FStar_Syntax_Syntax.sigmeta =
                          FStar_Syntax_Syntax.default_sigmeta;
                        FStar_Syntax_Syntax.sigattrs =
                          (FStar_List.append val_attrs attrs);
                        FStar_Syntax_Syntax.sigopts =
                          FStar_Pervasives_Native.None
                      }
let rec (desugar_tycon :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Parser_AST.tycon Prims.list ->
          (env_t * FStar_Syntax_Syntax.sigelts))
  =
  fun env ->
    fun d ->
      fun quals ->
        fun tcs ->
          let rng = d.FStar_Parser_AST.drange in
          let tycon_id uu___17_20446 =
            match uu___17_20446 with
            | FStar_Parser_AST.TyconAbstract (id, uu____20448, uu____20449)
                -> id
            | FStar_Parser_AST.TyconAbbrev
                (id, uu____20459, uu____20460, uu____20461) -> id
            | FStar_Parser_AST.TyconRecord
                (id, uu____20471, uu____20472, uu____20473) -> id
            | FStar_Parser_AST.TyconVariant
                (id, uu____20495, uu____20496, uu____20497) -> id in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x, uu____20535) ->
                let uu____20536 =
                  let uu____20537 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____20537 in
                let uu____20538 = FStar_Ident.range_of_id x in
                FStar_Parser_AST.mk_term uu____20536 uu____20538
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____20540 =
                  let uu____20541 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____20541 in
                let uu____20542 = FStar_Ident.range_of_id x in
                FStar_Parser_AST.mk_term uu____20540 uu____20542
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a, uu____20544) ->
                let uu____20545 = FStar_Ident.range_of_id a in
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  uu____20545 FStar_Parser_AST.Type_level
            | FStar_Parser_AST.TVariable a ->
                let uu____20547 = FStar_Ident.range_of_id a in
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  uu____20547 FStar_Parser_AST.Type_level
            | FStar_Parser_AST.NoName t -> t in
          let tot =
            FStar_Parser_AST.mk_term
              (FStar_Parser_AST.Name FStar_Parser_Const.effect_Tot_lid) rng
              FStar_Parser_AST.Expr in
          let with_constructor_effect t =
            FStar_Parser_AST.mk_term
              (FStar_Parser_AST.App (tot, t, FStar_Parser_AST.Nothing))
              t.FStar_Parser_AST.range t.FStar_Parser_AST.level in
          let apply_binders t binders =
            let imp_of_aqual b =
              match b.FStar_Parser_AST.aqual with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit) ->
                  FStar_Parser_AST.Hash
              | uu____20577 -> FStar_Parser_AST.Nothing in
            FStar_List.fold_left
              (fun out ->
                 fun b ->
                   let uu____20585 =
                     let uu____20586 =
                       let uu____20593 = binder_to_term b in
                       (out, uu____20593, (imp_of_aqual b)) in
                     FStar_Parser_AST.App uu____20586 in
                   FStar_Parser_AST.mk_term uu____20585
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders in
          let tycon_record_as_variant uu___18_20605 =
            match uu___18_20605 with
            | FStar_Parser_AST.TyconRecord (id, parms, kopt, fields) ->
                let constrName =
                  let uu____20637 =
                    let uu____20643 =
                      let uu____20645 = FStar_Ident.string_of_id id in
                      Prims.op_Hat "Mk" uu____20645 in
                    let uu____20648 = FStar_Ident.range_of_id id in
                    (uu____20643, uu____20648) in
                  FStar_Ident.mk_ident uu____20637 in
                let mfields =
                  FStar_List.map
                    (fun uu____20661 ->
                       match uu____20661 with
                       | (x, t) ->
                           let uu____20668 = FStar_Ident.range_of_id x in
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated (x, t)) uu____20668
                             FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields in
                let result =
                  let uu____20670 =
                    let uu____20671 =
                      let uu____20672 = FStar_Ident.lid_of_ids [id] in
                      FStar_Parser_AST.Var uu____20672 in
                    let uu____20673 = FStar_Ident.range_of_id id in
                    FStar_Parser_AST.mk_term uu____20671 uu____20673
                      FStar_Parser_AST.Type_level in
                  apply_binders uu____20670 parms in
                let constrTyp =
                  let uu____20675 = FStar_Ident.range_of_id id in
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    uu____20675 FStar_Parser_AST.Type_level in
                let names =
                  let uu____20681 = binder_idents parms in id :: uu____20681 in
                (FStar_List.iter
                   (fun uu____20695 ->
                      match uu____20695 with
                      | (f, uu____20701) ->
                          let uu____20702 =
                            FStar_Util.for_some
                              (fun i -> FStar_Ident.ident_equals f i) names in
                          if uu____20702
                          then
                            let uu____20707 =
                              let uu____20713 =
                                let uu____20715 = FStar_Ident.string_of_id f in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu____20715 in
                              (FStar_Errors.Error_FieldShadow, uu____20713) in
                            let uu____20719 = FStar_Ident.range_of_id f in
                            FStar_Errors.raise_error uu____20707 uu____20719
                          else ()) fields;
                 (let uu____20722 =
                    FStar_All.pipe_right fields
                      (FStar_List.map FStar_Pervasives_Native.fst) in
                  ((FStar_Parser_AST.TyconVariant
                      (id, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp), false)])),
                    uu____20722)))
            | uu____20776 -> failwith "impossible" in
          let desugar_abstract_tc quals1 _env mutuals uu___19_20816 =
            match uu___19_20816 with
            | FStar_Parser_AST.TyconAbstract (id, binders, kopt) ->
                let uu____20840 = typars_of_binders _env binders in
                (match uu____20840 with
                 | (_env', typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k in
                     let tconstr =
                       let uu____20876 =
                         let uu____20877 =
                           let uu____20878 = FStar_Ident.lid_of_ids [id] in
                           FStar_Parser_AST.Var uu____20878 in
                         let uu____20879 = FStar_Ident.range_of_id id in
                         FStar_Parser_AST.mk_term uu____20877 uu____20879
                           FStar_Parser_AST.Type_level in
                       apply_binders uu____20876 binders in
                     let qlid = FStar_Syntax_DsEnv.qualify _env id in
                     let typars1 = FStar_Syntax_Subst.close_binders typars in
                     let k1 = FStar_Syntax_Subst.close typars1 k in
                     let se =
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_inductive_typ
                              (qlid, [], typars1, k1, mutuals, []));
                         FStar_Syntax_Syntax.sigrng = rng;
                         FStar_Syntax_Syntax.sigquals = quals1;
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = [];
                         FStar_Syntax_Syntax.sigopts =
                           FStar_Pervasives_Native.None
                       } in
                     let uu____20888 =
                       FStar_Syntax_DsEnv.push_top_level_rec_binding _env id
                         FStar_Syntax_Syntax.delta_constant in
                     (match uu____20888 with
                      | (_env1, uu____20905) ->
                          let uu____20912 =
                            FStar_Syntax_DsEnv.push_top_level_rec_binding
                              _env' id FStar_Syntax_Syntax.delta_constant in
                          (match uu____20912 with
                           | (_env2, uu____20929) ->
                               (_env1, _env2, se, tconstr))))
            | uu____20936 -> failwith "Unexpected tycon" in
          let push_tparams env1 bs =
            let uu____20979 =
              FStar_List.fold_left
                (fun uu____21013 ->
                   fun uu____21014 ->
                     match (uu____21013, uu____21014) with
                     | ((env2, tps), (x, imp)) ->
                         let uu____21083 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname in
                         (match uu____21083 with
                          | (env3, y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs in
            match uu____20979 with
            | (env2, bs1) -> (env2, (FStar_List.rev bs1)) in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id, bs, kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None ->
                    let uu____21174 =
                      let uu____21175 = FStar_Ident.range_of_id id in
                      tm_type_z uu____21175 in
                    FStar_Pervasives_Native.Some uu____21174
                | uu____21176 -> kopt in
              let tc = FStar_Parser_AST.TyconAbstract (id, bs, kopt1) in
              let uu____21184 = desugar_abstract_tc quals env [] tc in
              (match uu____21184 with
               | (uu____21197, uu____21198, se, uu____21200) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l, uu____21203, typars, k, [], []) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____21222 =
                                 let uu____21224 = FStar_Options.ml_ish () in
                                 Prims.op_Negation uu____21224 in
                               if uu____21222
                               then
                                 let uu____21227 =
                                   let uu____21233 =
                                     let uu____21235 =
                                       FStar_Syntax_Print.lid_to_string l in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____21235 in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____21233) in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____21227
                               else ());
                              FStar_Syntax_Syntax.Assumption
                              ::
                              FStar_Syntax_Syntax.New
                              ::
                              quals1) in
                         let t =
                           match typars with
                           | [] -> k
                           | uu____21248 ->
                               let uu____21249 =
                                 let uu____21250 =
                                   let uu____21265 =
                                     FStar_Syntax_Syntax.mk_Total k in
                                   (typars, uu____21265) in
                                 FStar_Syntax_Syntax.Tm_arrow uu____21250 in
                               FStar_Syntax_Syntax.mk uu____21249
                                 se.FStar_Syntax_Syntax.sigrng in
                         let uu___2843_21278 = se in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___2843_21278.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___2843_21278.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___2843_21278.FStar_Syntax_Syntax.sigattrs);
                           FStar_Syntax_Syntax.sigopts =
                             (uu___2843_21278.FStar_Syntax_Syntax.sigopts)
                         }
                     | uu____21279 -> failwith "Impossible" in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1 in
                   (env1, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t))::[] ->
              let uu____21294 = typars_of_binders env binders in
              (match uu____21294 with
               | (env', typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None ->
                         let uu____21328 =
                           FStar_Util.for_some
                             (fun uu___20_21331 ->
                                match uu___20_21331 with
                                | FStar_Syntax_Syntax.Effect -> true
                                | uu____21334 -> false) quals in
                         if uu____21328
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____21342 = desugar_term env' k in
                         FStar_Pervasives_Native.Some uu____21342 in
                   let t0 = t in
                   let quals1 =
                     let uu____21347 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___21_21353 ->
                               match uu___21_21353 with
                               | FStar_Syntax_Syntax.Logic -> true
                               | uu____21356 -> false)) in
                     if uu____21347
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals in
                   let qlid = FStar_Syntax_DsEnv.qualify env id in
                   let se =
                     let uu____21370 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect) in
                     if uu____21370
                     then
                       let uu____21376 =
                         let uu____21383 =
                           let uu____21384 = unparen t in
                           uu____21384.FStar_Parser_AST.tm in
                         match uu____21383 with
                         | FStar_Parser_AST.Construct (head, args) ->
                             let uu____21405 =
                               match FStar_List.rev args with
                               | (last_arg, uu____21435)::args_rev ->
                                   let uu____21447 =
                                     let uu____21448 = unparen last_arg in
                                     uu____21448.FStar_Parser_AST.tm in
                                   (match uu____21447 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____21476 -> ([], args))
                               | uu____21485 -> ([], args) in
                             (match uu____21405 with
                              | (cattributes, args1) ->
                                  let uu____21524 =
                                    desugar_attributes env cattributes in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____21524))
                         | uu____21535 -> (t, []) in
                       match uu____21376 with
                       | (t1, cattributes) ->
                           let c =
                             desugar_comp t1.FStar_Parser_AST.range false
                               env' t1 in
                           let typars1 =
                             FStar_Syntax_Subst.close_binders typars in
                           let c1 = FStar_Syntax_Subst.close_comp typars1 c in
                           let quals2 =
                             FStar_All.pipe_right quals1
                               (FStar_List.filter
                                  (fun uu___22_21558 ->
                                     match uu___22_21558 with
                                     | FStar_Syntax_Syntax.Effect -> false
                                     | uu____21561 -> true)) in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_effect_abbrev
                                  (qlid, [], typars1, c1,
                                    (FStar_List.append cattributes
                                       (FStar_Syntax_Util.comp_flags c1))));
                             FStar_Syntax_Syntax.sigrng = rng;
                             FStar_Syntax_Syntax.sigquals = quals2;
                             FStar_Syntax_Syntax.sigmeta =
                               FStar_Syntax_Syntax.default_sigmeta;
                             FStar_Syntax_Syntax.sigattrs = [];
                             FStar_Syntax_Syntax.sigopts =
                               FStar_Pervasives_Native.None
                           }
                     else
                       (let t1 = desugar_typ env' t in
                        mk_typ_abbrev env d qlid [] typars kopt1 t1 [qlid]
                          quals1 rng) in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se in
                   (env1, [se]))
          | (FStar_Parser_AST.TyconRecord uu____21569)::[] ->
              let trec = FStar_List.hd tcs in
              let uu____21589 = tycon_record_as_variant trec in
              (match uu____21589 with
               | (t, fs) ->
                   let uu____21606 =
                     let uu____21609 =
                       let uu____21610 =
                         let uu____21619 =
                           let uu____21622 =
                             FStar_Syntax_DsEnv.current_module env in
                           FStar_Ident.ids_of_lid uu____21622 in
                         (uu____21619, fs) in
                       FStar_Syntax_Syntax.RecordType uu____21610 in
                     uu____21609 :: quals in
                   desugar_tycon env d uu____21606 [t])
          | uu____21627::uu____21628 ->
              let env0 = env in
              let mutuals =
                FStar_List.map
                  (fun x ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs in
              let rec collect_tcs quals1 et tc =
                let uu____21786 = et in
                match uu____21786 with
                | (env1, tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____21996 ->
                         let trec = tc in
                         let uu____22016 = tycon_record_as_variant trec in
                         (match uu____22016 with
                          | (t, fs) ->
                              let uu____22072 =
                                let uu____22075 =
                                  let uu____22076 =
                                    let uu____22085 =
                                      let uu____22088 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1 in
                                      FStar_Ident.ids_of_lid uu____22088 in
                                    (uu____22085, fs) in
                                  FStar_Syntax_Syntax.RecordType uu____22076 in
                                uu____22075 :: quals1 in
                              collect_tcs uu____22072 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id, binders, kopt, constructors) ->
                         let uu____22166 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt)) in
                         (match uu____22166 with
                          | (env2, uu____22223, se, tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t) ->
                         let uu____22360 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt)) in
                         (match uu____22360 with
                          | (env2, uu____22417, se, tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____22533 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng) in
              let uu____22579 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs in
              (match uu____22579 with
               | (env1, tcs1) ->
                   let tcs2 = FStar_List.rev tcs1 in
                   let tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___24_23031 ->
                             match uu___24_23031 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id, uvs, tpars, k, uu____23085,
                                       uu____23086);
                                    FStar_Syntax_Syntax.sigrng = uu____23087;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____23088;
                                    FStar_Syntax_Syntax.sigmeta = uu____23089;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____23090;
                                    FStar_Syntax_Syntax.sigopts = uu____23091;_},
                                  binders, t, quals1)
                                 ->
                                 let t1 =
                                   let uu____23153 =
                                     typars_of_binders env1 binders in
                                   match uu____23153 with
                                   | (env2, tpars1) ->
                                       let uu____23180 =
                                         push_tparams env2 tpars1 in
                                       (match uu____23180 with
                                        | (env_tps, tpars2) ->
                                            let t1 = desugar_typ env_tps t in
                                            let tpars3 =
                                              FStar_Syntax_Subst.close_binders
                                                tpars2 in
                                            FStar_Syntax_Subst.close tpars3
                                              t1) in
                                 let uu____23209 =
                                   let uu____23220 =
                                     mk_typ_abbrev env1 d id uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id] quals1 rng in
                                   ([], uu____23220) in
                                 [uu____23209]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname, univs, tpars, k, mutuals1,
                                       uu____23256);
                                    FStar_Syntax_Syntax.sigrng = uu____23257;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____23259;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____23260;
                                    FStar_Syntax_Syntax.sigopts = uu____23261;_},
                                  constrs, tconstr, quals1)
                                 ->
                                 let mk_tot t =
                                   let tot1 =
                                     FStar_Parser_AST.mk_term
                                       (FStar_Parser_AST.Name
                                          FStar_Parser_Const.effect_Tot_lid)
                                       t.FStar_Parser_AST.range
                                       t.FStar_Parser_AST.level in
                                   FStar_Parser_AST.mk_term
                                     (FStar_Parser_AST.App
                                        (tot1, t, FStar_Parser_AST.Nothing))
                                     t.FStar_Parser_AST.range
                                     t.FStar_Parser_AST.level in
                                 let tycon = (tname, tpars, k) in
                                 let uu____23352 = push_tparams env1 tpars in
                                 (match uu____23352 with
                                  | (env_tps, tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____23411 ->
                                             match uu____23411 with
                                             | (x, uu____23423) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps in
                                      let tot_tconstr = mk_tot tconstr in
                                      let attrs =
                                        FStar_List.map (desugar_term env1)
                                          d.FStar_Parser_AST.attrs in
                                      let val_attrs =
                                        let uu____23434 =
                                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                                            env1 tname in
                                        FStar_All.pipe_right uu____23434
                                          FStar_Pervasives_Native.snd in
                                      let uu____23457 =
                                        let uu____23476 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____23553 ->
                                                  match uu____23553 with
                                                  | (id, topt, of_notation)
                                                      ->
                                                      let t =
                                                        if of_notation
                                                        then
                                                          match topt with
                                                          | FStar_Pervasives_Native.Some
                                                              t ->
                                                              FStar_Parser_AST.mk_term
                                                                (FStar_Parser_AST.Product
                                                                   ([
                                                                    FStar_Parser_AST.mk_binder
                                                                    (FStar_Parser_AST.NoName
                                                                    t)
                                                                    t.FStar_Parser_AST.range
                                                                    t.FStar_Parser_AST.level
                                                                    FStar_Pervasives_Native.None],
                                                                    tot_tconstr))
                                                                t.FStar_Parser_AST.range
                                                                t.FStar_Parser_AST.level
                                                          | FStar_Pervasives_Native.None
                                                              -> tconstr
                                                        else
                                                          (match topt with
                                                           | FStar_Pervasives_Native.None
                                                               ->
                                                               failwith
                                                                 "Impossible"
                                                           | FStar_Pervasives_Native.Some
                                                               t -> t) in
                                                      let t1 =
                                                        let uu____23596 =
                                                          close env_tps t in
                                                        desugar_term env_tps
                                                          uu____23596 in
                                                      let name =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env1 id in
                                                      let quals2 =
                                                        FStar_All.pipe_right
                                                          tname_quals
                                                          (FStar_List.collect
                                                             (fun
                                                                uu___23_23607
                                                                ->
                                                                match uu___23_23607
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____23619
                                                                    -> [])) in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars in
                                                      let uu____23627 =
                                                        let uu____23638 =
                                                          let uu____23639 =
                                                            let uu____23640 =
                                                              let uu____23656
                                                                =
                                                                let uu____23657
                                                                  =
                                                                  let uu____23660
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____23660 in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____23657 in
                                                              (name, univs,
                                                                uu____23656,
                                                                tname, ntps,
                                                                mutuals1) in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____23640 in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____23639;
                                                            FStar_Syntax_Syntax.sigrng
                                                              = rng;
                                                            FStar_Syntax_Syntax.sigquals
                                                              = quals2;
                                                            FStar_Syntax_Syntax.sigmeta
                                                              =
                                                              FStar_Syntax_Syntax.default_sigmeta;
                                                            FStar_Syntax_Syntax.sigattrs
                                                              =
                                                              (FStar_List.append
                                                                 val_attrs
                                                                 attrs);
                                                            FStar_Syntax_Syntax.sigopts
                                                              =
                                                              FStar_Pervasives_Native.None
                                                          } in
                                                        (tps, uu____23638) in
                                                      (name, uu____23627))) in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____23476 in
                                      (match uu____23457 with
                                       | (constrNames, constrs1) ->
                                           ([],
                                             {
                                               FStar_Syntax_Syntax.sigel =
                                                 (FStar_Syntax_Syntax.Sig_inductive_typ
                                                    (tname, univs, tpars, k,
                                                      mutuals1, constrNames));
                                               FStar_Syntax_Syntax.sigrng =
                                                 rng;
                                               FStar_Syntax_Syntax.sigquals =
                                                 tname_quals;
                                               FStar_Syntax_Syntax.sigmeta =
                                                 FStar_Syntax_Syntax.default_sigmeta;
                                               FStar_Syntax_Syntax.sigattrs =
                                                 (FStar_List.append val_attrs
                                                    attrs);
                                               FStar_Syntax_Syntax.sigopts =
                                                 FStar_Pervasives_Native.None
                                             })
                                           :: constrs1))
                             | uu____23792 -> failwith "impossible")) in
                   let sigelts =
                     FStar_All.pipe_right tps_sigelts
                       (FStar_List.map
                          (fun uu____23873 ->
                             match uu____23873 with | (uu____23884, se) -> se)) in
                   let uu____23898 =
                     let uu____23905 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____23905 rng in
                   (match uu____23898 with
                    | (bundle, abbrevs) ->
                        let env2 = FStar_Syntax_DsEnv.push_sigelt env0 bundle in
                        let env3 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env2 abbrevs in
                        let data_ops =
                          FStar_All.pipe_right tps_sigelts
                            (FStar_List.collect
                               (fun uu____23950 ->
                                  match uu____23950 with
                                  | (tps, se) ->
                                      mk_data_projector_names quals env3 se)) in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname, uu____23998, tps, k,
                                       uu____24001, constrs)
                                      ->
                                      let quals1 =
                                        se.FStar_Syntax_Syntax.sigquals in
                                      let quals2 =
                                        if
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract
                                             quals1)
                                            &&
                                            (Prims.op_Negation
                                               (FStar_List.contains
                                                  FStar_Syntax_Syntax.Private
                                                  quals1))
                                        then FStar_Syntax_Syntax.Private ::
                                          quals1
                                        else quals1 in
                                      let uu____24022 =
                                        FStar_All.pipe_right constrs
                                          (FStar_List.filter
                                             (fun data_lid ->
                                                let data_quals =
                                                  let data_se =
                                                    let uu____24037 =
                                                      FStar_All.pipe_right
                                                        sigelts
                                                        (FStar_List.find
                                                           (fun se1 ->
                                                              match se1.FStar_Syntax_Syntax.sigel
                                                              with
                                                              | FStar_Syntax_Syntax.Sig_datacon
                                                                  (name,
                                                                   uu____24054,
                                                                   uu____24055,
                                                                   uu____24056,
                                                                   uu____24057,
                                                                   uu____24058)
                                                                  ->
                                                                  FStar_Ident.lid_equals
                                                                    name
                                                                    data_lid
                                                              | uu____24065
                                                                  -> false)) in
                                                    FStar_All.pipe_right
                                                      uu____24037
                                                      FStar_Util.must in
                                                  data_se.FStar_Syntax_Syntax.sigquals in
                                                let uu____24069 =
                                                  FStar_All.pipe_right
                                                    data_quals
                                                    (FStar_List.existsb
                                                       (fun uu___25_24076 ->
                                                          match uu___25_24076
                                                          with
                                                          | FStar_Syntax_Syntax.RecordConstructor
                                                              uu____24078 ->
                                                              true
                                                          | uu____24088 ->
                                                              false)) in
                                                Prims.op_Negation uu____24069)) in
                                      mk_data_discriminators quals2 env3
                                        uu____24022
                                  | uu____24090 -> [])) in
                        let ops = FStar_List.append discs data_ops in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops in
                        (env4,
                          (FStar_List.append [bundle]
                             (FStar_List.append abbrevs ops)))))
          | [] -> failwith "impossible"
let (desugar_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
        Prims.list))
  =
  fun env ->
    fun binders ->
      let uu____24127 =
        FStar_List.fold_left
          (fun uu____24162 ->
             fun b ->
               match uu____24162 with
               | (env1, binders1) ->
                   let uu____24206 = desugar_binder env1 b in
                   (match uu____24206 with
                    | (FStar_Pervasives_Native.Some a, k) ->
                        let uu____24229 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k) in
                        (match uu____24229 with
                         | (binder, env2) -> (env2, (binder :: binders1)))
                    | uu____24282 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders in
      match uu____24127 with
      | (env1, binders1) -> (env1, (FStar_List.rev binders1))
let (push_reflect_effect :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Ident.lid -> FStar_Range.range -> FStar_Syntax_DsEnv.env)
  =
  fun env ->
    fun quals ->
      fun effect_name ->
        fun range ->
          let uu____24386 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___26_24393 ->
                    match uu___26_24393 with
                    | FStar_Syntax_Syntax.Reflectable uu____24395 -> true
                    | uu____24397 -> false)) in
          if uu____24386
          then
            let monad_env =
              let uu____24401 = FStar_Ident.ident_of_lid effect_name in
              FStar_Syntax_DsEnv.enter_monad_scope env uu____24401 in
            let reflect_lid =
              let uu____24403 = FStar_Ident.id_of_text "reflect" in
              FStar_All.pipe_right uu____24403
                (FStar_Syntax_DsEnv.qualify monad_env) in
            let quals1 =
              [FStar_Syntax_Syntax.Assumption;
              FStar_Syntax_Syntax.Reflectable effect_name] in
            let refl_decl =
              {
                FStar_Syntax_Syntax.sigel =
                  (FStar_Syntax_Syntax.Sig_declare_typ
                     (reflect_lid, [], FStar_Syntax_Syntax.tun));
                FStar_Syntax_Syntax.sigrng = range;
                FStar_Syntax_Syntax.sigquals = quals1;
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta;
                FStar_Syntax_Syntax.sigattrs = [];
                FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
              } in
            FStar_Syntax_DsEnv.push_sigelt env refl_decl
          else env
let (parse_attr_with_list :
  Prims.bool ->
    FStar_Syntax_Syntax.term ->
      FStar_Ident.lident ->
        (Prims.int Prims.list FStar_Pervasives_Native.option * Prims.bool))
  =
  fun warn ->
    fun at ->
      fun head ->
        let warn1 uu____24454 =
          if warn
          then
            let uu____24456 =
              let uu____24462 =
                let uu____24464 = FStar_Ident.string_of_lid head in
                FStar_Util.format1
                  "Found ill-applied '%s', argument should be a non-empty list of integer literals"
                  uu____24464 in
              (FStar_Errors.Warning_UnappliedFail, uu____24462) in
            FStar_Errors.log_issue at.FStar_Syntax_Syntax.pos uu____24456
          else () in
        let uu____24470 = FStar_Syntax_Util.head_and_args at in
        match uu____24470 with
        | (hd, args) ->
            let uu____24523 =
              let uu____24524 = FStar_Syntax_Subst.compress hd in
              uu____24524.FStar_Syntax_Syntax.n in
            (match uu____24523 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 FStar_Syntax_Syntax.fv_eq_lid fv head ->
                 (match args with
                  | [] -> ((FStar_Pervasives_Native.Some []), true)
                  | (a1, uu____24568)::[] ->
                      let uu____24593 =
                        let uu____24598 =
                          let uu____24607 =
                            FStar_Syntax_Embeddings.e_list
                              FStar_Syntax_Embeddings.e_int in
                          FStar_Syntax_Embeddings.unembed uu____24607 a1 in
                        uu____24598 true FStar_Syntax_Embeddings.id_norm_cb in
                      (match uu____24593 with
                       | FStar_Pervasives_Native.Some es ->
                           let uu____24630 =
                             let uu____24636 =
                               FStar_List.map FStar_BigInt.to_int_fs es in
                             FStar_Pervasives_Native.Some uu____24636 in
                           (uu____24630, true)
                       | uu____24651 ->
                           (warn1 (); (FStar_Pervasives_Native.None, true)))
                  | uu____24667 ->
                      (warn1 (); (FStar_Pervasives_Native.None, true)))
             | uu____24689 -> (FStar_Pervasives_Native.None, false))
let (get_fail_attr1 :
  Prims.bool ->
    FStar_Syntax_Syntax.term ->
      (Prims.int Prims.list * Prims.bool) FStar_Pervasives_Native.option)
  =
  fun warn ->
    fun at ->
      let rebind res b =
        match res with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some l ->
            FStar_Pervasives_Native.Some (l, b) in
      let uu____24806 =
        parse_attr_with_list warn at FStar_Parser_Const.fail_attr in
      match uu____24806 with
      | (res, matched) ->
          if matched
          then rebind res false
          else
            (let uu____24855 =
               parse_attr_with_list warn at FStar_Parser_Const.fail_lax_attr in
             match uu____24855 with | (res1, uu____24877) -> rebind res1 true)
let (get_fail_attr :
  Prims.bool ->
    FStar_Syntax_Syntax.term Prims.list ->
      (Prims.int Prims.list * Prims.bool) FStar_Pervasives_Native.option)
  =
  fun warn ->
    fun ats ->
      let comb f1 f2 =
        match (f1, f2) with
        | (FStar_Pervasives_Native.Some (e1, l1),
           FStar_Pervasives_Native.Some (e2, l2)) ->
            FStar_Pervasives_Native.Some
              ((FStar_List.append e1 e2), (l1 || l2))
        | (FStar_Pervasives_Native.Some (e, l), FStar_Pervasives_Native.None)
            -> FStar_Pervasives_Native.Some (e, l)
        | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (e, l))
            -> FStar_Pervasives_Native.Some (e, l)
        | uu____25204 -> FStar_Pervasives_Native.None in
      FStar_List.fold_right
        (fun at ->
           fun acc ->
             let uu____25262 = get_fail_attr1 warn at in comb uu____25262 acc)
        ats FStar_Pervasives_Native.None
let (lookup_effect_lid :
  FStar_Syntax_DsEnv.env ->
    FStar_Ident.lident -> FStar_Range.range -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env ->
    fun l ->
      fun r ->
        let uu____25297 = FStar_Syntax_DsEnv.try_lookup_effect_defn env l in
        match uu____25297 with
        | FStar_Pervasives_Native.None ->
            let uu____25300 =
              let uu____25306 =
                let uu____25308 =
                  let uu____25310 = FStar_Syntax_Print.lid_to_string l in
                  Prims.op_Hat uu____25310 " not found" in
                Prims.op_Hat "Effect name " uu____25308 in
              (FStar_Errors.Fatal_EffectNotFound, uu____25306) in
            FStar_Errors.raise_error uu____25300 r
        | FStar_Pervasives_Native.Some l1 -> l1
let rec (desugar_effect :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.decl ->
      FStar_Parser_AST.qualifiers ->
        Prims.bool ->
          FStar_Ident.ident ->
            FStar_Parser_AST.binder Prims.list ->
              FStar_Parser_AST.term ->
                FStar_Parser_AST.decl Prims.list ->
                  FStar_Parser_AST.term Prims.list ->
                    (FStar_Syntax_DsEnv.env * FStar_Syntax_Syntax.sigelt
                      Prims.list))
  =
  fun env ->
    fun d ->
      fun quals ->
        fun is_layered ->
          fun eff_name ->
            fun eff_binders ->
              fun eff_typ ->
                fun eff_decls ->
                  fun attrs ->
                    let env0 = env in
                    let monad_env =
                      FStar_Syntax_DsEnv.enter_monad_scope env eff_name in
                    let uu____25466 = desugar_binders monad_env eff_binders in
                    match uu____25466 with
                    | (env1, binders) ->
                        let eff_t = desugar_term env1 eff_typ in
                        let num_indices =
                          let uu____25505 =
                            let uu____25514 =
                              FStar_Syntax_Util.arrow_formals eff_t in
                            FStar_Pervasives_Native.fst uu____25514 in
                          FStar_List.length uu____25505 in
                        (if is_layered && (num_indices <= Prims.int_one)
                         then
                           (let uu____25532 =
                              let uu____25538 =
                                let uu____25540 =
                                  let uu____25542 =
                                    FStar_Ident.string_of_id eff_name in
                                  Prims.op_Hat uu____25542
                                    "is defined as a layered effect but has no indices" in
                                Prims.op_Hat "Effect " uu____25540 in
                              (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                uu____25538) in
                            FStar_Errors.raise_error uu____25532
                              d.FStar_Parser_AST.drange)
                         else ();
                         (let for_free = num_indices = Prims.int_one in
                          let mandatory_members =
                            let rr_members = ["repr"; "return"; "bind"] in
                            if for_free
                            then rr_members
                            else
                              if is_layered
                              then
                                FStar_List.append rr_members
                                  ["subcomp"; "if_then_else"]
                              else
                                FStar_List.append rr_members
                                  ["return_wp";
                                  "bind_wp";
                                  "if_then_else";
                                  "ite_wp";
                                  "stronger";
                                  "close_wp";
                                  "trivial"] in
                          let name_of_eff_decl decl =
                            match decl.FStar_Parser_AST.d with
                            | FStar_Parser_AST.Tycon
                                (uu____25610, uu____25611,
                                 (FStar_Parser_AST.TyconAbbrev
                                 (name, uu____25613, uu____25614,
                                  uu____25615))::[])
                                -> FStar_Ident.string_of_id name
                            | uu____25630 ->
                                failwith
                                  "Malformed effect member declaration." in
                          let uu____25633 =
                            FStar_List.partition
                              (fun decl ->
                                 let uu____25645 = name_of_eff_decl decl in
                                 FStar_List.mem uu____25645 mandatory_members)
                              eff_decls in
                          match uu____25633 with
                          | (mandatory_members_decls, actions) ->
                              let uu____25664 =
                                FStar_All.pipe_right mandatory_members_decls
                                  (FStar_List.fold_left
                                     (fun uu____25693 ->
                                        fun decl ->
                                          match uu____25693 with
                                          | (env2, out) ->
                                              let uu____25713 =
                                                desugar_decl env2 decl in
                                              (match uu____25713 with
                                               | (env3, ses) ->
                                                   let uu____25726 =
                                                     let uu____25729 =
                                                       FStar_List.hd ses in
                                                     uu____25729 :: out in
                                                   (env3, uu____25726)))
                                     (env1, [])) in
                              (match uu____25664 with
                               | (env2, decls) ->
                                   let binders1 =
                                     FStar_Syntax_Subst.close_binders binders in
                                   let actions1 =
                                     FStar_All.pipe_right actions
                                       (FStar_List.map
                                          (fun d1 ->
                                             match d1.FStar_Parser_AST.d with
                                             | FStar_Parser_AST.Tycon
                                                 (uu____25775, uu____25776,
                                                  (FStar_Parser_AST.TyconAbbrev
                                                  (name, action_params,
                                                   uu____25779,
                                                   {
                                                     FStar_Parser_AST.tm =
                                                       FStar_Parser_AST.Construct
                                                       (uu____25780,
                                                        (def, uu____25782)::
                                                        (cps_type,
                                                         uu____25784)::[]);
                                                     FStar_Parser_AST.range =
                                                       uu____25785;
                                                     FStar_Parser_AST.level =
                                                       uu____25786;_}))::[])
                                                 when
                                                 Prims.op_Negation for_free
                                                 ->
                                                 let uu____25819 =
                                                   desugar_binders env2
                                                     action_params in
                                                 (match uu____25819 with
                                                  | (env3, action_params1) ->
                                                      let action_params2 =
                                                        FStar_Syntax_Subst.close_binders
                                                          action_params1 in
                                                      let uu____25851 =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env3 name in
                                                      let uu____25852 =
                                                        let uu____25853 =
                                                          desugar_term env3
                                                            def in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25853 in
                                                      let uu____25860 =
                                                        let uu____25861 =
                                                          desugar_typ env3
                                                            cps_type in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25861 in
                                                      {
                                                        FStar_Syntax_Syntax.action_name
                                                          = uu____25851;
                                                        FStar_Syntax_Syntax.action_unqualified_name
                                                          = name;
                                                        FStar_Syntax_Syntax.action_univs
                                                          = [];
                                                        FStar_Syntax_Syntax.action_params
                                                          = action_params2;
                                                        FStar_Syntax_Syntax.action_defn
                                                          = uu____25852;
                                                        FStar_Syntax_Syntax.action_typ
                                                          = uu____25860
                                                      })
                                             | FStar_Parser_AST.Tycon
                                                 (uu____25868, uu____25869,
                                                  (FStar_Parser_AST.TyconAbbrev
                                                  (name, action_params,
                                                   uu____25872, defn))::[])
                                                 when for_free || is_layered
                                                 ->
                                                 let uu____25888 =
                                                   desugar_binders env2
                                                     action_params in
                                                 (match uu____25888 with
                                                  | (env3, action_params1) ->
                                                      let action_params2 =
                                                        FStar_Syntax_Subst.close_binders
                                                          action_params1 in
                                                      let uu____25920 =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env3 name in
                                                      let uu____25921 =
                                                        let uu____25922 =
                                                          desugar_term env3
                                                            defn in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25922 in
                                                      {
                                                        FStar_Syntax_Syntax.action_name
                                                          = uu____25920;
                                                        FStar_Syntax_Syntax.action_unqualified_name
                                                          = name;
                                                        FStar_Syntax_Syntax.action_univs
                                                          = [];
                                                        FStar_Syntax_Syntax.action_params
                                                          = action_params2;
                                                        FStar_Syntax_Syntax.action_defn
                                                          = uu____25921;
                                                        FStar_Syntax_Syntax.action_typ
                                                          =
                                                          FStar_Syntax_Syntax.tun
                                                      })
                                             | uu____25929 ->
                                                 FStar_Errors.raise_error
                                                   (FStar_Errors.Fatal_MalformedActionDeclaration,
                                                     "Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples).")
                                                   d1.FStar_Parser_AST.drange)) in
                                   let eff_t1 =
                                     FStar_Syntax_Subst.close binders1 eff_t in
                                   let lookup s =
                                     let l =
                                       let uu____25948 =
                                         FStar_Ident.mk_ident
                                           (s, (d.FStar_Parser_AST.drange)) in
                                       FStar_Syntax_DsEnv.qualify env2
                                         uu____25948 in
                                     let uu____25950 =
                                       let uu____25951 =
                                         FStar_Syntax_DsEnv.fail_or env2
                                           (FStar_Syntax_DsEnv.try_lookup_definition
                                              env2) l in
                                       FStar_All.pipe_left
                                         (FStar_Syntax_Subst.close binders1)
                                         uu____25951 in
                                     ([], uu____25950) in
                                   let mname =
                                     FStar_Syntax_DsEnv.qualify env0 eff_name in
                                   let qualifiers =
                                     FStar_List.map
                                       (trans_qual d.FStar_Parser_AST.drange
                                          (FStar_Pervasives_Native.Some mname))
                                       quals in
                                   let dummy_tscheme =
                                     ([], FStar_Syntax_Syntax.tun) in
                                   let combinators =
                                     if for_free
                                     then
                                       let uu____25973 =
                                         let uu____25974 =
                                           let uu____25977 = lookup "repr" in
                                           FStar_Pervasives_Native.Some
                                             uu____25977 in
                                         let uu____25979 =
                                           let uu____25982 = lookup "return" in
                                           FStar_Pervasives_Native.Some
                                             uu____25982 in
                                         let uu____25984 =
                                           let uu____25987 = lookup "bind" in
                                           FStar_Pervasives_Native.Some
                                             uu____25987 in
                                         {
                                           FStar_Syntax_Syntax.ret_wp =
                                             dummy_tscheme;
                                           FStar_Syntax_Syntax.bind_wp =
                                             dummy_tscheme;
                                           FStar_Syntax_Syntax.stronger =
                                             dummy_tscheme;
                                           FStar_Syntax_Syntax.if_then_else =
                                             dummy_tscheme;
                                           FStar_Syntax_Syntax.ite_wp =
                                             dummy_tscheme;
                                           FStar_Syntax_Syntax.close_wp =
                                             dummy_tscheme;
                                           FStar_Syntax_Syntax.trivial =
                                             dummy_tscheme;
                                           FStar_Syntax_Syntax.repr =
                                             uu____25974;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____25979;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____25984
                                         } in
                                       FStar_Syntax_Syntax.DM4F_eff
                                         uu____25973
                                     else
                                       if is_layered
                                       then
                                         (let to_comb uu____26021 =
                                            match uu____26021 with
                                            | (us, t) ->
                                                ((us, t), dummy_tscheme) in
                                          let uu____26068 =
                                            let uu____26069 =
                                              FStar_Ident.lid_of_str "" in
                                            let uu____26071 =
                                              let uu____26076 = lookup "repr" in
                                              FStar_All.pipe_right
                                                uu____26076 to_comb in
                                            let uu____26094 =
                                              let uu____26099 =
                                                lookup "return" in
                                              FStar_All.pipe_right
                                                uu____26099 to_comb in
                                            let uu____26117 =
                                              let uu____26122 = lookup "bind" in
                                              FStar_All.pipe_right
                                                uu____26122 to_comb in
                                            let uu____26140 =
                                              let uu____26145 =
                                                lookup "subcomp" in
                                              FStar_All.pipe_right
                                                uu____26145 to_comb in
                                            let uu____26163 =
                                              let uu____26168 =
                                                lookup "if_then_else" in
                                              FStar_All.pipe_right
                                                uu____26168 to_comb in
                                            {
                                              FStar_Syntax_Syntax.l_base_effect
                                                = uu____26069;
                                              FStar_Syntax_Syntax.l_repr =
                                                uu____26071;
                                              FStar_Syntax_Syntax.l_return =
                                                uu____26094;
                                              FStar_Syntax_Syntax.l_bind =
                                                uu____26117;
                                              FStar_Syntax_Syntax.l_subcomp =
                                                uu____26140;
                                              FStar_Syntax_Syntax.l_if_then_else
                                                = uu____26163
                                            } in
                                          FStar_Syntax_Syntax.Layered_eff
                                            uu____26068)
                                       else
                                         (let rr =
                                            FStar_Util.for_some
                                              (fun uu___27_26191 ->
                                                 match uu___27_26191 with
                                                 | FStar_Syntax_Syntax.Reifiable
                                                     -> true
                                                 | FStar_Syntax_Syntax.Reflectable
                                                     uu____26194 -> true
                                                 | uu____26196 -> false)
                                              qualifiers in
                                          let uu____26198 =
                                            let uu____26199 =
                                              lookup "return_wp" in
                                            let uu____26201 =
                                              lookup "bind_wp" in
                                            let uu____26203 =
                                              lookup "stronger" in
                                            let uu____26205 =
                                              lookup "if_then_else" in
                                            let uu____26207 = lookup "ite_wp" in
                                            let uu____26209 =
                                              lookup "close_wp" in
                                            let uu____26211 =
                                              lookup "trivial" in
                                            let uu____26213 =
                                              if rr
                                              then
                                                let uu____26219 =
                                                  lookup "repr" in
                                                FStar_Pervasives_Native.Some
                                                  uu____26219
                                              else
                                                FStar_Pervasives_Native.None in
                                            let uu____26223 =
                                              if rr
                                              then
                                                let uu____26229 =
                                                  lookup "return" in
                                                FStar_Pervasives_Native.Some
                                                  uu____26229
                                              else
                                                FStar_Pervasives_Native.None in
                                            let uu____26233 =
                                              if rr
                                              then
                                                let uu____26239 =
                                                  lookup "bind" in
                                                FStar_Pervasives_Native.Some
                                                  uu____26239
                                              else
                                                FStar_Pervasives_Native.None in
                                            {
                                              FStar_Syntax_Syntax.ret_wp =
                                                uu____26199;
                                              FStar_Syntax_Syntax.bind_wp =
                                                uu____26201;
                                              FStar_Syntax_Syntax.stronger =
                                                uu____26203;
                                              FStar_Syntax_Syntax.if_then_else
                                                = uu____26205;
                                              FStar_Syntax_Syntax.ite_wp =
                                                uu____26207;
                                              FStar_Syntax_Syntax.close_wp =
                                                uu____26209;
                                              FStar_Syntax_Syntax.trivial =
                                                uu____26211;
                                              FStar_Syntax_Syntax.repr =
                                                uu____26213;
                                              FStar_Syntax_Syntax.return_repr
                                                = uu____26223;
                                              FStar_Syntax_Syntax.bind_repr =
                                                uu____26233
                                            } in
                                          FStar_Syntax_Syntax.Primitive_eff
                                            uu____26198) in
                                   let sigel =
                                     let uu____26244 =
                                       let uu____26245 =
                                         FStar_List.map (desugar_term env2)
                                           attrs in
                                       {
                                         FStar_Syntax_Syntax.mname = mname;
                                         FStar_Syntax_Syntax.cattributes = [];
                                         FStar_Syntax_Syntax.univs = [];
                                         FStar_Syntax_Syntax.binders =
                                           binders1;
                                         FStar_Syntax_Syntax.signature =
                                           ([], eff_t1);
                                         FStar_Syntax_Syntax.combinators =
                                           combinators;
                                         FStar_Syntax_Syntax.actions =
                                           actions1;
                                         FStar_Syntax_Syntax.eff_attrs =
                                           uu____26245
                                       } in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____26244 in
                                   let se =
                                     {
                                       FStar_Syntax_Syntax.sigel = sigel;
                                       FStar_Syntax_Syntax.sigrng =
                                         (d.FStar_Parser_AST.drange);
                                       FStar_Syntax_Syntax.sigquals =
                                         qualifiers;
                                       FStar_Syntax_Syntax.sigmeta =
                                         FStar_Syntax_Syntax.default_sigmeta;
                                       FStar_Syntax_Syntax.sigattrs = [];
                                       FStar_Syntax_Syntax.sigopts =
                                         FStar_Pervasives_Native.None
                                     } in
                                   let env3 =
                                     FStar_Syntax_DsEnv.push_sigelt env0 se in
                                   let env4 =
                                     FStar_All.pipe_right actions1
                                       (FStar_List.fold_left
                                          (fun env4 ->
                                             fun a ->
                                               let uu____26262 =
                                                 FStar_Syntax_Util.action_as_lb
                                                   mname a
                                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                                               FStar_Syntax_DsEnv.push_sigelt
                                                 env4 uu____26262) env3) in
                                   let env5 =
                                     push_reflect_effect env4 qualifiers
                                       mname d.FStar_Parser_AST.drange in
                                   (env5, [se]))))
and (desugar_redefine_effect :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.decl ->
      (FStar_Ident.lident FStar_Pervasives_Native.option ->
         FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier)
        ->
        FStar_Parser_AST.qualifier Prims.list ->
          FStar_Ident.ident ->
            FStar_Parser_AST.binder Prims.list ->
              FStar_Parser_AST.term ->
                (FStar_Syntax_DsEnv.env * FStar_Syntax_Syntax.sigelt
                  Prims.list))
  =
  fun env ->
    fun d ->
      fun trans_qual1 ->
        fun quals ->
          fun eff_name ->
            fun eff_binders ->
              fun defn ->
                let env0 = env in
                let env1 = FStar_Syntax_DsEnv.enter_monad_scope env eff_name in
                let uu____26285 = desugar_binders env1 eff_binders in
                match uu____26285 with
                | (env2, binders) ->
                    let uu____26322 =
                      let uu____26333 = head_and_args defn in
                      match uu____26333 with
                      | (head, args) ->
                          let lid =
                            match head.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____26370 ->
                                let uu____26371 =
                                  let uu____26377 =
                                    let uu____26379 =
                                      let uu____26381 =
                                        FStar_Parser_AST.term_to_string head in
                                      Prims.op_Hat uu____26381 " not found" in
                                    Prims.op_Hat "Effect " uu____26379 in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____26377) in
                                FStar_Errors.raise_error uu____26371
                                  d.FStar_Parser_AST.drange in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid in
                          let uu____26387 =
                            match FStar_List.rev args with
                            | (last_arg, uu____26417)::args_rev ->
                                let uu____26429 =
                                  let uu____26430 = unparen last_arg in
                                  uu____26430.FStar_Parser_AST.tm in
                                (match uu____26429 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____26458 -> ([], args))
                            | uu____26467 -> ([], args) in
                          (match uu____26387 with
                           | (cattributes, args1) ->
                               let uu____26510 = desugar_args env2 args1 in
                               let uu____26511 =
                                 desugar_attributes env2 cattributes in
                               (lid, ed, uu____26510, uu____26511)) in
                    (match uu____26322 with
                     | (ed_lid, ed, args, cattributes) ->
                         let binders1 =
                           FStar_Syntax_Subst.close_binders binders in
                         (if
                            (FStar_List.length args) <>
                              (FStar_List.length
                                 ed.FStar_Syntax_Syntax.binders)
                          then
                            FStar_Errors.raise_error
                              (FStar_Errors.Fatal_ArgumentLengthMismatch,
                                "Unexpected number of arguments to effect constructor")
                              defn.FStar_Parser_AST.range
                          else ();
                          (let uu____26551 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit in
                           match uu____26551 with
                           | (ed_binders, uu____26565, ed_binders_opening) ->
                               let sub' shift_n uu____26584 =
                                 match uu____26584 with
                                 | (us, x) ->
                                     let x1 =
                                       let uu____26599 =
                                         FStar_Syntax_Subst.shift_subst
                                           (shift_n + (FStar_List.length us))
                                           ed_binders_opening in
                                       FStar_Syntax_Subst.subst uu____26599 x in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args in
                                     let uu____26603 =
                                       let uu____26604 =
                                         FStar_Syntax_Subst.subst s x1 in
                                       (us, uu____26604) in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____26603 in
                               let sub = sub' Prims.int_zero in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name in
                               let ed1 =
                                 let uu____26625 =
                                   sub ed.FStar_Syntax_Syntax.signature in
                                 let uu____26626 =
                                   FStar_Syntax_Util.apply_eff_combinators
                                     sub ed.FStar_Syntax_Syntax.combinators in
                                 let uu____26627 =
                                   FStar_List.map
                                     (fun action ->
                                        let nparam =
                                          FStar_List.length
                                            action.FStar_Syntax_Syntax.action_params in
                                        let uu____26643 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name in
                                        let uu____26644 =
                                          let uu____26645 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn)) in
                                          FStar_Pervasives_Native.snd
                                            uu____26645 in
                                        let uu____26660 =
                                          let uu____26661 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ)) in
                                          FStar_Pervasives_Native.snd
                                            uu____26661 in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____26643;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____26644;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____26660
                                        }) ed.FStar_Syntax_Syntax.actions in
                                 {
                                   FStar_Syntax_Syntax.mname = mname;
                                   FStar_Syntax_Syntax.cattributes =
                                     cattributes;
                                   FStar_Syntax_Syntax.univs =
                                     (ed.FStar_Syntax_Syntax.univs);
                                   FStar_Syntax_Syntax.binders = binders1;
                                   FStar_Syntax_Syntax.signature =
                                     uu____26625;
                                   FStar_Syntax_Syntax.combinators =
                                     uu____26626;
                                   FStar_Syntax_Syntax.actions = uu____26627;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 } in
                               let se =
                                 let uu____26677 =
                                   let uu____26680 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname) in
                                   FStar_List.map uu____26680 quals in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (FStar_Syntax_Syntax.Sig_new_effect ed1);
                                   FStar_Syntax_Syntax.sigrng =
                                     (d.FStar_Parser_AST.drange);
                                   FStar_Syntax_Syntax.sigquals = uu____26677;
                                   FStar_Syntax_Syntax.sigmeta =
                                     FStar_Syntax_Syntax.default_sigmeta;
                                   FStar_Syntax_Syntax.sigattrs = [];
                                   FStar_Syntax_Syntax.sigopts =
                                     FStar_Pervasives_Native.None
                                 } in
                               let monad_env = env2 in
                               let env3 =
                                 FStar_Syntax_DsEnv.push_sigelt env0 se in
                               let env4 =
                                 FStar_All.pipe_right
                                   ed1.FStar_Syntax_Syntax.actions
                                   (FStar_List.fold_left
                                      (fun env4 ->
                                         fun a ->
                                           let uu____26695 =
                                             FStar_Syntax_Util.action_as_lb
                                               mname a
                                               (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                                           FStar_Syntax_DsEnv.push_sigelt
                                             env4 uu____26695) env3) in
                               let env5 =
                                 let uu____26697 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable) in
                                 if uu____26697
                                 then
                                   let reflect_lid =
                                     let uu____26704 =
                                       FStar_Ident.id_of_text "reflect" in
                                     FStar_All.pipe_right uu____26704
                                       (FStar_Syntax_DsEnv.qualify monad_env) in
                                   let quals1 =
                                     [FStar_Syntax_Syntax.Assumption;
                                     FStar_Syntax_Syntax.Reflectable mname] in
                                   let refl_decl =
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         (FStar_Syntax_Syntax.Sig_declare_typ
                                            (reflect_lid, [],
                                              FStar_Syntax_Syntax.tun));
                                       FStar_Syntax_Syntax.sigrng =
                                         (d.FStar_Parser_AST.drange);
                                       FStar_Syntax_Syntax.sigquals = quals1;
                                       FStar_Syntax_Syntax.sigmeta =
                                         FStar_Syntax_Syntax.default_sigmeta;
                                       FStar_Syntax_Syntax.sigattrs = [];
                                       FStar_Syntax_Syntax.sigopts =
                                         FStar_Pervasives_Native.None
                                     } in
                                   FStar_Syntax_DsEnv.push_sigelt env4
                                     refl_decl
                                 else env4 in
                               (env5, [se]))))
and (desugar_decl_aux :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts))
  =
  fun env ->
    fun d ->
      let no_fail_attrs ats =
        FStar_List.filter
          (fun at ->
             let uu____26737 = get_fail_attr1 false at in
             FStar_Option.isNone uu____26737) ats in
      let env0 =
        let uu____26758 = FStar_Syntax_DsEnv.snapshot env in
        FStar_All.pipe_right uu____26758 FStar_Pervasives_Native.snd in
      let attrs = FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs in
      let uu____26773 =
        let uu____26780 = get_fail_attr false attrs in
        match uu____26780 with
        | FStar_Pervasives_Native.Some (expected_errs, lax) ->
            let d1 =
              let uu___3398_26817 = d in
              {
                FStar_Parser_AST.d = (uu___3398_26817.FStar_Parser_AST.d);
                FStar_Parser_AST.drange =
                  (uu___3398_26817.FStar_Parser_AST.drange);
                FStar_Parser_AST.quals =
                  (uu___3398_26817.FStar_Parser_AST.quals);
                FStar_Parser_AST.attrs = []
              } in
            let uu____26818 =
              FStar_Errors.catch_errors
                (fun uu____26836 ->
                   FStar_Options.with_saved_options
                     (fun uu____26842 -> desugar_decl_noattrs env d1)) in
            (match uu____26818 with
             | (errs, r) ->
                 (match (errs, r) with
                  | ([], FStar_Pervasives_Native.Some (env1, ses)) ->
                      let ses1 =
                        FStar_List.map
                          (fun se ->
                             let uu___3413_26902 = se in
                             let uu____26903 = no_fail_attrs attrs in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (uu___3413_26902.FStar_Syntax_Syntax.sigel);
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___3413_26902.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___3413_26902.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___3413_26902.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs = uu____26903;
                               FStar_Syntax_Syntax.sigopts =
                                 (uu___3413_26902.FStar_Syntax_Syntax.sigopts)
                             }) ses in
                      let se =
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_fail
                               (expected_errs, lax, ses1));
                          FStar_Syntax_Syntax.sigrng =
                            (d1.FStar_Parser_AST.drange);
                          FStar_Syntax_Syntax.sigquals = [];
                          FStar_Syntax_Syntax.sigmeta =
                            FStar_Syntax_Syntax.default_sigmeta;
                          FStar_Syntax_Syntax.sigattrs = [];
                          FStar_Syntax_Syntax.sigopts =
                            FStar_Pervasives_Native.None
                        } in
                      (env0, [se])
                  | (errs1, ropt) ->
                      let errnos =
                        FStar_List.concatMap
                          (fun i ->
                             FStar_Common.list_of_option
                               i.FStar_Errors.issue_number) errs1 in
                      if expected_errs = []
                      then (env0, [])
                      else
                        (let uu____26956 =
                           FStar_Errors.find_multiset_discrepancy
                             expected_errs errnos in
                         match uu____26956 with
                         | FStar_Pervasives_Native.None -> (env0, [])
                         | FStar_Pervasives_Native.Some (e, n1, n2) ->
                             (FStar_List.iter FStar_Errors.print_issue errs1;
                              (let uu____27005 =
                                 let uu____27011 =
                                   let uu____27013 =
                                     FStar_Common.string_of_list
                                       FStar_Util.string_of_int expected_errs in
                                   let uu____27016 =
                                     FStar_Common.string_of_list
                                       FStar_Util.string_of_int errnos in
                                   let uu____27019 =
                                     FStar_Util.string_of_int e in
                                   let uu____27021 =
                                     FStar_Util.string_of_int n2 in
                                   let uu____27023 =
                                     FStar_Util.string_of_int n1 in
                                   FStar_Util.format5
                                     "This top-level definition was expected to raise error codes %s, but it raised %s (at desugaring time). Error #%s was raised %s times, instead of %s."
                                     uu____27013 uu____27016 uu____27019
                                     uu____27021 uu____27023 in
                                 (FStar_Errors.Error_DidNotFail, uu____27011) in
                               FStar_Errors.log_issue
                                 d1.FStar_Parser_AST.drange uu____27005);
                              (env0, [])))))
        | FStar_Pervasives_Native.None -> desugar_decl_noattrs env d in
      match uu____26773 with
      | (env1, sigelts) ->
          let rec val_attrs ses =
            match ses with
            | {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                  uu____27061;
                FStar_Syntax_Syntax.sigrng = uu____27062;
                FStar_Syntax_Syntax.sigquals = uu____27063;
                FStar_Syntax_Syntax.sigmeta = uu____27064;
                FStar_Syntax_Syntax.sigattrs = uu____27065;
                FStar_Syntax_Syntax.sigopts = uu____27066;_}::[] ->
                let uu____27079 =
                  let uu____27082 = FStar_List.hd sigelts in
                  FStar_Syntax_Util.lids_of_sigelt uu____27082 in
                FStar_All.pipe_right uu____27079
                  (FStar_List.collect
                     (fun nm ->
                        let uu____27090 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env0 nm in
                        FStar_Pervasives_Native.snd uu____27090))
            | {
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_inductive_typ uu____27103;
                FStar_Syntax_Syntax.sigrng = uu____27104;
                FStar_Syntax_Syntax.sigquals = uu____27105;
                FStar_Syntax_Syntax.sigmeta = uu____27106;
                FStar_Syntax_Syntax.sigattrs = uu____27107;
                FStar_Syntax_Syntax.sigopts = uu____27108;_}::uu____27109 ->
                let uu____27134 =
                  let uu____27137 = FStar_List.hd sigelts in
                  FStar_Syntax_Util.lids_of_sigelt uu____27137 in
                FStar_All.pipe_right uu____27134
                  (FStar_List.collect
                     (fun nm ->
                        let uu____27145 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env0 nm in
                        FStar_Pervasives_Native.snd uu____27145))
            | {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_fail
                  (_errs, _lax, ses1);
                FStar_Syntax_Syntax.sigrng = uu____27161;
                FStar_Syntax_Syntax.sigquals = uu____27162;
                FStar_Syntax_Syntax.sigmeta = uu____27163;
                FStar_Syntax_Syntax.sigattrs = uu____27164;
                FStar_Syntax_Syntax.sigopts = uu____27165;_}::[] ->
                FStar_List.collect (fun se -> val_attrs [se]) ses1
            | uu____27186 -> [] in
          let attrs1 =
            let uu____27192 = val_attrs sigelts in
            FStar_List.append attrs uu____27192 in
          let uu____27195 =
            FStar_List.map
              (fun sigelt ->
                 let uu___3473_27199 = sigelt in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___3473_27199.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___3473_27199.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___3473_27199.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___3473_27199.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs = attrs1;
                   FStar_Syntax_Syntax.sigopts =
                     (uu___3473_27199.FStar_Syntax_Syntax.sigopts)
                 }) sigelts in
          (env1, uu____27195)
and (desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env ->
    fun d ->
      let uu____27206 = desugar_decl_aux env d in
      match uu____27206 with
      | (env1, ses) ->
          let uu____27217 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs) in
          (env1, uu____27217)
and (desugar_decl_noattrs :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts))
  =
  fun env ->
    fun d ->
      let trans_qual1 = trans_qual d.FStar_Parser_AST.drange in
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Pragma p ->
          let p1 = trans_pragma p in
          (FStar_Syntax_Util.process_pragma p1 d.FStar_Parser_AST.drange;
           (let se =
              {
                FStar_Syntax_Syntax.sigel =
                  (FStar_Syntax_Syntax.Sig_pragma p1);
                FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta;
                FStar_Syntax_Syntax.sigattrs = [];
                FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
              } in
            (env, [se])))
      | FStar_Parser_AST.TopLevelModule id -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid in (env1, [])
      | FStar_Parser_AST.Friend lid ->
          let uu____27249 = FStar_Syntax_DsEnv.iface env in
          if uu____27249
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____27264 =
               let uu____27266 =
                 let uu____27268 = FStar_Syntax_DsEnv.dep_graph env in
                 let uu____27269 = FStar_Syntax_DsEnv.current_module env in
                 FStar_Parser_Dep.module_has_interface uu____27268
                   uu____27269 in
               Prims.op_Negation uu____27266 in
             if uu____27264
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____27283 =
                  let uu____27285 =
                    let uu____27287 = FStar_Syntax_DsEnv.dep_graph env in
                    FStar_Parser_Dep.module_has_interface uu____27287 lid in
                  Prims.op_Negation uu____27285 in
                if uu____27283
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____27301 =
                     let uu____27303 =
                       let uu____27305 = FStar_Syntax_DsEnv.dep_graph env in
                       FStar_Parser_Dep.deps_has_implementation uu____27305
                         lid in
                     Prims.op_Negation uu____27303 in
                   if uu____27301
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x, l) ->
          let uu____27323 = FStar_Syntax_DsEnv.push_module_abbrev env x l in
          (uu____27323, [])
      | FStar_Parser_AST.Tycon (is_effect, typeclass, tcs) ->
          let quals = d.FStar_Parser_AST.quals in
          let quals1 =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: quals
            else quals in
          let quals2 =
            if typeclass
            then
              match tcs with
              | (FStar_Parser_AST.TyconRecord uu____27352)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu____27371 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1 in
          let uu____27380 =
            let uu____27385 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2 in
            desugar_tycon env d uu____27385 tcs in
          (match uu____27380 with
           | (env1, ses) ->
               let mkclass lid =
                 let r = FStar_Ident.range_of_lid lid in
                 let uu____27403 =
                   let uu____27404 =
                     let uu____27411 =
                       let uu____27412 = tun_r r in
                       FStar_Syntax_Syntax.new_bv
                         (FStar_Pervasives_Native.Some r) uu____27412 in
                     FStar_Syntax_Syntax.mk_binder uu____27411 in
                   [uu____27404] in
                 let uu____27425 =
                   let uu____27428 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid in
                   let uu____27431 =
                     let uu____27442 =
                       let uu____27451 =
                         let uu____27452 = FStar_Ident.string_of_lid lid in
                         FStar_Syntax_Util.exp_string uu____27452 in
                       FStar_Syntax_Syntax.as_arg uu____27451 in
                     [uu____27442] in
                   FStar_Syntax_Util.mk_app uu____27428 uu____27431 in
                 FStar_Syntax_Util.abs uu____27403 uu____27425
                   FStar_Pervasives_Native.None in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____27492, id))::uu____27494 ->
                       FStar_Pervasives_Native.Some id
                   | uu____27497::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None in
                 let uu____27501 = get_fname se.FStar_Syntax_Syntax.sigquals in
                 match uu____27501 with
                 | FStar_Pervasives_Native.None -> []
                 | FStar_Pervasives_Native.Some id ->
                     let uu____27507 = FStar_Syntax_DsEnv.qualify env1 id in
                     [uu____27507] in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1, uu____27528) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid, uu____27538, uu____27539, uu____27540,
                      uu____27541, uu____27542)
                     ->
                     let uu____27551 =
                       let uu____27552 =
                         let uu____27553 =
                           let uu____27560 = mkclass lid in
                           (meths, uu____27560) in
                         FStar_Syntax_Syntax.Sig_splice uu____27553 in
                       {
                         FStar_Syntax_Syntax.sigel = uu____27552;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = [];
                         FStar_Syntax_Syntax.sigopts =
                           FStar_Pervasives_Native.None
                       } in
                     [uu____27551]
                 | uu____27563 -> [] in
               let extra =
                 if typeclass
                 then
                   let meths = FStar_List.concatMap get_meths ses in
                   FStar_List.concatMap (splice_decl meths) ses
                 else [] in
               let env2 =
                 FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt env1
                   extra in
               (env2, (FStar_List.append ses extra)))
      | FStar_Parser_AST.TopLevelLet (isrec, lets) ->
          let quals = d.FStar_Parser_AST.quals in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____27597;
                    FStar_Parser_AST.prange = uu____27598;_},
                  uu____27599)::[] -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____27609;
                    FStar_Parser_AST.prange = uu____27610;_},
                  uu____27611)::[] -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____27627;
                         FStar_Parser_AST.prange = uu____27628;_},
                       uu____27629);
                    FStar_Parser_AST.prange = uu____27630;_},
                  uu____27631)::[] -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____27653;
                         FStar_Parser_AST.prange = uu____27654;_},
                       uu____27655);
                    FStar_Parser_AST.prange = uu____27656;_},
                  uu____27657)::[] -> false
               | (p, uu____27686)::[] ->
                   let uu____27695 = is_app_pattern p in
                   Prims.op_Negation uu____27695
               | uu____27697 -> false) in
          if Prims.op_Negation expand_toplevel_pattern
          then
            let lets1 =
              FStar_List.map (fun x -> (FStar_Pervasives_Native.None, x))
                lets in
            let as_inner_let =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Let
                   (isrec, lets1,
                     (FStar_Parser_AST.mk_term
                        (FStar_Parser_AST.Const FStar_Const.Const_unit)
                        d.FStar_Parser_AST.drange FStar_Parser_AST.Expr)))
                d.FStar_Parser_AST.drange FStar_Parser_AST.Expr in
            let uu____27772 = desugar_term_maybe_top true env as_inner_let in
            (match uu____27772 with
             | (ds_lets, aq) ->
                 (check_no_aq aq;
                  (let uu____27785 =
                     let uu____27786 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets in
                     uu____27786.FStar_Syntax_Syntax.n in
                   match uu____27785 with
                   | FStar_Syntax_Syntax.Tm_let (lbs, uu____27796) ->
                       let fvs =
                         FStar_All.pipe_right
                           (FStar_Pervasives_Native.snd lbs)
                           (FStar_List.map
                              (fun lb ->
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname)) in
                       let uu____27827 =
                         FStar_List.fold_right
                           (fun fv ->
                              fun uu____27852 ->
                                match uu____27852 with
                                | (qs, ats) ->
                                    let uu____27879 =
                                      FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                                        env
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    (match uu____27879 with
                                     | (qs', ats') ->
                                         ((FStar_List.append qs' qs),
                                           (FStar_List.append ats' ats))))
                           fvs ([], []) in
                       (match uu____27827 with
                        | (val_quals, val_attrs) ->
                            let quals1 =
                              match quals with
                              | uu____27933::uu____27934 ->
                                  FStar_List.map
                                    (trans_qual1 FStar_Pervasives_Native.None)
                                    quals
                              | uu____27937 -> val_quals in
                            let quals2 =
                              let uu____27941 =
                                FStar_All.pipe_right lets1
                                  (FStar_Util.for_some
                                     (fun uu____27974 ->
                                        match uu____27974 with
                                        | (uu____27988, (uu____27989, t)) ->
                                            t.FStar_Parser_AST.level =
                                              FStar_Parser_AST.Formula)) in
                              if uu____27941
                              then FStar_Syntax_Syntax.Logic :: quals1
                              else quals1 in
                            let lbs1 =
                              let uu____28009 =
                                FStar_All.pipe_right quals2
                                  (FStar_List.contains
                                     FStar_Syntax_Syntax.Abstract) in
                              if uu____28009
                              then
                                let uu____28015 =
                                  FStar_All.pipe_right
                                    (FStar_Pervasives_Native.snd lbs)
                                    (FStar_List.map
                                       (fun lb ->
                                          let fv =
                                            FStar_Util.right
                                              lb.FStar_Syntax_Syntax.lbname in
                                          let uu___3651_28030 = lb in
                                          {
                                            FStar_Syntax_Syntax.lbname =
                                              (FStar_Util.Inr
                                                 (let uu___3653_28032 = fv in
                                                  {
                                                    FStar_Syntax_Syntax.fv_name
                                                      =
                                                      (uu___3653_28032.FStar_Syntax_Syntax.fv_name);
                                                    FStar_Syntax_Syntax.fv_delta
                                                      =
                                                      (FStar_Syntax_Syntax.Delta_abstract
                                                         (fv.FStar_Syntax_Syntax.fv_delta));
                                                    FStar_Syntax_Syntax.fv_qual
                                                      =
                                                      (uu___3653_28032.FStar_Syntax_Syntax.fv_qual)
                                                  }));
                                            FStar_Syntax_Syntax.lbunivs =
                                              (uu___3651_28030.FStar_Syntax_Syntax.lbunivs);
                                            FStar_Syntax_Syntax.lbtyp =
                                              (uu___3651_28030.FStar_Syntax_Syntax.lbtyp);
                                            FStar_Syntax_Syntax.lbeff =
                                              (uu___3651_28030.FStar_Syntax_Syntax.lbeff);
                                            FStar_Syntax_Syntax.lbdef =
                                              (uu___3651_28030.FStar_Syntax_Syntax.lbdef);
                                            FStar_Syntax_Syntax.lbattrs =
                                              (uu___3651_28030.FStar_Syntax_Syntax.lbattrs);
                                            FStar_Syntax_Syntax.lbpos =
                                              (uu___3651_28030.FStar_Syntax_Syntax.lbpos)
                                          })) in
                                ((FStar_Pervasives_Native.fst lbs),
                                  uu____28015)
                              else lbs in
                            let names =
                              FStar_All.pipe_right fvs
                                (FStar_List.map
                                   (fun fv ->
                                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                            let attrs =
                              FStar_List.map (desugar_term env)
                                d.FStar_Parser_AST.attrs in
                            let s =
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_let (lbs1, names));
                                FStar_Syntax_Syntax.sigrng =
                                  (d.FStar_Parser_AST.drange);
                                FStar_Syntax_Syntax.sigquals = quals2;
                                FStar_Syntax_Syntax.sigmeta =
                                  FStar_Syntax_Syntax.default_sigmeta;
                                FStar_Syntax_Syntax.sigattrs =
                                  (FStar_List.append val_attrs attrs);
                                FStar_Syntax_Syntax.sigopts =
                                  FStar_Pervasives_Native.None
                              } in
                            let env1 = FStar_Syntax_DsEnv.push_sigelt env s in
                            (env1, [s]))
                   | uu____28057 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____28065 =
               match lets with
               | (pat, body)::[] -> (pat, body)
               | uu____28084 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets" in
             match uu____28065 with
             | (pat, body) ->
                 let fresh_toplevel_name =
                   FStar_Ident.gen FStar_Range.dummyRange in
                 let fresh_pat =
                   let var_pat =
                     FStar_Parser_AST.mk_pattern
                       (FStar_Parser_AST.PatVar
                          (fresh_toplevel_name, FStar_Pervasives_Native.None))
                       FStar_Range.dummyRange in
                   match pat.FStar_Parser_AST.pat with
                   | FStar_Parser_AST.PatAscribed (pat1, ty) ->
                       let uu___3676_28121 = pat1 in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___3676_28121.FStar_Parser_AST.prange)
                       }
                   | uu____28128 -> var_pat in
                 let main_let =
                   let quals1 =
                     if
                       FStar_List.mem FStar_Parser_AST.Private
                         d.FStar_Parser_AST.quals
                     then d.FStar_Parser_AST.quals
                     else FStar_Parser_AST.Private ::
                       (d.FStar_Parser_AST.quals) in
                   desugar_decl env
                     (let uu___3682_28139 = d in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___3682_28139.FStar_Parser_AST.drange);
                        FStar_Parser_AST.quals = quals1;
                        FStar_Parser_AST.attrs =
                          (uu___3682_28139.FStar_Parser_AST.attrs)
                      }) in
                 let main =
                   let uu____28155 =
                     let uu____28156 =
                       FStar_Ident.lid_of_ids [fresh_toplevel_name] in
                     FStar_Parser_AST.Var uu____28156 in
                   FStar_Parser_AST.mk_term uu____28155
                     pat.FStar_Parser_AST.prange FStar_Parser_AST.Expr in
                 let build_generic_projection uu____28180 id_opt =
                   match uu____28180 with
                   | (env1, ses) ->
                       let uu____28202 =
                         match id_opt with
                         | FStar_Pervasives_Native.Some id ->
                             let lid = FStar_Ident.lid_of_ids [id] in
                             let branch =
                               let uu____28214 = FStar_Ident.range_of_lid lid in
                               FStar_Parser_AST.mk_term
                                 (FStar_Parser_AST.Var lid) uu____28214
                                 FStar_Parser_AST.Expr in
                             let bv_pat =
                               let uu____28216 = FStar_Ident.range_of_id id in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatVar
                                    (id, FStar_Pervasives_Native.None))
                                 uu____28216 in
                             (bv_pat, branch)
                         | FStar_Pervasives_Native.None ->
                             let id = FStar_Ident.gen FStar_Range.dummyRange in
                             let branch =
                               FStar_Parser_AST.mk_term
                                 (FStar_Parser_AST.Const
                                    FStar_Const.Const_unit)
                                 FStar_Range.dummyRange FStar_Parser_AST.Expr in
                             let bv_pat =
                               let uu____28222 = FStar_Ident.range_of_id id in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatVar
                                    (id, FStar_Pervasives_Native.None))
                                 uu____28222 in
                             let bv_pat1 =
                               let uu____28226 =
                                 let uu____28227 =
                                   let uu____28238 =
                                     let uu____28245 =
                                       let uu____28246 =
                                         FStar_Ident.range_of_id id in
                                       unit_ty uu____28246 in
                                     (uu____28245,
                                       FStar_Pervasives_Native.None) in
                                   (bv_pat, uu____28238) in
                                 FStar_Parser_AST.PatAscribed uu____28227 in
                               let uu____28255 = FStar_Ident.range_of_id id in
                               FStar_Parser_AST.mk_pattern uu____28226
                                 uu____28255 in
                             (bv_pat1, branch) in
                       (match uu____28202 with
                        | (bv_pat, branch) ->
                            let body1 =
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Match
                                   (main,
                                     [(pat, FStar_Pervasives_Native.None,
                                        branch)]))
                                main.FStar_Parser_AST.range
                                FStar_Parser_AST.Expr in
                            let id_decl =
                              FStar_Parser_AST.mk_decl
                                (FStar_Parser_AST.TopLevelLet
                                   (FStar_Parser_AST.NoLetQualifier,
                                     [(bv_pat, body1)]))
                                FStar_Range.dummyRange [] in
                            let id_decl1 =
                              let uu___3706_28309 = id_decl in
                              {
                                FStar_Parser_AST.d =
                                  (uu___3706_28309.FStar_Parser_AST.d);
                                FStar_Parser_AST.drange =
                                  (uu___3706_28309.FStar_Parser_AST.drange);
                                FStar_Parser_AST.quals =
                                  (d.FStar_Parser_AST.quals);
                                FStar_Parser_AST.attrs =
                                  (uu___3706_28309.FStar_Parser_AST.attrs)
                              } in
                            let uu____28310 = desugar_decl env1 id_decl1 in
                            (match uu____28310 with
                             | (env2, ses') ->
                                 (env2, (FStar_List.append ses ses')))) in
                 let build_projection uu____28346 id =
                   match uu____28346 with
                   | (env1, ses) ->
                       build_generic_projection (env1, ses)
                         (FStar_Pervasives_Native.Some id) in
                 let build_coverage_check uu____28385 =
                   match uu____28385 with
                   | (env1, ses) ->
                       build_generic_projection (env1, ses)
                         FStar_Pervasives_Native.None in
                 let bvs =
                   let uu____28409 = gather_pattern_bound_vars pat in
                   FStar_All.pipe_right uu____28409 FStar_Util.set_elements in
                 let uu____28416 =
                   (FStar_List.isEmpty bvs) &&
                     (let uu____28419 = is_var_pattern pat in
                      Prims.op_Negation uu____28419) in
                 if uu____28416
                 then build_coverage_check main_let
                 else FStar_List.fold_left build_projection main_let bvs)
      | FStar_Parser_AST.Assume (id, t) ->
          let f = desugar_formula env t in
          let lid = FStar_Syntax_DsEnv.qualify env id in
          (env,
            [{
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_assume (lid, [], f));
               FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
               FStar_Syntax_Syntax.sigquals =
                 [FStar_Syntax_Syntax.Assumption];
               FStar_Syntax_Syntax.sigmeta =
                 FStar_Syntax_Syntax.default_sigmeta;
               FStar_Syntax_Syntax.sigattrs = [];
               FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
             }])
      | FStar_Parser_AST.Val (id, t) ->
          let quals = d.FStar_Parser_AST.quals in
          let t1 =
            let uu____28442 = close_fun env t in desugar_term env uu____28442 in
          let quals1 =
            let uu____28446 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env) in
            if uu____28446
            then FStar_Parser_AST.Assumption :: quals
            else quals in
          let lid = FStar_Syntax_DsEnv.qualify env id in
          let attrs =
            FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs in
          let se =
            let uu____28458 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1 in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____28458;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = attrs;
              FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
            } in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se in (env1, [se])
      | FStar_Parser_AST.Exception (id, t_opt) ->
          let t =
            match t_opt with
            | FStar_Pervasives_Native.None ->
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_lid env)
                  FStar_Parser_Const.exn_lid
            | FStar_Pervasives_Native.Some term ->
                let t = desugar_term env term in
                let uu____28471 =
                  let uu____28480 = FStar_Syntax_Syntax.null_binder t in
                  [uu____28480] in
                let uu____28499 =
                  let uu____28502 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total
                    uu____28502 in
                FStar_Syntax_Util.arrow uu____28471 uu____28499 in
          let l = FStar_Syntax_DsEnv.qualify env id in
          let qual = [FStar_Syntax_Syntax.ExceptionConstructor] in
          let se =
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_datacon
                   (l, [], t, FStar_Parser_Const.exn_lid, Prims.int_zero,
                     [FStar_Parser_Const.exn_lid]));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = qual;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = [];
              FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
            } in
          let se' =
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_bundle ([se], [l]));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = qual;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = [];
              FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
            } in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se' in
          let data_ops = mk_data_projector_names [] env1 se in
          let discs = mk_data_discriminators [] env1 [l] in
          let env2 =
            FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt env1
              (FStar_List.append discs data_ops) in
          (env2, (FStar_List.append (se' :: discs) data_ops))
      | FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect
          (eff_name, eff_binders, defn)) ->
          let quals = d.FStar_Parser_AST.quals in
          desugar_redefine_effect env d trans_qual1 quals eff_name
            eff_binders defn
      | FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect
          (eff_name, eff_binders, eff_typ, eff_decls)) ->
          let quals = d.FStar_Parser_AST.quals in
          let attrs = d.FStar_Parser_AST.attrs in
          desugar_effect env d quals false eff_name eff_binders eff_typ
            eff_decls attrs
      | FStar_Parser_AST.LayeredEffect (FStar_Parser_AST.DefineEffect
          (eff_name, eff_binders, eff_typ, eff_decls)) ->
          let quals = d.FStar_Parser_AST.quals in
          let attrs = d.FStar_Parser_AST.attrs in
          desugar_effect env d quals true eff_name eff_binders eff_typ
            eff_decls attrs
      | FStar_Parser_AST.LayeredEffect (FStar_Parser_AST.RedefineEffect
          uu____28565) ->
          failwith
            "Impossible: LayeredEffect (RedefineEffect _) (should not be parseable)"
      | FStar_Parser_AST.SubEffect l ->
          let src_ed =
            lookup_effect_lid env l.FStar_Parser_AST.msource
              d.FStar_Parser_AST.drange in
          let dst_ed =
            lookup_effect_lid env l.FStar_Parser_AST.mdest
              d.FStar_Parser_AST.drange in
          let uu____28582 =
            let uu____28584 =
              (FStar_Syntax_Util.is_layered src_ed) ||
                (FStar_Syntax_Util.is_layered dst_ed) in
            Prims.op_Negation uu____28584 in
          if uu____28582
          then
            let uu____28591 =
              match l.FStar_Parser_AST.lift_op with
              | FStar_Parser_AST.NonReifiableLift t ->
                  let uu____28609 =
                    let uu____28612 =
                      let uu____28613 = desugar_term env t in
                      ([], uu____28613) in
                    FStar_Pervasives_Native.Some uu____28612 in
                  (uu____28609, FStar_Pervasives_Native.None)
              | FStar_Parser_AST.ReifiableLift (wp, t) ->
                  let uu____28626 =
                    let uu____28629 =
                      let uu____28630 = desugar_term env wp in
                      ([], uu____28630) in
                    FStar_Pervasives_Native.Some uu____28629 in
                  let uu____28637 =
                    let uu____28640 =
                      let uu____28641 = desugar_term env t in
                      ([], uu____28641) in
                    FStar_Pervasives_Native.Some uu____28640 in
                  (uu____28626, uu____28637)
              | FStar_Parser_AST.LiftForFree t ->
                  let uu____28653 =
                    let uu____28656 =
                      let uu____28657 = desugar_term env t in
                      ([], uu____28657) in
                    FStar_Pervasives_Native.Some uu____28656 in
                  (FStar_Pervasives_Native.None, uu____28653) in
            (match uu____28591 with
             | (lift_wp, lift) ->
                 let se =
                   {
                     FStar_Syntax_Syntax.sigel =
                       (FStar_Syntax_Syntax.Sig_sub_effect
                          {
                            FStar_Syntax_Syntax.source =
                              (src_ed.FStar_Syntax_Syntax.mname);
                            FStar_Syntax_Syntax.target =
                              (dst_ed.FStar_Syntax_Syntax.mname);
                            FStar_Syntax_Syntax.lift_wp = lift_wp;
                            FStar_Syntax_Syntax.lift = lift
                          });
                     FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                     FStar_Syntax_Syntax.sigquals = [];
                     FStar_Syntax_Syntax.sigmeta =
                       FStar_Syntax_Syntax.default_sigmeta;
                     FStar_Syntax_Syntax.sigattrs = [];
                     FStar_Syntax_Syntax.sigopts =
                       FStar_Pervasives_Native.None
                   } in
                 (env, [se]))
          else
            (match l.FStar_Parser_AST.lift_op with
             | FStar_Parser_AST.NonReifiableLift t ->
                 let sub_eff =
                   let uu____28691 =
                     let uu____28694 =
                       let uu____28695 = desugar_term env t in
                       ([], uu____28695) in
                     FStar_Pervasives_Native.Some uu____28694 in
                   {
                     FStar_Syntax_Syntax.source =
                       (src_ed.FStar_Syntax_Syntax.mname);
                     FStar_Syntax_Syntax.target =
                       (dst_ed.FStar_Syntax_Syntax.mname);
                     FStar_Syntax_Syntax.lift_wp =
                       FStar_Pervasives_Native.None;
                     FStar_Syntax_Syntax.lift = uu____28691
                   } in
                 (env,
                   [{
                      FStar_Syntax_Syntax.sigel =
                        (FStar_Syntax_Syntax.Sig_sub_effect sub_eff);
                      FStar_Syntax_Syntax.sigrng =
                        (d.FStar_Parser_AST.drange);
                      FStar_Syntax_Syntax.sigquals = [];
                      FStar_Syntax_Syntax.sigmeta =
                        FStar_Syntax_Syntax.default_sigmeta;
                      FStar_Syntax_Syntax.sigattrs = [];
                      FStar_Syntax_Syntax.sigopts =
                        FStar_Pervasives_Native.None
                    }])
             | uu____28702 ->
                 failwith
                   "Impossible! unexpected lift_op for lift to a layered effect")
      | FStar_Parser_AST.Polymonadic_bind (m_eff, n_eff, p_eff, bind) ->
          let m = lookup_effect_lid env m_eff d.FStar_Parser_AST.drange in
          let n = lookup_effect_lid env n_eff d.FStar_Parser_AST.drange in
          let p = lookup_effect_lid env p_eff d.FStar_Parser_AST.drange in
          let uu____28715 =
            let uu____28716 =
              let uu____28717 =
                let uu____28718 =
                  let uu____28729 =
                    let uu____28730 = desugar_term env bind in
                    ([], uu____28730) in
                  ((m.FStar_Syntax_Syntax.mname),
                    (n.FStar_Syntax_Syntax.mname),
                    (p.FStar_Syntax_Syntax.mname), uu____28729,
                    ([], FStar_Syntax_Syntax.tun)) in
                FStar_Syntax_Syntax.Sig_polymonadic_bind uu____28718 in
              {
                FStar_Syntax_Syntax.sigel = uu____28717;
                FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta;
                FStar_Syntax_Syntax.sigattrs = [];
                FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
              } in
            [uu____28716] in
          (env, uu____28715)
      | FStar_Parser_AST.Polymonadic_subcomp (m_eff, n_eff, subcomp) ->
          let m = lookup_effect_lid env m_eff d.FStar_Parser_AST.drange in
          let n = lookup_effect_lid env n_eff d.FStar_Parser_AST.drange in
          let uu____28746 =
            let uu____28747 =
              let uu____28748 =
                let uu____28749 =
                  let uu____28758 =
                    let uu____28759 = desugar_term env subcomp in
                    ([], uu____28759) in
                  ((m.FStar_Syntax_Syntax.mname),
                    (n.FStar_Syntax_Syntax.mname), uu____28758,
                    ([], FStar_Syntax_Syntax.tun)) in
                FStar_Syntax_Syntax.Sig_polymonadic_subcomp uu____28749 in
              {
                FStar_Syntax_Syntax.sigel = uu____28748;
                FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta;
                FStar_Syntax_Syntax.sigattrs = [];
                FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
              } in
            [uu____28747] in
          (env, uu____28746)
      | FStar_Parser_AST.Splice (ids, t) ->
          let t1 = desugar_term env t in
          let se =
            let uu____28778 =
              let uu____28779 =
                let uu____28786 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids in
                (uu____28786, t1) in
              FStar_Syntax_Syntax.Sig_splice uu____28779 in
            {
              FStar_Syntax_Syntax.sigel = uu____28778;
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = [];
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = [];
              FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
            } in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se in (env1, [se])
let (desugar_decls :
  env_t ->
    FStar_Parser_AST.decl Prims.list ->
      (env_t * FStar_Syntax_Syntax.sigelt Prims.list))
  =
  fun env ->
    fun decls ->
      let uu____28813 =
        FStar_List.fold_left
          (fun uu____28833 ->
             fun d ->
               match uu____28833 with
               | (env1, sigelts) ->
                   let uu____28853 = desugar_decl env1 d in
                   (match uu____28853 with
                    | (env2, se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls in
      match uu____28813 with | (env1, sigelts) -> (env1, sigelts)
let (open_prims_all :
  (FStar_Parser_AST.decoration Prims.list -> FStar_Parser_AST.decl)
    Prims.list)
  =
  [FStar_Parser_AST.mk_decl
     (FStar_Parser_AST.Open FStar_Parser_Const.prims_lid)
     FStar_Range.dummyRange;
  FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open FStar_Parser_Const.all_lid)
    FStar_Range.dummyRange]
let (desugar_modul_common :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Syntax_DsEnv.env ->
      FStar_Parser_AST.modul ->
        (env_t * FStar_Syntax_Syntax.modul * Prims.bool))
  =
  fun curmod ->
    fun env ->
      fun m ->
        let env1 =
          match (curmod, m) with
          | (FStar_Pervasives_Native.None, uu____28944) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____28948;
               FStar_Syntax_Syntax.exports = uu____28949;
               FStar_Syntax_Syntax.is_interface = uu____28950;_},
             FStar_Parser_AST.Module (current_lid, uu____28952)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod, uu____28961) ->
              let uu____28964 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod in
              FStar_Pervasives_Native.fst uu____28964 in
        let uu____28969 =
          match m with
          | FStar_Parser_AST.Interface (mname, decls, admitted) ->
              let uu____29011 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii in
              (uu____29011, mname, decls, true)
          | FStar_Parser_AST.Module (mname, decls) ->
              let uu____29033 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii in
              (uu____29033, mname, decls, false) in
        match uu____28969 with
        | ((env2, pop_when_done), mname, decls, intf) ->
            let uu____29075 = desugar_decls env2 decls in
            (match uu____29075 with
             | (env3, sigelts) ->
                 let modul =
                   {
                     FStar_Syntax_Syntax.name = mname;
                     FStar_Syntax_Syntax.declarations = sigelts;
                     FStar_Syntax_Syntax.exports = [];
                     FStar_Syntax_Syntax.is_interface = intf
                   } in
                 (env3, modul, pop_when_done))
let (as_interface : FStar_Parser_AST.modul -> FStar_Parser_AST.modul) =
  fun m ->
    match m with
    | FStar_Parser_AST.Module (mname, decls) ->
        FStar_Parser_AST.Interface (mname, decls, true)
    | i -> i
let (desugar_partial_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    env_t -> FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun curmod ->
    fun env ->
      fun m ->
        let m1 =
          let uu____29143 =
            (FStar_Options.interactive ()) &&
              (let uu____29146 =
                 let uu____29148 =
                   let uu____29150 = FStar_Options.file_list () in
                   FStar_List.hd uu____29150 in
                 FStar_Util.get_file_extension uu____29148 in
               FStar_List.mem uu____29146 ["fsti"; "fsi"]) in
          if uu____29143 then as_interface m else m in
        let uu____29164 = desugar_modul_common curmod env m1 in
        match uu____29164 with
        | (env1, modul, pop_when_done) ->
            if pop_when_done
            then
              let uu____29186 = FStar_Syntax_DsEnv.pop () in
              (uu____29186, modul)
            else (env1, modul)
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun env ->
    fun m ->
      let uu____29208 =
        desugar_modul_common FStar_Pervasives_Native.None env m in
      match uu____29208 with
      | (env1, modul, pop_when_done) ->
          let uu____29225 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul in
          (match uu____29225 with
           | (env2, modul1) ->
               ((let uu____29237 =
                   let uu____29239 =
                     FStar_Ident.string_of_lid
                       modul1.FStar_Syntax_Syntax.name in
                   FStar_Options.dump_module uu____29239 in
                 if uu____29237
                 then
                   let uu____29242 =
                     FStar_Syntax_Print.modul_to_string modul1 in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____29242
                 else ());
                (let uu____29247 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2 in
                 (uu____29247, modul1))))
let with_options : 'a . (unit -> 'a) -> 'a =
  fun f ->
    FStar_Options.push ();
    (let res = f () in
     let light = FStar_Options.ml_ish () in
     FStar_Options.pop ();
     if light then FStar_Options.set_ml_ish () else ();
     res)
let (ast_modul_to_modul :
  FStar_Parser_AST.modul ->
    FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul ->
    fun env ->
      with_options
        (fun uu____29297 ->
           let uu____29298 = desugar_modul env modul in
           match uu____29298 with | (e, m) -> (m, e))
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls ->
    fun env ->
      with_options
        (fun uu____29336 ->
           let uu____29337 = desugar_decls env decls in
           match uu____29337 with | (env1, sigelts) -> (sigelts, env1))
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul ->
    fun a_modul ->
      fun env ->
        with_options
          (fun uu____29388 ->
             let uu____29389 = desugar_partial_modul modul env a_modul in
             match uu____29389 with | (env1, modul1) -> (modul1, env1))
let (add_modul_to_env :
  FStar_Syntax_Syntax.modul ->
    FStar_Syntax_DsEnv.module_inclusion_info ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        unit FStar_Syntax_DsEnv.withenv)
  =
  fun m ->
    fun mii ->
      fun erase_univs ->
        fun en ->
          let erase_univs_ed ed =
            let erase_binders bs =
              match bs with
              | [] -> []
              | uu____29484 ->
                  let t =
                    let uu____29494 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Range.dummyRange in
                    erase_univs uu____29494 in
                  let uu____29507 =
                    let uu____29508 = FStar_Syntax_Subst.compress t in
                    uu____29508.FStar_Syntax_Syntax.n in
                  (match uu____29507 with
                   | FStar_Syntax_Syntax.Tm_abs
                       (bs1, uu____29520, uu____29521) -> bs1
                   | uu____29546 -> failwith "Impossible") in
            let uu____29556 =
              let uu____29563 = erase_binders ed.FStar_Syntax_Syntax.binders in
              FStar_Syntax_Subst.open_term' uu____29563
                FStar_Syntax_Syntax.t_unit in
            match uu____29556 with
            | (binders, uu____29565, binders_opening) ->
                let erase_term t =
                  let uu____29573 =
                    let uu____29574 =
                      FStar_Syntax_Subst.subst binders_opening t in
                    erase_univs uu____29574 in
                  FStar_Syntax_Subst.close binders uu____29573 in
                let erase_tscheme uu____29592 =
                  match uu____29592 with
                  | (us, t) ->
                      let t1 =
                        let uu____29612 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening in
                        FStar_Syntax_Subst.subst uu____29612 t in
                      let uu____29615 =
                        let uu____29616 = erase_univs t1 in
                        FStar_Syntax_Subst.close binders uu____29616 in
                      ([], uu____29615) in
                let erase_action action =
                  let opening =
                    FStar_Syntax_Subst.shift_subst
                      (FStar_List.length
                         action.FStar_Syntax_Syntax.action_univs)
                      binders_opening in
                  let erased_action_params =
                    match action.FStar_Syntax_Syntax.action_params with
                    | [] -> []
                    | uu____29639 ->
                        let bs =
                          let uu____29649 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params in
                          FStar_All.pipe_left erase_binders uu____29649 in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Range.dummyRange in
                        let uu____29689 =
                          let uu____29690 =
                            let uu____29693 =
                              FStar_Syntax_Subst.close binders t in
                            FStar_Syntax_Subst.compress uu____29693 in
                          uu____29690.FStar_Syntax_Syntax.n in
                        (match uu____29689 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1, uu____29695, uu____29696) -> bs1
                         | uu____29721 -> failwith "Impossible") in
                  let erase_term1 t =
                    let uu____29729 =
                      let uu____29730 = FStar_Syntax_Subst.subst opening t in
                      erase_univs uu____29730 in
                    FStar_Syntax_Subst.close binders uu____29729 in
                  let uu___3984_29731 = action in
                  let uu____29732 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn in
                  let uu____29733 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___3984_29731.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___3984_29731.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____29732;
                    FStar_Syntax_Syntax.action_typ = uu____29733
                  } in
                let uu___3986_29734 = ed in
                let uu____29735 = FStar_Syntax_Subst.close_binders binders in
                let uu____29736 =
                  erase_tscheme ed.FStar_Syntax_Syntax.signature in
                let uu____29737 =
                  FStar_Syntax_Util.apply_eff_combinators erase_tscheme
                    ed.FStar_Syntax_Syntax.combinators in
                let uu____29738 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions in
                {
                  FStar_Syntax_Syntax.mname =
                    (uu___3986_29734.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.cattributes =
                    (uu___3986_29734.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____29735;
                  FStar_Syntax_Syntax.signature = uu____29736;
                  FStar_Syntax_Syntax.combinators = uu____29737;
                  FStar_Syntax_Syntax.actions = uu____29738;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___3986_29734.FStar_Syntax_Syntax.eff_attrs)
                } in
          let push_sigelt env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___3993_29754 = se in
                  let uu____29755 =
                    let uu____29756 = erase_univs_ed ed in
                    FStar_Syntax_Syntax.Sig_new_effect uu____29756 in
                  {
                    FStar_Syntax_Syntax.sigel = uu____29755;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___3993_29754.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___3993_29754.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___3993_29754.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___3993_29754.FStar_Syntax_Syntax.sigattrs);
                    FStar_Syntax_Syntax.sigopts =
                      (uu___3993_29754.FStar_Syntax_Syntax.sigopts)
                  } in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se' in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____29758 -> FStar_Syntax_DsEnv.push_sigelt env se in
          let uu____29759 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii in
          match uu____29759 with
          | (en1, pop_when_done) ->
              let en2 =
                let uu____29776 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name in
                FStar_List.fold_left push_sigelt uu____29776
                  m.FStar_Syntax_Syntax.exports in
              let env = FStar_Syntax_DsEnv.finish en2 m in
              let uu____29778 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env in
              ((), uu____29778)