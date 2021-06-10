open Prims
let (tun_r : FStar_Range.range -> FStar_Syntax_Syntax.term) =
  fun r ->
    let uu___ = FStar_Syntax_Syntax.tun in
    {
      FStar_Syntax_Syntax.n = (uu___.FStar_Syntax_Syntax.n);
      FStar_Syntax_Syntax.pos = r;
      FStar_Syntax_Syntax.vars = (uu___.FStar_Syntax_Syntax.vars)
    }
type annotated_pat =
  (FStar_Syntax_Syntax.pat * (FStar_Syntax_Syntax.bv *
    FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term Prims.list)
    Prims.list)
let desugar_disjunctive_pattern :
  'uuuuu .
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t *
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax * 'uuuuu) Prims.list) Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.branch Prims.list
  =
  fun annotated_pats ->
    fun when_opt ->
      fun branch ->
        FStar_All.pipe_right annotated_pats
          (FStar_List.map
             (fun uu___ ->
                match uu___ with
                | (pat, annots) ->
                    let branch1 =
                      FStar_List.fold_left
                        (fun br ->
                           fun uu___1 ->
                             match uu___1 with
                             | (bv, ty, uu___2) ->
                                 let lb =
                                   let uu___3 =
                                     FStar_Syntax_Syntax.bv_to_name bv in
                                   FStar_Syntax_Util.mk_letbinding
                                     (FStar_Pervasives.Inl bv) [] ty
                                     FStar_Parser_Const.effect_Tot_lid uu___3
                                     [] br.FStar_Syntax_Syntax.pos in
                                 let branch2 =
                                   let uu___3 =
                                     let uu___4 =
                                       FStar_Syntax_Syntax.mk_binder bv in
                                     [uu___4] in
                                   FStar_Syntax_Subst.close uu___3 branch in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((false, [lb]), branch2))
                                   br.FStar_Syntax_Syntax.pos) branch annots in
                    FStar_Syntax_Util.branch (pat, when_opt, branch1)))
let (trans_qual :
  FStar_Range.range ->
    FStar_Ident.lident FStar_Pervasives_Native.option ->
      FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier)
  =
  fun r ->
    fun maybe_effect_id ->
      fun uu___ ->
        match uu___ with
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
  fun uu___ ->
    match uu___ with
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
  fun uu___ ->
    match uu___ with
    | FStar_Parser_AST.Hash ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | uu___1 -> FStar_Pervasives_Native.None
let arg_withimp_e :
  'uuuuu .
    FStar_Parser_AST.imp ->
      'uuuuu ->
        ('uuuuu * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  = fun imp -> fun t -> (t, (as_imp imp))
let arg_withimp_t :
  'uuuuu .
    FStar_Parser_AST.imp ->
      'uuuuu ->
        ('uuuuu * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  =
  fun imp ->
    fun t ->
      match imp with
      | FStar_Parser_AST.Hash ->
          (t, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag))
      | uu___ -> (t, FStar_Pervasives_Native.None)
let (contains_binder : FStar_Parser_AST.binder Prims.list -> Prims.bool) =
  fun binders ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu___ -> true
            | uu___ -> false))
let rec (unparen : FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun t ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu___ -> t
let (tm_type_z : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r ->
    let uu___ =
      let uu___1 = FStar_Ident.lid_of_path ["Type0"] r in
      FStar_Parser_AST.Name uu___1 in
    FStar_Parser_AST.mk_term uu___ r FStar_Parser_AST.Kind
let (tm_type : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r ->
    let uu___ =
      let uu___1 = FStar_Ident.lid_of_path ["Type"] r in
      FStar_Parser_AST.Name uu___1 in
    FStar_Parser_AST.mk_term uu___ r FStar_Parser_AST.Kind
let rec (is_comp_type :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun env ->
    fun t ->
      let uu___ = let uu___1 = unparen t in uu___1.FStar_Parser_AST.tm in
      match uu___ with
      | FStar_Parser_AST.Name l ->
          let uu___1 = FStar_Syntax_DsEnv.try_lookup_effect_name env l in
          FStar_All.pipe_right uu___1 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l, uu___1) ->
          let uu___2 = FStar_Syntax_DsEnv.try_lookup_effect_name env l in
          FStar_All.pipe_right uu___2 FStar_Option.isSome
      | FStar_Parser_AST.App (head, uu___1, uu___2) -> is_comp_type env head
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1, uu___1, uu___2) -> is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu___1, t1) -> is_comp_type env t1
      | uu___1 -> false
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
  'uuuuu .
    'uuuuu ->
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
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_Parser_AST.compile_op n s r in (uu___3, r) in
            FStar_Ident.mk_ident uu___2 in
          [uu___1] in
        FStar_All.pipe_right uu___ FStar_Ident.lid_of_ids
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
          let uu___ =
            let uu___1 =
              let uu___2 =
                let uu___3 = FStar_Ident.range_of_id op in
                FStar_Ident.set_lid_range l uu___3 in
              FStar_Syntax_Syntax.lid_as_fv uu___2 dd
                FStar_Pervasives_Native.None in
            FStar_All.pipe_right uu___1 FStar_Syntax_Syntax.fv_to_tm in
          FStar_Pervasives_Native.Some uu___ in
        let fallback uu___ =
          let uu___1 = FStar_Ident.string_of_id op in
          match uu___1 with
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
              let uu___2 = FStar_Options.ml_ish () in
              if uu___2
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
          | uu___2 -> FStar_Pervasives_Native.None in
        let uu___ =
          let uu___1 =
            let uu___2 = FStar_Ident.string_of_id op in
            let uu___3 = FStar_Ident.range_of_id op in
            compile_op_lid arity uu___2 uu___3 in
          desugar_name'
            (fun t ->
               let uu___2 = t in
               let uu___3 = FStar_Ident.range_of_id op in
               {
                 FStar_Syntax_Syntax.n = (uu___2.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = uu___3;
                 FStar_Syntax_Syntax.vars = (uu___2.FStar_Syntax_Syntax.vars)
               }) env true uu___1 in
        match uu___ with
        | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
        | uu___1 -> fallback ()
let (sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list)
  =
  fun ftv ->
    let uu___ =
      FStar_Util.remove_dups
        (fun x ->
           fun y ->
             let uu___1 = FStar_Ident.string_of_id x in
             let uu___2 = FStar_Ident.string_of_id y in uu___1 = uu___2) ftv in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x ->
            fun y ->
              let uu___1 = FStar_Ident.string_of_id x in
              let uu___2 = FStar_Ident.string_of_id y in
              FStar_String.compare uu___1 uu___2)) uu___
let rec (free_type_vars_b :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Syntax_DsEnv.env * FStar_Ident.ident Prims.list))
  =
  fun env ->
    fun binder ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu___ -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu___ = FStar_Syntax_DsEnv.push_bv env x in
          (match uu___ with | (env1, uu___1) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu___, term) ->
          let uu___1 = free_type_vars env term in (env, uu___1)
      | FStar_Parser_AST.TAnnotated (id, uu___) ->
          let uu___1 = FStar_Syntax_DsEnv.push_bv env id in
          (match uu___1 with | (env1, uu___2) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu___ = free_type_vars env t in (env, uu___)
and (free_type_vars :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list)
  =
  fun env ->
    fun t ->
      let uu___ = let uu___1 = unparen t in uu___1.FStar_Parser_AST.tm in
      match uu___ with
      | FStar_Parser_AST.Labeled uu___1 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu___1 = FStar_Syntax_DsEnv.try_lookup_id env a in
          (match uu___1 with
           | FStar_Pervasives_Native.None -> [a]
           | uu___2 -> [])
      | FStar_Parser_AST.Wild -> []
      | FStar_Parser_AST.Const uu___1 -> []
      | FStar_Parser_AST.Uvar uu___1 -> []
      | FStar_Parser_AST.Var uu___1 -> []
      | FStar_Parser_AST.Projector uu___1 -> []
      | FStar_Parser_AST.Discrim uu___1 -> []
      | FStar_Parser_AST.Name uu___1 -> []
      | FStar_Parser_AST.Requires (t1, uu___1) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1, uu___1) -> free_type_vars env t1
      | FStar_Parser_AST.Decreases (t1, uu___1) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu___1, t1) -> free_type_vars env t1
      | FStar_Parser_AST.LexList l ->
          FStar_List.collect (free_type_vars env) l
      | FStar_Parser_AST.WFOrder (rel, e) ->
          let uu___1 = free_type_vars env rel in
          let uu___2 = free_type_vars env e in
          FStar_List.append uu___1 uu___2
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1, t', tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None -> []
             | FStar_Pervasives_Native.Some t2 -> [t2]) in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu___1, ts) ->
          FStar_List.collect
            (fun uu___2 ->
               match uu___2 with | (t1, uu___3) -> free_type_vars env t1) ts
      | FStar_Parser_AST.Op (uu___1, ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1, t2, uu___1) ->
          let uu___2 = free_type_vars env t1 in
          let uu___3 = free_type_vars env t2 in
          FStar_List.append uu___2 uu___3
      | FStar_Parser_AST.Refine (b, t1) ->
          let uu___1 = free_type_vars_b env b in
          (match uu___1 with
           | (env1, f) ->
               let uu___2 = free_type_vars env1 t1 in
               FStar_List.append f uu___2)
      | FStar_Parser_AST.Sum (binders, body) ->
          let uu___1 =
            FStar_List.fold_left
              (fun uu___2 ->
                 fun bt ->
                   match uu___2 with
                   | (env1, free) ->
                       let uu___3 =
                         match bt with
                         | FStar_Pervasives.Inl binder ->
                             free_type_vars_b env1 binder
                         | FStar_Pervasives.Inr t1 ->
                             let uu___4 = free_type_vars env1 t1 in
                             (env1, uu___4) in
                       (match uu___3 with
                        | (env2, f) -> (env2, (FStar_List.append f free))))
              (env, []) binders in
          (match uu___1 with
           | (env1, free) ->
               let uu___2 = free_type_vars env1 body in
               FStar_List.append free uu___2)
      | FStar_Parser_AST.Product (binders, body) ->
          let uu___1 =
            FStar_List.fold_left
              (fun uu___2 ->
                 fun binder ->
                   match uu___2 with
                   | (env1, free) ->
                       let uu___3 = free_type_vars_b env1 binder in
                       (match uu___3 with
                        | (env2, f) -> (env2, (FStar_List.append f free))))
              (env, []) binders in
          (match uu___1 with
           | (env1, free) ->
               let uu___2 = free_type_vars env1 body in
               FStar_List.append free uu___2)
      | FStar_Parser_AST.Project (t1, uu___1) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.CalcProof (rel, init, steps) ->
          let uu___1 = free_type_vars env rel in
          let uu___2 =
            let uu___3 = free_type_vars env init in
            let uu___4 =
              FStar_List.collect
                (fun uu___5 ->
                   match uu___5 with
                   | FStar_Parser_AST.CalcStep (rel1, just, next) ->
                       let uu___6 = free_type_vars env rel1 in
                       let uu___7 =
                         let uu___8 = free_type_vars env just in
                         let uu___9 = free_type_vars env next in
                         FStar_List.append uu___8 uu___9 in
                       FStar_List.append uu___6 uu___7) steps in
            FStar_List.append uu___3 uu___4 in
          FStar_List.append uu___1 uu___2
      | FStar_Parser_AST.Abs uu___1 -> []
      | FStar_Parser_AST.Let uu___1 -> []
      | FStar_Parser_AST.LetOpen uu___1 -> []
      | FStar_Parser_AST.If uu___1 -> []
      | FStar_Parser_AST.QForall uu___1 -> []
      | FStar_Parser_AST.QExists uu___1 -> []
      | FStar_Parser_AST.Record uu___1 -> []
      | FStar_Parser_AST.Match uu___1 -> []
      | FStar_Parser_AST.TryWith uu___1 -> []
      | FStar_Parser_AST.Bind uu___1 -> []
      | FStar_Parser_AST.Quote uu___1 -> []
      | FStar_Parser_AST.VQuote uu___1 -> []
      | FStar_Parser_AST.Antiquote uu___1 -> []
      | FStar_Parser_AST.Seq uu___1 -> []
let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun t ->
    let rec aux args t1 =
      let uu___ = let uu___1 = unparen t1 in uu___1.FStar_Parser_AST.tm in
      match uu___ with
      | FStar_Parser_AST.App (t2, arg, imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l, args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu___1 -> (t1, args) in
    aux [] t
let (close :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env ->
    fun t ->
      let ftv =
        let uu___ = free_type_vars env t in
        FStar_All.pipe_left sort_ftv uu___ in
      if (FStar_List.length ftv) = Prims.int_zero
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x ->
                   let uu___1 =
                     let uu___2 =
                       let uu___3 =
                         let uu___4 = FStar_Ident.range_of_id x in
                         tm_type uu___4 in
                       (x, uu___3) in
                     FStar_Parser_AST.TAnnotated uu___2 in
                   let uu___2 = FStar_Ident.range_of_id x in
                   FStar_Parser_AST.mk_binder uu___1 uu___2
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
        let uu___ = free_type_vars env t in
        FStar_All.pipe_left sort_ftv uu___ in
      if (FStar_List.length ftv) = Prims.int_zero
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x ->
                   let uu___1 =
                     let uu___2 =
                       let uu___3 =
                         let uu___4 = FStar_Ident.range_of_id x in
                         tm_type uu___4 in
                       (x, uu___3) in
                     FStar_Parser_AST.TAnnotated uu___2 in
                   let uu___2 = FStar_Ident.range_of_id x in
                   FStar_Parser_AST.mk_binder uu___1 uu___2
                     FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit))) in
         let t1 =
           let uu___1 = let uu___2 = unparen t in uu___2.FStar_Parser_AST.tm in
           match uu___1 with
           | FStar_Parser_AST.Product uu___2 -> t
           | uu___2 ->
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
      | uu___ -> (bs, t)
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild uu___ -> true
    | FStar_Parser_AST.PatTvar uu___ -> true
    | FStar_Parser_AST.PatVar uu___ -> true
    | FStar_Parser_AST.PatAscribed (p1, uu___) -> is_var_pattern p1
    | uu___ -> false
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1, uu___) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu___;
           FStar_Parser_AST.prange = uu___1;_},
         uu___2)
        -> true
    | uu___ -> false
let (replace_unit_pattern :
  FStar_Parser_AST.pattern -> FStar_Parser_AST.pattern) =
  fun p ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatConst (FStar_Const.Const_unit) ->
        FStar_Parser_AST.mk_pattern
          (FStar_Parser_AST.PatAscribed
             ((FStar_Parser_AST.mk_pattern
                 (FStar_Parser_AST.PatWild (FStar_Pervasives_Native.None, []))
                 p.FStar_Parser_AST.prange),
               ((unit_ty p.FStar_Parser_AST.prange),
                 FStar_Pervasives_Native.None))) p.FStar_Parser_AST.prange
    | uu___ -> p
let rec (destruct_app_pattern :
  env_t ->
    Prims.bool ->
      FStar_Parser_AST.pattern ->
        ((FStar_Ident.ident, FStar_Ident.lid) FStar_Pervasives.either *
          FStar_Parser_AST.pattern Prims.list * (FStar_Parser_AST.term *
          FStar_Parser_AST.term FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.option))
  =
  fun env ->
    fun is_top_level ->
      fun p ->
        match p.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatAscribed (p1, t) ->
            let uu___ = destruct_app_pattern env is_top_level p1 in
            (match uu___ with
             | (name, args, uu___1) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id, uu___, uu___1);
               FStar_Parser_AST.prange = uu___2;_},
             args)
            when is_top_level ->
            let uu___3 =
              let uu___4 = FStar_Syntax_DsEnv.qualify env id in
              FStar_Pervasives.Inr uu___4 in
            (uu___3, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id, uu___, uu___1);
               FStar_Parser_AST.prange = uu___2;_},
             args)
            ->
            ((FStar_Pervasives.Inl id), args, FStar_Pervasives_Native.None)
        | uu___ -> failwith "Not an app pattern"
let rec (gather_pattern_bound_vars_maybe_top :
  FStar_Ident.ident FStar_Util.set ->
    FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set)
  =
  fun acc ->
    fun p ->
      let gather_pattern_bound_vars_from_list =
        FStar_List.fold_left gather_pattern_bound_vars_maybe_top acc in
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatWild uu___ -> acc
      | FStar_Parser_AST.PatConst uu___ -> acc
      | FStar_Parser_AST.PatName uu___ -> acc
      | FStar_Parser_AST.PatOp uu___ -> acc
      | FStar_Parser_AST.PatApp (phead, pats) ->
          gather_pattern_bound_vars_from_list (phead :: pats)
      | FStar_Parser_AST.PatTvar (x, uu___, uu___1) ->
          FStar_Util.set_add x acc
      | FStar_Parser_AST.PatVar (x, uu___, uu___1) ->
          FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatTuple (pats, uu___) ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu___ = FStar_List.map FStar_Pervasives_Native.snd guarded_pats in
          gather_pattern_bound_vars_from_list uu___
      | FStar_Parser_AST.PatAscribed (pat, uu___) ->
          gather_pattern_bound_vars_maybe_top acc pat
let (gather_pattern_bound_vars :
  FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set) =
  let acc =
    FStar_Util.new_set
      (fun id1 ->
         fun id2 ->
           let uu___ =
             let uu___1 = FStar_Ident.string_of_id id1 in
             let uu___2 = FStar_Ident.string_of_id id2 in uu___1 = uu___2 in
           if uu___ then Prims.int_zero else Prims.int_one) in
  fun p -> gather_pattern_bound_vars_maybe_top acc p
type bnd =
  | LocalBinder of (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual *
  FStar_Syntax_Syntax.term Prims.list) 
  | LetBinder of (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)) 
let (uu___is_LocalBinder : bnd -> Prims.bool) =
  fun projectee ->
    match projectee with | LocalBinder _0 -> true | uu___ -> false
let (__proj__LocalBinder__item___0 :
  bnd ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual *
      FStar_Syntax_Syntax.term Prims.list))
  = fun projectee -> match projectee with | LocalBinder _0 -> _0
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee ->
    match projectee with | LetBinder _0 -> true | uu___ -> false
let (__proj__LetBinder__item___0 :
  bnd ->
    (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)))
  = fun projectee -> match projectee with | LetBinder _0 -> _0
let (is_implicit : bnd -> Prims.bool) =
  fun b ->
    match b with
    | LocalBinder
        (uu___, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
         uu___1), uu___2)
        -> true
    | uu___ -> false
let (binder_of_bnd :
  bnd ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual *
      FStar_Syntax_Syntax.term Prims.list))
  =
  fun uu___ ->
    match uu___ with
    | LocalBinder (a, aq, attrs) -> (a, aq, attrs)
    | uu___1 -> failwith "Impossible"
let (mk_lb :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list *
    (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Pervasives.either
    * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Range.range)
    -> FStar_Syntax_Syntax.letbinding)
  =
  fun uu___ ->
    match uu___ with
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
      let uu___ =
        let uu___1 =
          let uu___2 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
          FStar_Syntax_Syntax.fv_to_tm uu___2 in
        let uu___2 =
          let uu___3 =
            let uu___4 = FStar_Syntax_Syntax.as_implicit false in
            (tm, uu___4) in
          [uu___3] in
        (uu___1, uu___2) in
      FStar_Syntax_Syntax.Tm_app uu___ in
    FStar_Syntax_Syntax.mk tm' tm.FStar_Syntax_Syntax.pos
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm ->
    let tm' =
      let uu___ =
        let uu___1 =
          let uu___2 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
          FStar_Syntax_Syntax.fv_to_tm uu___2 in
        let uu___2 =
          let uu___3 =
            let uu___4 = FStar_Syntax_Syntax.as_implicit false in
            (tm, uu___4) in
          [uu___3] in
        (uu___1, uu___2) in
      FStar_Syntax_Syntax.Tm_app uu___ in
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
          let uu___ =
            let uu___1 =
              let uu___2 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Syntax_Syntax.fv_to_tm uu___2 in
            let uu___2 =
              let uu___3 =
                let uu___4 = FStar_Syntax_Syntax.as_implicit false in
                (t1, uu___4) in
              let uu___4 =
                let uu___5 =
                  let uu___6 = FStar_Syntax_Syntax.as_implicit false in
                  (t2, uu___6) in
                [uu___5] in
              uu___3 :: uu___4 in
            (uu___1, uu___2) in
          FStar_Syntax_Syntax.Tm_app uu___ in
        FStar_Syntax_Syntax.mk tm pos
let rec (generalize_annotated_univs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun s ->
    let bs_univnames bs =
      let uu___ =
        let uu___1 = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name in
        FStar_List.fold_left
          (fun uvs ->
             fun b ->
               let uu___2 =
                 FStar_Syntax_Free.univnames
                   (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
               FStar_Util.set_union uvs uu___2) uu___1 in
      FStar_All.pipe_right bs uu___ in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu___ ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu___ ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs, lids) ->
        let uvs =
          let uu___ =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs1 ->
                    fun se ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu___1, uu___2, bs, t, uu___3, uu___4) ->
                            let uu___5 = bs_univnames bs in
                            let uu___6 = FStar_Syntax_Free.univnames t in
                            FStar_Util.set_union uu___5 uu___6
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu___1, uu___2, t, uu___3, uu___4, uu___5) ->
                            FStar_Syntax_Free.univnames t
                        | uu___1 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt" in
                      FStar_Util.set_union uvs1 se_univs) empty_set) in
          FStar_All.pipe_right uu___ FStar_Util.set_elements in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs in
        let uu___ = s in
        let uu___1 =
          let uu___2 =
            let uu___3 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid, uu___4, bs, t, lids1, lids2) ->
                          let uu___5 = se in
                          let uu___6 =
                            let uu___7 =
                              let uu___8 =
                                FStar_Syntax_Subst.subst_binders usubst bs in
                              let uu___9 =
                                let uu___10 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst in
                                FStar_Syntax_Subst.subst uu___10 t in
                              (lid, uvs, uu___8, uu___9, lids1, lids2) in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu___7 in
                          {
                            FStar_Syntax_Syntax.sigel = uu___6;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___5.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___5.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___5.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___5.FStar_Syntax_Syntax.sigattrs);
                            FStar_Syntax_Syntax.sigopts =
                              (uu___5.FStar_Syntax_Syntax.sigopts)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid, uu___4, t, tlid, n, lids1) ->
                          let uu___5 = se in
                          let uu___6 =
                            let uu___7 =
                              let uu___8 = FStar_Syntax_Subst.subst usubst t in
                              (lid, uvs, uu___8, tlid, n, lids1) in
                            FStar_Syntax_Syntax.Sig_datacon uu___7 in
                          {
                            FStar_Syntax_Syntax.sigel = uu___6;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___5.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___5.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___5.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___5.FStar_Syntax_Syntax.sigattrs);
                            FStar_Syntax_Syntax.sigopts =
                              (uu___5.FStar_Syntax_Syntax.sigopts)
                          }
                      | uu___4 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt")) in
            (uu___3, lids) in
          FStar_Syntax_Syntax.Sig_bundle uu___2 in
        {
          FStar_Syntax_Syntax.sigel = uu___1;
          FStar_Syntax_Syntax.sigrng = (uu___.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals = (uu___.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta = (uu___.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs = (uu___.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts = (uu___.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid, uu___, t) ->
        let uvs =
          let uu___1 = FStar_Syntax_Free.univnames t in
          FStar_All.pipe_right uu___1 FStar_Util.set_elements in
        let uu___1 = s in
        let uu___2 =
          let uu___3 =
            let uu___4 = FStar_Syntax_Subst.close_univ_vars uvs t in
            (lid, uvs, uu___4) in
          FStar_Syntax_Syntax.Sig_declare_typ uu___3 in
        {
          FStar_Syntax_Syntax.sigel = uu___2;
          FStar_Syntax_Syntax.sigrng = (uu___1.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta = (uu___1.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts = (uu___1.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_let ((b, lbs), lids) ->
        let lb_univnames lb =
          let uu___ =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp in
          let uu___1 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs, e, uu___2) ->
                let uvs1 = bs_univnames bs in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu___3, (FStar_Pervasives.Inl t, uu___4), uu___5) ->
                      FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu___3, (FStar_Pervasives.Inr c, uu___4), uu___5) ->
                      FStar_Syntax_Free.univnames_comp c
                  | uu___3 -> empty_set in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_arrow (bs, uu___2) -> bs_univnames bs
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu___2, (FStar_Pervasives.Inl t, uu___3), uu___4) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu___2, (FStar_Pervasives.Inr c, uu___3), uu___4) ->
                FStar_Syntax_Free.univnames_comp c
            | uu___2 -> empty_set in
          FStar_Util.set_union uu___ uu___1 in
        let all_lb_univs =
          let uu___ =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs ->
                    fun lb ->
                      let uu___1 = lb_univnames lb in
                      FStar_Util.set_union uvs uu___1) empty_set) in
          FStar_All.pipe_right uu___ FStar_Util.set_elements in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs in
        let uu___ = s in
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb ->
                        let uu___5 = lb in
                        let uu___6 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp in
                        let uu___7 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___5.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu___6;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___5.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu___7;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___5.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___5.FStar_Syntax_Syntax.lbpos)
                        })) in
              (b, uu___4) in
            (uu___3, lids) in
          FStar_Syntax_Syntax.Sig_let uu___2 in
        {
          FStar_Syntax_Syntax.sigel = uu___1;
          FStar_Syntax_Syntax.sigrng = (uu___.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals = (uu___.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta = (uu___.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs = (uu___.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts = (uu___.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid, uu___, fml) ->
        let uvs =
          let uu___1 = FStar_Syntax_Free.univnames fml in
          FStar_All.pipe_right uu___1 FStar_Util.set_elements in
        let uu___1 = s in
        let uu___2 =
          let uu___3 =
            let uu___4 = FStar_Syntax_Subst.close_univ_vars uvs fml in
            (lid, uvs, uu___4) in
          FStar_Syntax_Syntax.Sig_assume uu___3 in
        {
          FStar_Syntax_Syntax.sigel = uu___2;
          FStar_Syntax_Syntax.sigrng = (uu___1.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta = (uu___1.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts = (uu___1.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uu___, bs, c, flags) ->
        let uvs =
          let uu___1 =
            let uu___2 = bs_univnames bs in
            let uu___3 = FStar_Syntax_Free.univnames_comp c in
            FStar_Util.set_union uu___2 uu___3 in
          FStar_All.pipe_right uu___1 FStar_Util.set_elements in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs in
        let uu___1 = s in
        let uu___2 =
          let uu___3 =
            let uu___4 = FStar_Syntax_Subst.subst_binders usubst bs in
            let uu___5 = FStar_Syntax_Subst.subst_comp usubst c in
            (lid, uvs, uu___4, uu___5, flags) in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu___3 in
        {
          FStar_Syntax_Syntax.sigel = uu___2;
          FStar_Syntax_Syntax.sigrng = (uu___1.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___1.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta = (uu___1.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___1.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts = (uu___1.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_fail (errs, lax, ses) ->
        let uu___ = s in
        let uu___1 =
          let uu___2 =
            let uu___3 = FStar_List.map generalize_annotated_univs ses in
            (errs, lax, uu___3) in
          FStar_Syntax_Syntax.Sig_fail uu___2 in
        {
          FStar_Syntax_Syntax.sigel = uu___1;
          FStar_Syntax_Syntax.sigrng = (uu___.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals = (uu___.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta = (uu___.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs = (uu___.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts = (uu___.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_new_effect uu___ -> s
    | FStar_Syntax_Syntax.Sig_sub_effect uu___ -> s
    | FStar_Syntax_Syntax.Sig_polymonadic_bind uu___ -> s
    | FStar_Syntax_Syntax.Sig_polymonadic_subcomp uu___ -> s
    | FStar_Syntax_Syntax.Sig_splice uu___ -> s
    | FStar_Syntax_Syntax.Sig_pragma uu___ -> s
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___ ->
    match uu___ with
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
    | uu___1 -> false
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u ->
    fun n ->
      if n = Prims.int_zero
      then u
      else
        (let uu___1 = sum_to_universe u (n - Prims.int_one) in
         FStar_Syntax_Syntax.U_succ uu___1)
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n -> sum_to_universe FStar_Syntax_Syntax.U_zero n
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int, FStar_Syntax_Syntax.universe) FStar_Pervasives.either)
  =
  fun t ->
    let uu___ = let uu___1 = unparen t in uu___1.FStar_Parser_AST.tm in
    match uu___ with
    | FStar_Parser_AST.Wild ->
        FStar_Pervasives.Inr FStar_Syntax_Syntax.U_unknown
    | FStar_Parser_AST.Uvar u ->
        FStar_Pervasives.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr, uu___1)) ->
        let n = FStar_Util.int_of_string repr in
        (if n < Prims.int_zero
         then
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_NegativeUniverseConstFatal_NotSupported,
               (Prims.op_Hat
                  "Negative universe constant  are not supported : " repr))
             t.FStar_Parser_AST.range
         else ();
         FStar_Pervasives.Inl n)
    | FStar_Parser_AST.Op (op_plus, t1::t2::[]) ->
        let u1 = desugar_maybe_non_constant_universe t1 in
        let u2 = desugar_maybe_non_constant_universe t2 in
        (match (u1, u2) with
         | (FStar_Pervasives.Inl n1, FStar_Pervasives.Inl n2) ->
             FStar_Pervasives.Inl (n1 + n2)
         | (FStar_Pervasives.Inl n, FStar_Pervasives.Inr u) ->
             let uu___2 = sum_to_universe u n in FStar_Pervasives.Inr uu___2
         | (FStar_Pervasives.Inr u, FStar_Pervasives.Inl n) ->
             let uu___2 = sum_to_universe u n in FStar_Pervasives.Inr uu___2
         | (FStar_Pervasives.Inr u11, FStar_Pervasives.Inr u21) ->
             let uu___2 =
               let uu___3 =
                 let uu___4 = FStar_Parser_AST.term_to_string t in
                 Prims.op_Hat
                   "This universe might contain a sum of two universe variables "
                   uu___4 in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu___3) in
             FStar_Errors.raise_error uu___2 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu___1 ->
        let rec aux t1 univargs =
          let uu___2 = let uu___3 = unparen t1 in uu___3.FStar_Parser_AST.tm in
          match uu___2 with
          | FStar_Parser_AST.App (t2, targ, uu___3) ->
              let uarg = desugar_maybe_non_constant_universe targ in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid ->
              if
                FStar_List.existsb
                  (fun uu___4 ->
                     match uu___4 with
                     | FStar_Pervasives.Inr uu___5 -> true
                     | uu___5 -> false) univargs
              then
                let uu___4 =
                  let uu___5 =
                    FStar_List.map
                      (fun uu___6 ->
                         match uu___6 with
                         | FStar_Pervasives.Inl n -> int_to_universe n
                         | FStar_Pervasives.Inr u -> u) univargs in
                  FStar_Syntax_Syntax.U_max uu___5 in
                FStar_Pervasives.Inr uu___4
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___5 ->
                        match uu___5 with
                        | FStar_Pervasives.Inl n -> n
                        | FStar_Pervasives.Inr uu___6 ->
                            failwith "impossible") univargs in
                 let uu___5 =
                   FStar_List.fold_left
                     (fun m -> fun n -> if m > n then m else n)
                     Prims.int_zero nargs in
                 FStar_Pervasives.Inl uu___5)
          | uu___3 ->
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    let uu___7 = FStar_Parser_AST.term_to_string t1 in
                    Prims.op_Hat uu___7 " in universe context" in
                  Prims.op_Hat "Unexpected term " uu___6 in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu___5) in
              FStar_Errors.raise_error uu___4 t1.FStar_Parser_AST.range in
        aux t []
    | uu___1 ->
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 = FStar_Parser_AST.term_to_string t in
              Prims.op_Hat uu___5 " in universe context" in
            Prims.op_Hat "Unexpected term " uu___4 in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu___3) in
        FStar_Errors.raise_error uu___2 t.FStar_Parser_AST.range
let (desugar_universe :
  FStar_Parser_AST.term -> FStar_Syntax_Syntax.universe) =
  fun t ->
    let u = desugar_maybe_non_constant_universe t in
    match u with
    | FStar_Pervasives.Inl n -> int_to_universe n
    | FStar_Pervasives.Inr u1 -> u1
let (check_no_aq : FStar_Syntax_Syntax.antiquotations -> unit) =
  fun aq ->
    match aq with
    | [] -> ()
    | (bv,
       {
         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_quoted
           (e,
            { FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
              FStar_Syntax_Syntax.antiquotes = uu___;_});
         FStar_Syntax_Syntax.pos = uu___1;
         FStar_Syntax_Syntax.vars = uu___2;_})::uu___3
        ->
        let uu___4 =
          let uu___5 =
            let uu___6 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu___6 in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu___5) in
        FStar_Errors.raise_error uu___4 e.FStar_Syntax_Syntax.pos
    | (bv, e)::uu___ ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu___3 in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu___2) in
        FStar_Errors.raise_error uu___1 e.FStar_Syntax_Syntax.pos
let check_fields :
  'uuuuu .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident * 'uuuuu) Prims.list ->
        FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env ->
    fun fields ->
      fun rg ->
        let uu___ = FStar_List.hd fields in
        match uu___ with
        | (f, uu___1) ->
            let record =
              FStar_Syntax_DsEnv.fail_or env
                (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f in
            let check_field uu___2 =
              match uu___2 with
              | (f', uu___3) ->
                  let uu___4 =
                    FStar_Syntax_DsEnv.belongs_to_record env f' record in
                  if uu___4
                  then ()
                  else
                    (let msg =
                       let uu___6 = FStar_Ident.string_of_lid f in
                       let uu___7 =
                         FStar_Ident.string_of_lid
                           record.FStar_Syntax_DsEnv.typename in
                       let uu___8 = FStar_Ident.string_of_lid f' in
                       FStar_Util.format3
                         "Field %s belongs to record type %s, whereas field %s does not"
                         uu___6 uu___7 uu___8 in
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FieldsNotBelongToSameRecordType,
                         msg) rg) in
            ((let uu___3 = FStar_List.tl fields in
              FStar_List.iter check_field uu___3);
             (match () with | () -> record))
let (check_linear_pattern_variables :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t Prims.list ->
    FStar_Range.range -> unit)
  =
  fun pats ->
    fun r ->
      let rec pat_vars p =
        match p.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_dot_term uu___ ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_wild uu___ -> FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_constant uu___ ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_var x ->
            FStar_Util.set_add x FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_cons (uu___, pats1) ->
            let aux out uu___1 =
              match uu___1 with
              | (p1, uu___2) ->
                  let p_vars = pat_vars p1 in
                  let intersection = FStar_Util.set_intersect p_vars out in
                  let uu___3 = FStar_Util.set_is_empty intersection in
                  if uu___3
                  then FStar_Util.set_union out p_vars
                  else
                    (let duplicate_bv =
                       let uu___5 = FStar_Util.set_elements intersection in
                       FStar_List.hd uu___5 in
                     let uu___5 =
                       let uu___6 =
                         let uu___7 =
                           FStar_Ident.string_of_id
                             duplicate_bv.FStar_Syntax_Syntax.ppname in
                         FStar_Util.format1
                           "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                           uu___7 in
                       (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                         uu___6) in
                     FStar_Errors.raise_error uu___5 r) in
            FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1 in
      match pats with
      | [] -> ()
      | p::[] ->
          let uu___ = pat_vars p in
          FStar_All.pipe_right uu___ (fun uu___1 -> ())
      | p::ps ->
          let pvars = pat_vars p in
          let aux p1 =
            let uu___ =
              let uu___1 = pat_vars p1 in FStar_Util.set_eq pvars uu___1 in
            if uu___
            then ()
            else
              (let nonlinear_vars =
                 let uu___2 = pat_vars p1 in
                 FStar_Util.set_symmetric_difference pvars uu___2 in
               let first_nonlinear_var =
                 let uu___2 = FStar_Util.set_elements nonlinear_vars in
                 FStar_List.hd uu___2 in
               let uu___2 =
                 let uu___3 =
                   let uu___4 =
                     FStar_Ident.string_of_id
                       first_nonlinear_var.FStar_Syntax_Syntax.ppname in
                   FStar_Util.format1
                     "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                     uu___4 in
                 (FStar_Errors.Fatal_IncoherentPatterns, uu___3) in
               FStar_Errors.raise_error uu___2 r) in
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
          let uu___ =
            FStar_Util.find_opt
              (fun y ->
                 let uu___1 =
                   FStar_Ident.string_of_id y.FStar_Syntax_Syntax.ppname in
                 let uu___2 = FStar_Ident.string_of_id x in uu___1 = uu___2)
              l in
          match uu___ with
          | FStar_Pervasives_Native.Some y -> (l, e, y)
          | uu___1 ->
              let uu___2 = FStar_Syntax_DsEnv.push_bv e x in
              (match uu___2 with | (e1, xbv) -> ((xbv :: l), e1, xbv)) in
        let rec aux' top loc env1 p1 =
          let pos q =
            FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange in
          let pos_r r q = FStar_Syntax_Syntax.withinfo q r in
          let orig = p1 in
          match p1.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOr uu___ ->
              failwith "impossible: PatOr handled below"
          | FStar_Parser_AST.PatOp op ->
              let id_op =
                let uu___ =
                  let uu___1 =
                    let uu___2 = FStar_Ident.string_of_id op in
                    let uu___3 = FStar_Ident.range_of_id op in
                    FStar_Parser_AST.compile_op Prims.int_zero uu___2 uu___3 in
                  let uu___2 = FStar_Ident.range_of_id op in (uu___1, uu___2) in
                FStar_Ident.mk_ident uu___ in
              let p2 =
                let uu___ = p1 in
                {
                  FStar_Parser_AST.pat =
                    (FStar_Parser_AST.PatVar
                       (id_op, FStar_Pervasives_Native.None, []));
                  FStar_Parser_AST.prange = (uu___.FStar_Parser_AST.prange)
                } in
              aux loc env1 p2
          | FStar_Parser_AST.PatAscribed (p2, (t, tacopt)) ->
              ((match tacopt with
                | FStar_Pervasives_Native.None -> ()
                | FStar_Pervasives_Native.Some uu___1 ->
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                        "Type ascriptions within patterns cannot be associated with a tactic")
                      orig.FStar_Parser_AST.prange);
               (let uu___1 = aux loc env1 p2 in
                match uu___1 with
                | (loc1, env', binder, p3, annots) ->
                    let uu___2 =
                      match binder with
                      | LetBinder uu___3 -> failwith "impossible"
                      | LocalBinder (x, aq, attrs) ->
                          let t1 =
                            let uu___3 = close_fun env1 t in
                            desugar_term env1 uu___3 in
                          let x1 =
                            let uu___3 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___3.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___3.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            } in
                          ([(x1, t1, attrs)], (LocalBinder (x1, aq, attrs))) in
                    (match uu___2 with
                     | (annots', binder1) ->
                         ((match p3.FStar_Syntax_Syntax.v with
                           | FStar_Syntax_Syntax.Pat_var uu___4 -> ()
                           | FStar_Syntax_Syntax.Pat_wild uu___4 -> ()
                           | uu___4 when top && top_level_ascr_allowed -> ()
                           | uu___4 ->
                               FStar_Errors.raise_error
                                 (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                                   "Type ascriptions within patterns are only allowed on variables")
                                 orig.FStar_Parser_AST.prange);
                          (loc1, env', binder1, p3,
                            (FStar_List.append annots' annots))))))
          | FStar_Parser_AST.PatWild (aq, attrs) ->
              let aq1 = trans_aqual env1 aq in
              let attrs1 =
                FStar_All.pipe_right attrs
                  (FStar_List.map (desugar_term env1)) in
              let x =
                let uu___ = tun_r p1.FStar_Parser_AST.prange in
                FStar_Syntax_Syntax.new_bv
                  (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                  uu___ in
              let uu___ =
                FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x) in
              (loc, env1, (LocalBinder (x, aq1, attrs1)), uu___, [])
          | FStar_Parser_AST.PatConst c ->
              let x =
                let uu___ = tun_r p1.FStar_Parser_AST.prange in
                FStar_Syntax_Syntax.new_bv
                  (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                  uu___ in
              let uu___ =
                FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c) in
              (loc, env1,
                (LocalBinder (x, FStar_Pervasives_Native.None, [])), uu___,
                [])
          | FStar_Parser_AST.PatTvar (x, aq, attrs) ->
              let aq1 = trans_aqual env1 aq in
              let attrs1 =
                FStar_All.pipe_right attrs
                  (FStar_List.map (desugar_term env1)) in
              let uu___ = resolvex loc env1 x in
              (match uu___ with
               | (loc1, env2, xbv) ->
                   let uu___1 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_var xbv) in
                   (loc1, env2, (LocalBinder (xbv, aq1, attrs1)), uu___1, []))
          | FStar_Parser_AST.PatVar (x, aq, attrs) ->
              let aq1 = trans_aqual env1 aq in
              let attrs1 =
                FStar_All.pipe_right attrs
                  (FStar_List.map (desugar_term env1)) in
              let uu___ = resolvex loc env1 x in
              (match uu___ with
               | (loc1, env2, xbv) ->
                   let uu___1 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_var xbv) in
                   (loc1, env2, (LocalBinder (xbv, aq1, attrs1)), uu___1, []))
          | FStar_Parser_AST.PatName l ->
              let l1 =
                FStar_Syntax_DsEnv.fail_or env1
                  (FStar_Syntax_DsEnv.try_lookup_datacon env1) l in
              let x =
                let uu___ = tun_r p1.FStar_Parser_AST.prange in
                FStar_Syntax_Syntax.new_bv
                  (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                  uu___ in
              let uu___ =
                FStar_All.pipe_left pos
                  (FStar_Syntax_Syntax.Pat_cons (l1, [])) in
              (loc, env1,
                (LocalBinder (x, FStar_Pervasives_Native.None, [])), uu___,
                [])
          | FStar_Parser_AST.PatApp
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                 FStar_Parser_AST.prange = uu___;_},
               args)
              ->
              let uu___1 =
                FStar_List.fold_right
                  (fun arg ->
                     fun uu___2 ->
                       match uu___2 with
                       | (loc1, env2, annots, args1) ->
                           let uu___3 = aux loc1 env2 arg in
                           (match uu___3 with
                            | (loc2, env3, b, arg1, ans) ->
                                let imp = is_implicit b in
                                (loc2, env3, (FStar_List.append ans annots),
                                  ((arg1, imp) :: args1)))) args
                  (loc, env1, [], []) in
              (match uu___1 with
               | (loc1, env2, annots, args1) ->
                   let l1 =
                     FStar_Syntax_DsEnv.fail_or env2
                       (FStar_Syntax_DsEnv.try_lookup_datacon env2) l in
                   let x =
                     let uu___2 = tun_r p1.FStar_Parser_AST.prange in
                     FStar_Syntax_Syntax.new_bv
                       (FStar_Pervasives_Native.Some
                          (p1.FStar_Parser_AST.prange)) uu___2 in
                   let uu___2 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_cons (l1, args1)) in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None, [])),
                     uu___2, annots))
          | FStar_Parser_AST.PatApp uu___ ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                p1.FStar_Parser_AST.prange
          | FStar_Parser_AST.PatList pats ->
              let uu___ =
                FStar_List.fold_right
                  (fun pat ->
                     fun uu___1 ->
                       match uu___1 with
                       | (loc1, env2, annots, pats1) ->
                           let uu___2 = aux loc1 env2 pat in
                           (match uu___2 with
                            | (loc2, env3, uu___3, pat1, ans) ->
                                (loc2, env3, (FStar_List.append ans annots),
                                  (pat1 :: pats1)))) pats (loc, env1, [], []) in
              (match uu___ with
               | (loc1, env2, annots, pats1) ->
                   let pat =
                     let uu___1 =
                       let uu___2 =
                         let uu___3 =
                           FStar_Range.end_range p1.FStar_Parser_AST.prange in
                         pos_r uu___3 in
                       let uu___3 =
                         let uu___4 =
                           let uu___5 =
                             FStar_Syntax_Syntax.lid_as_fv
                               FStar_Parser_Const.nil_lid
                               FStar_Syntax_Syntax.delta_constant
                               (FStar_Pervasives_Native.Some
                                  FStar_Syntax_Syntax.Data_ctor) in
                           (uu___5, []) in
                         FStar_Syntax_Syntax.Pat_cons uu___4 in
                       FStar_All.pipe_left uu___2 uu___3 in
                     FStar_List.fold_right
                       (fun hd ->
                          fun tl ->
                            let r =
                              FStar_Range.union_ranges
                                hd.FStar_Syntax_Syntax.p
                                tl.FStar_Syntax_Syntax.p in
                            let uu___2 =
                              let uu___3 =
                                let uu___4 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.cons_lid
                                    FStar_Syntax_Syntax.delta_constant
                                    (FStar_Pervasives_Native.Some
                                       FStar_Syntax_Syntax.Data_ctor) in
                                (uu___4, [(hd, false); (tl, false)]) in
                              FStar_Syntax_Syntax.Pat_cons uu___3 in
                            FStar_All.pipe_left (pos_r r) uu___2) pats1
                       uu___1 in
                   let x =
                     let uu___1 = tun_r p1.FStar_Parser_AST.prange in
                     FStar_Syntax_Syntax.new_bv
                       (FStar_Pervasives_Native.Some
                          (p1.FStar_Parser_AST.prange)) uu___1 in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None, [])),
                     pat, annots))
          | FStar_Parser_AST.PatTuple (args, dep) ->
              let uu___ =
                FStar_List.fold_left
                  (fun uu___1 ->
                     fun p2 ->
                       match uu___1 with
                       | (loc1, env2, annots, pats) ->
                           let uu___2 = aux loc1 env2 p2 in
                           (match uu___2 with
                            | (loc2, env3, uu___3, pat, ans) ->
                                (loc2, env3, (FStar_List.append ans annots),
                                  ((pat, false) :: pats))))
                  (loc, env1, [], []) args in
              (match uu___ with
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
                     | uu___1 -> failwith "impossible" in
                   let x =
                     let uu___1 = tun_r p1.FStar_Parser_AST.prange in
                     FStar_Syntax_Syntax.new_bv
                       (FStar_Pervasives_Native.Some
                          (p1.FStar_Parser_AST.prange)) uu___1 in
                   let uu___1 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_cons (l1, args2)) in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None, [])),
                     uu___1, annots))
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
                     (fun uu___ ->
                        match uu___ with
                        | (f, p2) ->
                            let uu___1 = FStar_Ident.ident_of_lid f in
                            (uu___1, p2))) in
              let args =
                FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                  (FStar_List.map
                     (fun uu___ ->
                        match uu___ with
                        | (f, uu___1) ->
                            let uu___2 =
                              FStar_All.pipe_right fields1
                                (FStar_List.tryFind
                                   (fun uu___3 ->
                                      match uu___3 with
                                      | (g, uu___4) ->
                                          let uu___5 =
                                            FStar_Ident.string_of_id f in
                                          let uu___6 =
                                            FStar_Ident.string_of_id g in
                                          uu___5 = uu___6)) in
                            (match uu___2 with
                             | FStar_Pervasives_Native.None ->
                                 FStar_Parser_AST.mk_pattern
                                   (FStar_Parser_AST.PatWild
                                      (FStar_Pervasives_Native.None, []))
                                   p1.FStar_Parser_AST.prange
                             | FStar_Pervasives_Native.Some (uu___3, p2) ->
                                 p2))) in
              let app =
                let uu___ =
                  let uu___1 =
                    let uu___2 =
                      let uu___3 =
                        let uu___4 =
                          let uu___5 =
                            let uu___6 =
                              FStar_Ident.ns_of_lid
                                record.FStar_Syntax_DsEnv.typename in
                            FStar_List.append uu___6
                              [record.FStar_Syntax_DsEnv.constrname] in
                          FStar_Ident.lid_of_ids uu___5 in
                        FStar_Parser_AST.PatName uu___4 in
                      FStar_Parser_AST.mk_pattern uu___3
                        p1.FStar_Parser_AST.prange in
                    (uu___2, args) in
                  FStar_Parser_AST.PatApp uu___1 in
                FStar_Parser_AST.mk_pattern uu___ p1.FStar_Parser_AST.prange in
              let uu___ = aux loc env1 app in
              (match uu___ with
               | (env2, e, b, p2, annots) ->
                   let p3 =
                     match p2.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_cons (fv, args1) ->
                         let uu___1 =
                           let uu___2 =
                             let uu___3 =
                               let uu___4 = fv in
                               let uu___5 =
                                 let uu___6 =
                                   let uu___7 =
                                     let uu___8 =
                                       FStar_All.pipe_right
                                         record.FStar_Syntax_DsEnv.fields
                                         (FStar_List.map
                                            FStar_Pervasives_Native.fst) in
                                     ((record.FStar_Syntax_DsEnv.typename),
                                       uu___8) in
                                   FStar_Syntax_Syntax.Record_ctor uu___7 in
                                 FStar_Pervasives_Native.Some uu___6 in
                               {
                                 FStar_Syntax_Syntax.fv_name =
                                   (uu___4.FStar_Syntax_Syntax.fv_name);
                                 FStar_Syntax_Syntax.fv_delta =
                                   (uu___4.FStar_Syntax_Syntax.fv_delta);
                                 FStar_Syntax_Syntax.fv_qual = uu___5
                               } in
                             (uu___3, args1) in
                           FStar_Syntax_Syntax.Pat_cons uu___2 in
                         FStar_All.pipe_left pos uu___1
                     | uu___1 -> p2 in
                   (env2, e, b, p3, annots))
        and aux loc env1 p1 = aux' false loc env1 p1 in
        let aux_maybe_or env1 p1 =
          let loc = [] in
          match p1.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOr [] -> failwith "impossible"
          | FStar_Parser_AST.PatOr (p2::ps) ->
              let uu___ = aux' true loc env1 p2 in
              (match uu___ with
               | (loc1, env2, var, p3, ans) ->
                   let uu___1 =
                     FStar_List.fold_left
                       (fun uu___2 ->
                          fun p4 ->
                            match uu___2 with
                            | (loc2, env3, ps1) ->
                                let uu___3 = aux' true loc2 env3 p4 in
                                (match uu___3 with
                                 | (loc3, env4, uu___4, p5, ans1) ->
                                     (loc3, env4, ((p5, ans1) :: ps1))))
                       (loc1, env2, []) ps in
                   (match uu___1 with
                    | (loc2, env3, ps1) ->
                        let pats = (p3, ans) :: (FStar_List.rev ps1) in
                        (env3, var, pats)))
          | uu___ ->
              let uu___1 = aux' true loc env1 p1 in
              (match uu___1 with
               | (loc1, env2, var, pat, ans) -> (env2, var, [(pat, ans)])) in
        let uu___ = aux_maybe_or env p in
        match uu___ with
        | (env1, b, pats) ->
            ((let uu___2 = FStar_List.map FStar_Pervasives_Native.fst pats in
              check_linear_pattern_variables uu___2 p.FStar_Parser_AST.prange);
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
            let uu___ =
              let uu___1 =
                let uu___2 = FStar_Syntax_DsEnv.qualify env x in
                (uu___2, (ty, tacopt)) in
              LetBinder uu___1 in
            (env, uu___, []) in
          let op_to_ident x =
            let uu___ =
              let uu___1 =
                let uu___2 = FStar_Ident.string_of_id x in
                let uu___3 = FStar_Ident.range_of_id x in
                FStar_Parser_AST.compile_op Prims.int_zero uu___2 uu___3 in
              let uu___2 = FStar_Ident.range_of_id x in (uu___1, uu___2) in
            FStar_Ident.mk_ident uu___ in
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu___ = op_to_ident x in
              let uu___1 =
                let uu___2 = FStar_Ident.range_of_id x in tun_r uu___2 in
              mklet uu___ uu___1 FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x, uu___, uu___1) ->
              let uu___2 =
                let uu___3 = FStar_Ident.range_of_id x in tun_r uu___3 in
              mklet x uu___2 FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu___;_},
               (t, tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env) in
              let uu___1 = op_to_ident x in
              let uu___2 = desugar_term env t in mklet uu___1 uu___2 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x, uu___, uu___1);
                 FStar_Parser_AST.prange = uu___2;_},
               (t, tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env) in
              let uu___3 = desugar_term env t in mklet x uu___3 tacopt1
          | uu___ ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu___1 = desugar_data_pat true env p in
           match uu___1 with
           | (env1, binder, p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu___2;
                      FStar_Syntax_Syntax.p = uu___3;_},
                    uu___4)::[] -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu___2;
                      FStar_Syntax_Syntax.p = uu___3;_},
                    uu___4)::[] -> []
                 | uu___2 -> p1 in
               (env1, binder, p2))
and (desugar_binding_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern -> (env_t * bnd * annotated_pat Prims.list))
  = fun env -> fun p -> desugar_binding_pat_maybe_top false env p
and (desugar_match_pat_maybe_top :
  Prims.bool ->
    env_t -> FStar_Parser_AST.pattern -> (env_t * annotated_pat Prims.list))
  =
  fun uu___ ->
    fun env ->
      fun pat ->
        let uu___1 = desugar_data_pat false env pat in
        match uu___1 with | (env1, uu___2, pat1) -> (env1, pat1)
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
      let uu___ = desugar_term_aq env e in
      match uu___ with | (t, aq) -> (check_no_aq aq; t)
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
      let uu___ = desugar_typ_aq env e in
      match uu___ with | (t, aq) -> (check_no_aq aq; t)
and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness * FStar_Const.width) ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun repr ->
      fun uu___ ->
        fun range ->
          match uu___ with
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
              ((let uu___2 =
                  let uu___3 =
                    FStar_Const.within_bounds repr signedness width in
                  Prims.op_Negation uu___3 in
                if uu___2
                then
                  let uu___3 =
                    let uu___4 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm in
                    (FStar_Errors.Error_OutOfRange, uu___4) in
                  FStar_Errors.log_issue range uu___3
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
                  let uu___2 = FStar_Ident.path_of_text intro_nm in
                  FStar_Ident.lid_of_path uu___2 range in
                let lid1 =
                  let uu___2 = FStar_Syntax_DsEnv.try_lookup_lid env lid in
                  match uu___2 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu___3 =
                               FStar_Ident.path_of_text private_intro_nm in
                             FStar_Ident.lid_of_path uu___3 range in
                           let private_fv =
                             let uu___3 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta in
                             FStar_Syntax_Syntax.lid_as_fv private_lid uu___3
                               fv.FStar_Syntax_Syntax.fv_qual in
                           let uu___3 = intro_term in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___3.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___3.FStar_Syntax_Syntax.vars)
                           }
                       | uu___3 ->
                           failwith
                             (Prims.op_Hat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None ->
                      let uu___3 =
                        let uu___4 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral, uu___4) in
                      FStar_Errors.raise_error uu___3 range in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None))) range in
                let uu___2 =
                  let uu___3 =
                    let uu___4 =
                      let uu___5 =
                        let uu___6 = FStar_Syntax_Syntax.as_implicit false in
                        (repr1, uu___6) in
                      [uu___5] in
                    (lid1, uu___4) in
                  FStar_Syntax_Syntax.Tm_app uu___3 in
                FStar_Syntax_Syntax.mk uu___2 range))
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
          let uu___ = e in
          {
            FStar_Syntax_Syntax.n = (uu___.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars = (uu___.FStar_Syntax_Syntax.vars)
          } in
        let uu___ = let uu___1 = unparen top in uu___1.FStar_Parser_AST.tm in
        match uu___ with
        | FStar_Parser_AST.Wild -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu___1 ->
            let uu___2 = desugar_formula env top in (uu___2, noaqs)
        | FStar_Parser_AST.Requires (t, lopt) ->
            let uu___1 = desugar_formula env t in (uu___1, noaqs)
        | FStar_Parser_AST.Ensures (t, lopt) ->
            let uu___1 = desugar_formula env t in (uu___1, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i, FStar_Pervasives_Native.Some size)) ->
            let uu___1 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range in
            (uu___1, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu___1 = mk (FStar_Syntax_Syntax.Tm_constant c) in
            (uu___1, noaqs)
        | FStar_Parser_AST.Op (id, args) when
            let uu___1 = FStar_Ident.string_of_id id in uu___1 = "=!=" ->
            let r = FStar_Ident.range_of_id id in
            let e =
              let uu___1 =
                let uu___2 =
                  let uu___3 = FStar_Ident.mk_ident ("==", r) in
                  (uu___3, args) in
                FStar_Parser_AST.Op uu___2 in
              FStar_Parser_AST.mk_term uu___1 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level in
            let uu___1 =
              let uu___2 =
                let uu___3 =
                  let uu___4 = FStar_Ident.mk_ident ("~", r) in (uu___4, [e]) in
                FStar_Parser_AST.Op uu___3 in
              FStar_Parser_AST.mk_term uu___2 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level in
            desugar_term_aq env uu___1
        | FStar_Parser_AST.Op (op_star, lhs::rhs::[]) when
            (let uu___1 = FStar_Ident.string_of_id op_star in uu___1 = "*")
              &&
              (let uu___1 = op_as_term env (Prims.of_int (2)) op_star in
               FStar_All.pipe_right uu___1 FStar_Option.isNone)
            ->
            let rec flatten t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op (id, t1::t2::[]) when
                  (let uu___1 = FStar_Ident.string_of_id id in uu___1 = "*")
                    &&
                    (let uu___1 = op_as_term env (Prims.of_int (2)) op_star in
                     FStar_All.pipe_right uu___1 FStar_Option.isNone)
                  -> let uu___1 = flatten t1 in FStar_List.append uu___1 [t2]
              | uu___1 -> [t] in
            let terms = flatten lhs in
            let t =
              let uu___1 = top in
              let uu___2 =
                let uu___3 =
                  let uu___4 =
                    FStar_List.map
                      (fun uu___5 -> FStar_Pervasives.Inr uu___5) terms in
                  (uu___4, rhs) in
                FStar_Parser_AST.Sum uu___3 in
              {
                FStar_Parser_AST.tm = uu___2;
                FStar_Parser_AST.range = (uu___1.FStar_Parser_AST.range);
                FStar_Parser_AST.level = (uu___1.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env t
        | FStar_Parser_AST.Tvar a ->
            let uu___1 =
              let uu___2 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a in
              FStar_All.pipe_left setpos uu___2 in
            (uu___1, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu___1 =
              let uu___2 =
                let uu___3 =
                  let uu___4 = FStar_Ident.string_of_id u in
                  Prims.op_Hat uu___4 " in non-universe context" in
                Prims.op_Hat "Unexpected universe variable " uu___3 in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu___2) in
            FStar_Errors.raise_error uu___1 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s, args) ->
            let uu___1 = op_as_term env (FStar_List.length args) s in
            (match uu___1 with
             | FStar_Pervasives_Native.None ->
                 let uu___2 =
                   let uu___3 =
                     let uu___4 = FStar_Ident.string_of_id s in
                     Prims.op_Hat "Unexpected or unbound operator: " uu___4 in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator, uu___3) in
                 FStar_Errors.raise_error uu___2 top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > Prims.int_zero
                 then
                   let uu___2 =
                     let uu___3 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t ->
                               let uu___4 = desugar_term_aq env t in
                               match uu___4 with
                               | (t', s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1))) in
                     FStar_All.pipe_right uu___3 FStar_List.unzip in
                   (match uu___2 with
                    | (args1, aqs) ->
                        let uu___3 =
                          mk (FStar_Syntax_Syntax.Tm_app (op, args1)) in
                        (uu___3, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n, (a, uu___1)::[]) when
            let uu___2 = FStar_Ident.string_of_lid n in uu___2 = "SMTPat" ->
            let uu___2 =
              let uu___3 = top in
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    let uu___7 = top in
                    let uu___8 =
                      let uu___9 = smt_pat_lid top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu___9 in
                    {
                      FStar_Parser_AST.tm = uu___8;
                      FStar_Parser_AST.range =
                        (uu___7.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___7.FStar_Parser_AST.level)
                    } in
                  (uu___6, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu___5 in
              {
                FStar_Parser_AST.tm = uu___4;
                FStar_Parser_AST.range = (uu___3.FStar_Parser_AST.range);
                FStar_Parser_AST.level = (uu___3.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu___2
        | FStar_Parser_AST.Construct (n, (a, uu___1)::[]) when
            let uu___2 = FStar_Ident.string_of_lid n in uu___2 = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu___3 =
                let uu___4 = top in
                let uu___5 =
                  let uu___6 =
                    let uu___7 =
                      let uu___8 = top in
                      let uu___9 =
                        let uu___10 = smt_pat_lid top.FStar_Parser_AST.range in
                        FStar_Parser_AST.Var uu___10 in
                      {
                        FStar_Parser_AST.tm = uu___9;
                        FStar_Parser_AST.range =
                          (uu___8.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___8.FStar_Parser_AST.level)
                      } in
                    (uu___7, a, FStar_Parser_AST.Nothing) in
                  FStar_Parser_AST.App uu___6 in
                {
                  FStar_Parser_AST.tm = uu___5;
                  FStar_Parser_AST.range = (uu___4.FStar_Parser_AST.range);
                  FStar_Parser_AST.level = (uu___4.FStar_Parser_AST.level)
                } in
              desugar_term_maybe_top top_level env uu___3))
        | FStar_Parser_AST.Construct (n, (a, uu___1)::[]) when
            let uu___2 = FStar_Ident.string_of_lid n in uu___2 = "SMTPatOr"
            ->
            let uu___2 =
              let uu___3 = top in
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    let uu___7 = top in
                    let uu___8 =
                      let uu___9 = smt_pat_or_lid top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu___9 in
                    {
                      FStar_Parser_AST.tm = uu___8;
                      FStar_Parser_AST.range =
                        (uu___7.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___7.FStar_Parser_AST.level)
                    } in
                  (uu___6, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu___5 in
              {
                FStar_Parser_AST.tm = uu___4;
                FStar_Parser_AST.range = (uu___3.FStar_Parser_AST.range);
                FStar_Parser_AST.level = (uu___3.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu___2
        | FStar_Parser_AST.Name lid when
            let uu___1 = FStar_Ident.string_of_lid lid in uu___1 = "Type0" ->
            let uu___1 =
              mk (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero) in
            (uu___1, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu___1 = FStar_Ident.string_of_lid lid in uu___1 = "Type" ->
            let uu___1 =
              mk (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown) in
            (uu___1, noaqs)
        | FStar_Parser_AST.Construct (lid, (t, FStar_Parser_AST.UnivApp)::[])
            when
            let uu___1 = FStar_Ident.string_of_lid lid in uu___1 = "Type" ->
            let uu___1 =
              let uu___2 =
                let uu___3 = desugar_universe t in
                FStar_Syntax_Syntax.Tm_type uu___3 in
              mk uu___2 in
            (uu___1, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu___1 = FStar_Ident.string_of_lid lid in uu___1 = "Effect"
            ->
            let uu___1 =
              mk (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect) in
            (uu___1, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu___1 = FStar_Ident.string_of_lid lid in uu___1 = "True" ->
            let uu___1 =
              let uu___2 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range in
              FStar_Syntax_Syntax.fvar uu___2
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None in
            (uu___1, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu___1 = FStar_Ident.string_of_lid lid in uu___1 = "False" ->
            let uu___1 =
              let uu___2 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range in
              FStar_Syntax_Syntax.fvar uu___2
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None in
            (uu___1, noaqs)
        | FStar_Parser_AST.Projector (eff_name, id) when
            (let uu___1 = FStar_Ident.string_of_id id in
             is_special_effect_combinator uu___1) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            let txt = FStar_Ident.string_of_id id in
            let uu___1 =
              FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name in
            (match uu___1 with
             | FStar_Pervasives_Native.Some ed ->
                 let lid = FStar_Syntax_Util.dm4f_lid ed txt in
                 let uu___2 =
                   FStar_Syntax_Syntax.fvar lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None in
                 (uu___2, noaqs)
             | FStar_Pervasives_Native.None ->
                 let uu___2 =
                   let uu___3 = FStar_Ident.string_of_lid eff_name in
                   FStar_Util.format2
                     "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                     uu___3 txt in
                 failwith uu___2)
        | FStar_Parser_AST.Var l ->
            let uu___1 = desugar_name mk setpos env true l in (uu___1, noaqs)
        | FStar_Parser_AST.Name l ->
            let uu___1 = desugar_name mk setpos env true l in (uu___1, noaqs)
        | FStar_Parser_AST.Projector (l, i) ->
            let name =
              let uu___1 = FStar_Syntax_DsEnv.try_lookup_datacon env l in
              match uu___1 with
              | FStar_Pervasives_Native.Some uu___2 ->
                  FStar_Pervasives_Native.Some (true, l)
              | FStar_Pervasives_Native.None ->
                  let uu___2 =
                    FStar_Syntax_DsEnv.try_lookup_root_effect_name env l in
                  (match uu___2 with
                   | FStar_Pervasives_Native.Some new_name ->
                       FStar_Pervasives_Native.Some (false, new_name)
                   | uu___3 -> FStar_Pervasives_Native.None) in
            (match name with
             | FStar_Pervasives_Native.Some (resolve, new_name) ->
                 let uu___1 =
                   let uu___2 =
                     FStar_Syntax_Util.mk_field_projector_name_from_ident
                       new_name i in
                   desugar_name mk setpos env resolve uu___2 in
                 (uu___1, noaqs)
             | uu___1 ->
                 let uu___2 =
                   let uu___3 =
                     let uu___4 = FStar_Ident.string_of_lid l in
                     FStar_Util.format1
                       "Data constructor or effect %s not found" uu___4 in
                   (FStar_Errors.Fatal_EffectNotFound, uu___3) in
                 FStar_Errors.raise_error uu___2 top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Discrim lid ->
            let uu___1 = FStar_Syntax_DsEnv.try_lookup_datacon env lid in
            (match uu___1 with
             | FStar_Pervasives_Native.None ->
                 let uu___2 =
                   let uu___3 =
                     let uu___4 = FStar_Ident.string_of_lid lid in
                     FStar_Util.format1 "Data constructor %s not found"
                       uu___4 in
                   (FStar_Errors.Fatal_DataContructorNotFound, uu___3) in
                 FStar_Errors.raise_error uu___2 top.FStar_Parser_AST.range
             | uu___2 ->
                 let lid' = FStar_Syntax_Util.mk_discriminator lid in
                 let uu___3 = desugar_name mk setpos env true lid' in
                 (uu___3, noaqs))
        | FStar_Parser_AST.Construct (l, args) ->
            let uu___1 = FStar_Syntax_DsEnv.try_lookup_datacon env l in
            (match uu___1 with
             | FStar_Pervasives_Native.Some head ->
                 let head1 = mk (FStar_Syntax_Syntax.Tm_fvar head) in
                 (match args with
                  | [] -> (head1, noaqs)
                  | uu___2 ->
                      let uu___3 =
                        FStar_Util.take
                          (fun uu___4 ->
                             match uu___4 with
                             | (uu___5, imp) ->
                                 imp = FStar_Parser_AST.UnivApp) args in
                      (match uu___3 with
                       | (universes, args1) ->
                           let universes1 =
                             FStar_List.map
                               (fun x ->
                                  desugar_universe
                                    (FStar_Pervasives_Native.fst x))
                               universes in
                           let uu___4 =
                             let uu___5 =
                               FStar_List.map
                                 (fun uu___6 ->
                                    match uu___6 with
                                    | (t, imp) ->
                                        let uu___7 = desugar_term_aq env t in
                                        (match uu___7 with
                                         | (te, aq) ->
                                             ((arg_withimp_e imp te), aq)))
                                 args1 in
                             FStar_All.pipe_right uu___5 FStar_List.unzip in
                           (match uu___4 with
                            | (args2, aqs) ->
                                let head2 =
                                  if universes1 = []
                                  then head1
                                  else
                                    mk
                                      (FStar_Syntax_Syntax.Tm_uinst
                                         (head1, universes1)) in
                                let uu___5 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_app
                                       (head2, args2)) in
                                (uu___5, (join_aqs aqs)))))
             | FStar_Pervasives_Native.None ->
                 let err =
                   let uu___2 =
                     FStar_Syntax_DsEnv.try_lookup_effect_name env l in
                   match uu___2 with
                   | FStar_Pervasives_Native.None ->
                       let uu___3 =
                         let uu___4 =
                           let uu___5 = FStar_Ident.string_of_lid l in
                           Prims.op_Hat uu___5 " not found" in
                         Prims.op_Hat "Constructor " uu___4 in
                       (FStar_Errors.Fatal_ConstructorNotFound, uu___3)
                   | FStar_Pervasives_Native.Some uu___3 ->
                       let uu___4 =
                         let uu___5 =
                           let uu___6 = FStar_Ident.string_of_lid l in
                           Prims.op_Hat uu___6
                             " used at an unexpected position" in
                         Prims.op_Hat "Effect " uu___5 in
                       (FStar_Errors.Fatal_UnexpectedEffect, uu___4) in
                 FStar_Errors.raise_error err top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Sum (binders, t) when
            FStar_Util.for_all
              (fun uu___1 ->
                 match uu___1 with
                 | FStar_Pervasives.Inr uu___2 -> true
                 | uu___2 -> false) binders
            ->
            let terms =
              let uu___1 =
                FStar_All.pipe_right binders
                  (FStar_List.map
                     (fun uu___2 ->
                        match uu___2 with
                        | FStar_Pervasives.Inr x -> x
                        | FStar_Pervasives.Inl uu___3 ->
                            failwith "Impossible")) in
              FStar_List.append uu___1 [t] in
            let uu___1 =
              let uu___2 =
                FStar_All.pipe_right terms
                  (FStar_List.map
                     (fun t1 ->
                        let uu___3 = desugar_typ_aq env t1 in
                        match uu___3 with
                        | (t', aq) ->
                            let uu___4 = FStar_Syntax_Syntax.as_arg t' in
                            (uu___4, aq))) in
              FStar_All.pipe_right uu___2 FStar_List.unzip in
            (match uu___1 with
             | (targs, aqs) ->
                 let tup =
                   let uu___2 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu___2 in
                 let uu___2 = mk (FStar_Syntax_Syntax.Tm_app (tup, targs)) in
                 (uu___2, (join_aqs aqs)))
        | FStar_Parser_AST.Sum (binders, t) ->
            let uu___1 =
              let uu___2 =
                let uu___3 =
                  let uu___4 =
                    FStar_All.pipe_left
                      (fun uu___5 -> FStar_Pervasives.Inl uu___5)
                      (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                         FStar_Pervasives_Native.None) in
                  [uu___4] in
                FStar_List.append binders uu___3 in
              FStar_List.fold_left
                (fun uu___3 ->
                   fun b ->
                     match uu___3 with
                     | (env1, tparams, typs) ->
                         let uu___4 =
                           match b with
                           | FStar_Pervasives.Inl b1 ->
                               desugar_binder env1 b1
                           | FStar_Pervasives.Inr t1 ->
                               let uu___5 = desugar_typ env1 t1 in
                               (FStar_Pervasives_Native.None, uu___5, []) in
                         (match uu___4 with
                          | (xopt, t1, attrs) ->
                              let uu___5 =
                                match xopt with
                                | FStar_Pervasives_Native.None ->
                                    let uu___6 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        (setpos FStar_Syntax_Syntax.tun) in
                                    (env1, uu___6)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x in
                              (match uu___5 with
                               | (env2, x) ->
                                   let uu___6 =
                                     let uu___7 =
                                       let uu___8 =
                                         FStar_Syntax_Syntax.mk_binder_with_attrs
                                           (let uu___9 = x in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___9.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___9.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            }) FStar_Pervasives_Native.None
                                           attrs in
                                       [uu___8] in
                                     FStar_List.append tparams uu___7 in
                                   let uu___7 =
                                     let uu___8 =
                                       let uu___9 =
                                         let uu___10 =
                                           no_annot_abs tparams t1 in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg uu___10 in
                                       [uu___9] in
                                     FStar_List.append typs uu___8 in
                                   (env2, uu___6, uu___7)))) (env, [], [])
                uu___2 in
            (match uu___1 with
             | (env1, uu___2, targs) ->
                 let tup =
                   let uu___3 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu___3 in
                 let uu___3 =
                   FStar_All.pipe_left mk
                     (FStar_Syntax_Syntax.Tm_app (tup, targs)) in
                 (uu___3, noaqs))
        | FStar_Parser_AST.Product (binders, t) ->
            let uu___1 = uncurry binders t in
            (match uu___1 with
             | (bs, t1) ->
                 let rec aux env1 bs1 uu___2 =
                   match uu___2 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range true env1 t1 in
                       let uu___3 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod in
                       FStar_All.pipe_left setpos uu___3
                   | hd::tl ->
                       let bb = desugar_binder env1 hd in
                       let uu___3 =
                         as_binder env1 hd.FStar_Parser_AST.aqual bb in
                       (match uu___3 with
                        | (b, env2) -> aux env2 (b :: bs1) tl) in
                 let uu___2 = aux env [] bs in (uu___2, noaqs))
        | FStar_Parser_AST.Refine (b, f) ->
            let uu___1 = desugar_binder env b in
            (match uu___1 with
             | (FStar_Pervasives_Native.None, uu___2, uu___3) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu___2 = as_binder env FStar_Pervasives_Native.None b1 in
                 (match uu___2 with
                  | (b2, env1) ->
                      let f1 = desugar_formula env1 f in
                      let uu___3 =
                        let uu___4 =
                          FStar_Syntax_Util.refine
                            b2.FStar_Syntax_Syntax.binder_bv f1 in
                        FStar_All.pipe_left setpos uu___4 in
                      (uu___3, noaqs)))
        | FStar_Parser_AST.Abs (binders, body) ->
            let bvss = FStar_List.map gather_pattern_bound_vars binders in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set::sets2 ->
                    let i = FStar_Util.set_intersect acc set in
                    let uu___1 = FStar_Util.set_is_empty i in
                    if uu___1
                    then
                      let uu___2 = FStar_Util.set_union acc set in
                      aux uu___2 sets2
                    else
                      (let uu___3 =
                         let uu___4 = FStar_Util.set_elements i in
                         FStar_List.hd uu___4 in
                       FStar_Pervasives_Native.Some uu___3) in
              let uu___1 = FStar_Syntax_Syntax.new_id_set () in
              aux uu___1 sets in
            ((let uu___2 = check_disjoint bvss in
              match uu___2 with
              | FStar_Pervasives_Native.None -> ()
              | FStar_Pervasives_Native.Some id ->
                  let uu___3 =
                    let uu___4 =
                      let uu___5 = FStar_Ident.string_of_id id in
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        uu___5 in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted, uu___4) in
                  let uu___4 = FStar_Ident.range_of_id id in
                  FStar_Errors.raise_error uu___3 uu___4);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern) in
              let uu___2 =
                FStar_List.fold_left
                  (fun uu___3 ->
                     fun pat ->
                       match uu___3 with
                       | (env1, ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu___4, (t, FStar_Pervasives_Native.None))
                                ->
                                let uu___5 =
                                  let uu___6 = free_type_vars env1 t in
                                  FStar_List.append uu___6 ftvs in
                                (env1, uu___5)
                            | FStar_Parser_AST.PatAscribed
                                (uu___4,
                                 (t, FStar_Pervasives_Native.Some tac))
                                ->
                                let uu___5 =
                                  let uu___6 = free_type_vars env1 t in
                                  let uu___7 =
                                    let uu___8 = free_type_vars env1 tac in
                                    FStar_List.append uu___8 ftvs in
                                  FStar_List.append uu___6 uu___7 in
                                (env1, uu___5)
                            | uu___4 -> (env1, ftvs))) (env, []) binders1 in
              match uu___2 with
              | (uu___3, ftv) ->
                  let ftv1 = sort_ftv ftv in
                  let binders2 =
                    let uu___4 =
                      FStar_All.pipe_right ftv1
                        (FStar_List.map
                           (fun a ->
                              FStar_Parser_AST.mk_pattern
                                (FStar_Parser_AST.PatTvar
                                   (a,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Parser_AST.Implicit), []))
                                top.FStar_Parser_AST.range)) in
                    FStar_List.append uu___4 binders1 in
                  let rec aux env1 bs sc_pat_opt pats =
                    match pats with
                    | [] ->
                        let uu___4 = desugar_term_aq env1 body in
                        (match uu___4 with
                         | (body1, aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc, pat) ->
                                   let body3 =
                                     let uu___5 =
                                       let uu___6 =
                                         FStar_Syntax_Syntax.pat_bvs pat in
                                       FStar_All.pipe_right uu___6
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder) in
                                     FStar_Syntax_Subst.close uu___5 body1 in
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_match
                                        (sc, FStar_Pervasives_Native.None,
                                          [(pat,
                                             FStar_Pervasives_Native.None,
                                             body3)]))
                                     body3.FStar_Syntax_Syntax.pos
                               | FStar_Pervasives_Native.None -> body1 in
                             let uu___5 =
                               let uu___6 =
                                 no_annot_abs (FStar_List.rev bs) body2 in
                               setpos uu___6 in
                             (uu___5, aq))
                    | p::rest ->
                        let uu___4 = desugar_binding_pat env1 p in
                        (match uu___4 with
                         | (env2, b, pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1, uu___5)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu___5 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange in
                             let uu___5 =
                               match b with
                               | LetBinder uu___6 -> failwith "Impossible"
                               | LocalBinder (x, aq, attrs) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None, uu___6)
                                         -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some p1,
                                        FStar_Pervasives_Native.None) ->
                                         let uu___6 =
                                           let uu___7 =
                                             FStar_Syntax_Syntax.bv_to_name x in
                                           (uu___7, p1) in
                                         FStar_Pervasives_Native.Some uu___6
                                     | (FStar_Pervasives_Native.Some p1,
                                        FStar_Pervasives_Native.Some
                                        (sc, p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu___6, uu___7) ->
                                              let tup2 =
                                                let uu___8 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.of_int (2))
                                                    top.FStar_Parser_AST.range in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu___8
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor) in
                                              let sc1 =
                                                let uu___8 =
                                                  let uu___9 =
                                                    let uu___10 =
                                                      mk
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tup2) in
                                                    let uu___11 =
                                                      let uu___12 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          sc in
                                                      let uu___13 =
                                                        let uu___14 =
                                                          let uu___15 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu___15 in
                                                        [uu___14] in
                                                      uu___12 :: uu___13 in
                                                    (uu___10, uu___11) in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu___9 in
                                                FStar_Syntax_Syntax.mk uu___8
                                                  top.FStar_Parser_AST.range in
                                              let p2 =
                                                let uu___8 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)])) uu___8 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu___6, args),
                                             FStar_Syntax_Syntax.Pat_cons
                                             (uu___7, pats1)) ->
                                              let tupn =
                                                let uu___8 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.int_one +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu___8
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor) in
                                              let sc1 =
                                                let uu___8 =
                                                  let uu___9 =
                                                    let uu___10 =
                                                      mk
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn) in
                                                    let uu___11 =
                                                      let uu___12 =
                                                        let uu___13 =
                                                          let uu___14 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu___14 in
                                                        [uu___13] in
                                                      FStar_List.append args
                                                        uu___12 in
                                                    (uu___10, uu___11) in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu___9 in
                                                mk uu___8 in
                                              let p2 =
                                                let uu___8 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats1 [(p1, false)])))
                                                  uu___8 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu___6 -> failwith "Impossible") in
                                   let uu___6 =
                                     FStar_Syntax_Syntax.mk_binder_with_attrs
                                       x aq attrs in
                                   (uu___6, sc_pat_opt1) in
                             (match uu___5 with
                              | (b1, sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest)) in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App (uu___1, uu___2, FStar_Parser_AST.UnivApp) ->
            let rec aux universes e =
              let uu___3 =
                let uu___4 = unparen e in uu___4.FStar_Parser_AST.tm in
              match uu___3 with
              | FStar_Parser_AST.App (e1, t, FStar_Parser_AST.UnivApp) ->
                  let univ_arg = desugar_universe t in
                  aux (univ_arg :: universes) e1
              | uu___4 ->
                  let uu___5 = desugar_term_aq env e in
                  (match uu___5 with
                   | (head, aq) ->
                       let uu___6 =
                         mk (FStar_Syntax_Syntax.Tm_uinst (head, universes)) in
                       (uu___6, aq)) in
            aux [] top
        | FStar_Parser_AST.App uu___1 ->
            let rec aux args aqs e =
              let uu___2 =
                let uu___3 = unparen e in uu___3.FStar_Parser_AST.tm in
              match uu___2 with
              | FStar_Parser_AST.App (e1, t, imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu___3 = desugar_term_aq env t in
                  (match uu___3 with
                   | (t1, aq) ->
                       let arg = arg_withimp_e imp t1 in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu___3 ->
                  let uu___4 = desugar_term_aq env e in
                  (match uu___4 with
                   | (head, aq) ->
                       let uu___5 =
                         FStar_Syntax_Syntax.extend_app_n head args
                           top.FStar_Parser_AST.range in
                       (uu___5, (join_aqs (aq :: aqs)))) in
            aux [] [] top
        | FStar_Parser_AST.Bind (x, t1, t2) ->
            let xpat =
              let uu___1 = FStar_Ident.range_of_id x in
              FStar_Parser_AST.mk_pattern
                (FStar_Parser_AST.PatVar
                   (x, FStar_Pervasives_Native.None, [])) uu___1 in
            let k =
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Abs ([xpat], t2))
                t2.FStar_Parser_AST.range t2.FStar_Parser_AST.level in
            let bind_lid =
              let uu___1 = FStar_Ident.range_of_id x in
              FStar_Ident.lid_of_path ["bind"] uu___1 in
            let bind =
              let uu___1 = FStar_Ident.range_of_id x in
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Var bind_lid) uu___1
                FStar_Parser_AST.Expr in
            let uu___1 =
              FStar_Parser_AST.mkExplicitApp bind [t1; k]
                top.FStar_Parser_AST.range in
            desugar_term_aq env uu___1
        | FStar_Parser_AST.Seq (t1, t2) ->
            let t =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Let
                   (FStar_Parser_AST.NoLetQualifier,
                     [(FStar_Pervasives_Native.None,
                        ((FStar_Parser_AST.mk_pattern
                            (FStar_Parser_AST.PatWild
                               (FStar_Pervasives_Native.None, []))
                            t1.FStar_Parser_AST.range), t1))], t2))
                top.FStar_Parser_AST.range FStar_Parser_AST.Expr in
            let uu___1 = desugar_term_aq env t in
            (match uu___1 with
             | (tm, s) ->
                 let uu___2 =
                   mk
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence))) in
                 (uu___2, s))
        | FStar_Parser_AST.LetOpen (lid, e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid in
            let uu___1 =
              let uu___2 = FStar_Syntax_DsEnv.expect_typ env1 in
              if uu___2 then desugar_typ_aq else desugar_term_aq in
            uu___1 env1 e
        | FStar_Parser_AST.LetOpenRecord (r, rty, e) ->
            let rec head_of t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.App (t1, uu___1, uu___2) -> head_of t1
              | uu___1 -> t in
            let tycon = head_of rty in
            let tycon_name =
              match tycon.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var l -> l
              | uu___1 ->
                  let uu___2 =
                    let uu___3 =
                      let uu___4 = FStar_Parser_AST.term_to_string rty in
                      FStar_Util.format1
                        "This type must be a (possibly applied) record name"
                        uu___4 in
                    (FStar_Errors.Error_BadLetOpenRecord, uu___3) in
                  FStar_Errors.raise_error uu___2 rty.FStar_Parser_AST.range in
            let record =
              let uu___1 =
                FStar_Syntax_DsEnv.try_lookup_record_type env tycon_name in
              match uu___1 with
              | FStar_Pervasives_Native.Some r1 -> r1
              | FStar_Pervasives_Native.None ->
                  let uu___2 =
                    let uu___3 =
                      let uu___4 = FStar_Parser_AST.term_to_string rty in
                      FStar_Util.format1 "Not a record type: `%s`" uu___4 in
                    (FStar_Errors.Error_BadLetOpenRecord, uu___3) in
                  FStar_Errors.raise_error uu___2 rty.FStar_Parser_AST.range in
            let constrname =
              let uu___1 =
                FStar_Ident.ns_of_lid record.FStar_Syntax_DsEnv.typename in
              FStar_Ident.lid_of_ns_and_id uu___1
                record.FStar_Syntax_DsEnv.constrname in
            let mk_pattern p =
              FStar_Parser_AST.mk_pattern p r.FStar_Parser_AST.range in
            let elab =
              let pat =
                let uu___1 =
                  let uu___2 =
                    let uu___3 =
                      FStar_List.map
                        (fun uu___4 ->
                           match uu___4 with
                           | (field, uu___5) ->
                               mk_pattern
                                 (FStar_Parser_AST.PatVar
                                    (field, FStar_Pervasives_Native.None, [])))
                        record.FStar_Syntax_DsEnv.fields in
                    ((mk_pattern (FStar_Parser_AST.PatName constrname)),
                      uu___3) in
                  FStar_Parser_AST.PatApp uu___2 in
                mk_pattern uu___1 in
              let branch = (pat, FStar_Pervasives_Native.None, e) in
              let r1 =
                FStar_Parser_AST.mk_term
                  (FStar_Parser_AST.Ascribed
                     (r, rty, FStar_Pervasives_Native.None))
                  r.FStar_Parser_AST.range FStar_Parser_AST.Expr in
              let uu___1 = top in
              {
                FStar_Parser_AST.tm =
                  (FStar_Parser_AST.Match
                     (r1, FStar_Pervasives_Native.None, [branch]));
                FStar_Parser_AST.range = (uu___1.FStar_Parser_AST.range);
                FStar_Parser_AST.level = (uu___1.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env elab
        | FStar_Parser_AST.Let (qual, lbs, body) ->
            let is_rec = qual = FStar_Parser_AST.Rec in
            let ds_let_rec_or_app uu___1 =
              let bindings = lbs in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu___2 ->
                        match uu___2 with
                        | (attr_opt, (p, def)) ->
                            let uu___3 = is_app_pattern p in
                            if uu___3
                            then
                              let uu___4 =
                                destruct_app_pattern env top_level p in
                              (attr_opt, uu___4, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1, def1) ->
                                   let uu___5 =
                                     destruct_app_pattern env top_level p1 in
                                   (attr_opt, uu___5, def1)
                               | uu___5 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id, uu___6, uu___7);
                                           FStar_Parser_AST.prange = uu___8;_},
                                         t)
                                        ->
                                        if top_level
                                        then
                                          let uu___9 =
                                            let uu___10 =
                                              let uu___11 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id in
                                              FStar_Pervasives.Inr uu___11 in
                                            (uu___10, [],
                                              (FStar_Pervasives_Native.Some t)) in
                                          (attr_opt, uu___9, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Pervasives.Inl id), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id, uu___6, uu___7) ->
                                        if top_level
                                        then
                                          let uu___8 =
                                            let uu___9 =
                                              let uu___10 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id in
                                              FStar_Pervasives.Inr uu___10 in
                                            (uu___9, [],
                                              FStar_Pervasives_Native.None) in
                                          (attr_opt, uu___8, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Pervasives.Inl id), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu___6 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange)))) in
              let uu___2 =
                FStar_List.fold_left
                  (fun uu___3 ->
                     fun uu___4 ->
                       match (uu___3, uu___4) with
                       | ((env1, fnames, rec_bindings, used_markers),
                          (_attr_opt, (f, uu___5, uu___6), uu___7)) ->
                           let uu___8 =
                             match f with
                             | FStar_Pervasives.Inl x ->
                                 let uu___9 =
                                   FStar_Syntax_DsEnv.push_bv' env1 x in
                                 (match uu___9 with
                                  | (env2, xx, used_marker) ->
                                      let dummy_ref = FStar_Util.mk_ref true in
                                      let uu___10 =
                                        let uu___11 =
                                          FStar_Syntax_Syntax.mk_binder xx in
                                        uu___11 :: rec_bindings in
                                      (env2, (FStar_Pervasives.Inl xx),
                                        uu___10, (used_marker ::
                                        used_markers)))
                             | FStar_Pervasives.Inr l ->
                                 let uu___9 =
                                   let uu___10 = FStar_Ident.ident_of_lid l in
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 uu___10
                                     FStar_Syntax_Syntax.delta_equational in
                                 (match uu___9 with
                                  | (env2, used_marker) ->
                                      (env2, (FStar_Pervasives.Inr l),
                                        rec_bindings, (used_marker ::
                                        used_markers))) in
                           (match uu___8 with
                            | (env2, lbname, rec_bindings1, used_markers1) ->
                                (env2, (lbname :: fnames), rec_bindings1,
                                  used_markers1))) (env, [], [], []) funs in
              match uu___2 with
              | (env', fnames, rec_bindings, used_markers) ->
                  let fnames1 = FStar_List.rev fnames in
                  let rec_bindings1 = FStar_List.rev rec_bindings in
                  let used_markers1 = FStar_List.rev used_markers in
                  let desugar_one_def env1 lbname uu___3 =
                    match uu___3 with
                    | (attrs_opt, (uu___4, args, result_t), def) ->
                        let args1 =
                          FStar_All.pipe_right args
                            (FStar_List.map replace_unit_pattern) in
                        let pos = def.FStar_Parser_AST.range in
                        let def1 =
                          match result_t with
                          | FStar_Pervasives_Native.None -> def
                          | FStar_Pervasives_Native.Some (t, tacopt) ->
                              let t1 =
                                let uu___5 = is_comp_type env1 t in
                                if uu___5
                                then
                                  ((let uu___7 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x ->
                                              let uu___8 = is_var_pattern x in
                                              Prims.op_Negation uu___8)) in
                                    match uu___7 with
                                    | FStar_Pervasives_Native.None -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu___7 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu___8 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid in
                                         FStar_Option.isSome uu___8))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             Prims.int_zero)) in
                                   if uu___7
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t) in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed (def, t1, tacopt))
                                def.FStar_Parser_AST.range
                                FStar_Parser_AST.Expr in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu___5 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level in
                        let uu___5 = desugar_term_aq env1 def2 in
                        (match uu___5 with
                         | (body1, aq) ->
                             let lbname1 =
                               match lbname with
                               | FStar_Pervasives.Inl x ->
                                   FStar_Pervasives.Inl x
                               | FStar_Pervasives.Inr l ->
                                   let uu___6 =
                                     let uu___7 =
                                       FStar_Syntax_Util.incr_delta_qualifier
                                         body1 in
                                     FStar_Syntax_Syntax.lid_as_fv l uu___7
                                       FStar_Pervasives_Native.None in
                                   FStar_Pervasives.Inr uu___6 in
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
                  let uu___3 =
                    let uu___4 =
                      FStar_List.map2
                        (desugar_one_def (if is_rec then env' else env))
                        fnames1 funs in
                    FStar_All.pipe_right uu___4 FStar_List.unzip in
                  (match uu___3 with
                   | (lbs1, aqss) ->
                       let uu___4 = desugar_term_aq env' body in
                       (match uu___4 with
                        | (body1, aq) ->
                            (if is_rec
                             then
                               FStar_List.iter2
                                 (fun uu___6 ->
                                    fun used_marker ->
                                      match uu___6 with
                                      | (_attr_opt, (f, uu___7, uu___8),
                                         uu___9) ->
                                          let uu___10 =
                                            let uu___11 =
                                              FStar_ST.op_Bang used_marker in
                                            Prims.op_Negation uu___11 in
                                          if uu___10
                                          then
                                            let uu___11 =
                                              match f with
                                              | FStar_Pervasives.Inl x ->
                                                  let uu___12 =
                                                    FStar_Ident.string_of_id
                                                      x in
                                                  let uu___13 =
                                                    FStar_Ident.range_of_id x in
                                                  (uu___12, "Local", uu___13)
                                              | FStar_Pervasives.Inr l ->
                                                  let uu___12 =
                                                    FStar_Ident.string_of_lid
                                                      l in
                                                  let uu___13 =
                                                    FStar_Ident.range_of_lid
                                                      l in
                                                  (uu___12, "Global",
                                                    uu___13) in
                                            (match uu___11 with
                                             | (nm, gl, rng) ->
                                                 let uu___12 =
                                                   let uu___13 =
                                                     FStar_Util.format2
                                                       "%s binding %s is recursive but not used in its body"
                                                       gl nm in
                                                   (FStar_Errors.Warning_UnusedLetRec,
                                                     uu___13) in
                                                 FStar_Errors.log_issue rng
                                                   uu___12)
                                          else ()) funs used_markers1
                             else ();
                             (let uu___6 =
                                let uu___7 =
                                  let uu___8 =
                                    let uu___9 =
                                      FStar_Syntax_Subst.close rec_bindings1
                                        body1 in
                                    ((is_rec, lbs1), uu___9) in
                                  FStar_Syntax_Syntax.Tm_let uu___8 in
                                FStar_All.pipe_left mk uu___7 in
                              (uu___6,
                                (FStar_List.append aq
                                   (FStar_List.flatten aqss))))))) in
            let ds_non_rec attrs_opt pat t1 t2 =
              let attrs =
                match attrs_opt with
                | FStar_Pervasives_Native.None -> []
                | FStar_Pervasives_Native.Some l ->
                    FStar_List.map (desugar_term env) l in
              let uu___1 = desugar_term_aq env t1 in
              match uu___1 with
              | (t11, aq0) ->
                  let uu___2 =
                    desugar_binding_pat_maybe_top top_level env pat in
                  (match uu___2 with
                   | (env1, binder, pat1) ->
                       let uu___3 =
                         match binder with
                         | LetBinder (l, (t, _tacopt)) ->
                             let uu___4 = desugar_term_aq env1 t2 in
                             (match uu___4 with
                              | (body1, aq) ->
                                  let fv =
                                    let uu___5 =
                                      FStar_Syntax_Util.incr_delta_qualifier
                                        t11 in
                                    FStar_Syntax_Syntax.lid_as_fv l uu___5
                                      FStar_Pervasives_Native.None in
                                  let uu___5 =
                                    FStar_All.pipe_left mk
                                      (FStar_Syntax_Syntax.Tm_let
                                         ((false,
                                            [mk_lb
                                               (attrs,
                                                 (FStar_Pervasives.Inr fv),
                                                 t, t11,
                                                 (t11.FStar_Syntax_Syntax.pos))]),
                                           body1)) in
                                  (uu___5, aq))
                         | LocalBinder (x, uu___4, uu___5) ->
                             let uu___6 = desugar_term_aq env1 t2 in
                             (match uu___6 with
                              | (body1, aq) ->
                                  let body2 =
                                    match pat1 with
                                    | [] -> body1
                                    | ({
                                         FStar_Syntax_Syntax.v =
                                           FStar_Syntax_Syntax.Pat_wild
                                           uu___7;
                                         FStar_Syntax_Syntax.p = uu___8;_},
                                       uu___9)::[] -> body1
                                    | uu___7 ->
                                        let uu___8 =
                                          let uu___9 =
                                            let uu___10 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x in
                                            let uu___11 =
                                              desugar_disjunctive_pattern
                                                pat1
                                                FStar_Pervasives_Native.None
                                                body1 in
                                            (uu___10,
                                              FStar_Pervasives_Native.None,
                                              uu___11) in
                                          FStar_Syntax_Syntax.Tm_match uu___9 in
                                        FStar_Syntax_Syntax.mk uu___8
                                          top.FStar_Parser_AST.range in
                                  let uu___7 =
                                    let uu___8 =
                                      let uu___9 =
                                        let uu___10 =
                                          let uu___11 =
                                            let uu___12 =
                                              FStar_Syntax_Syntax.mk_binder x in
                                            [uu___12] in
                                          FStar_Syntax_Subst.close uu___11
                                            body2 in
                                        ((false,
                                           [mk_lb
                                              (attrs,
                                                (FStar_Pervasives.Inl x),
                                                (x.FStar_Syntax_Syntax.sort),
                                                t11,
                                                (t11.FStar_Syntax_Syntax.pos))]),
                                          uu___10) in
                                      FStar_Syntax_Syntax.Tm_let uu___9 in
                                    FStar_All.pipe_left mk uu___8 in
                                  (uu___7, aq)) in
                       (match uu___3 with
                        | (tm, aq1) -> (tm, (FStar_List.append aq0 aq1)))) in
            let uu___1 = FStar_List.hd lbs in
            (match uu___1 with
             | (attrs, (head_pat, defn)) ->
                 let uu___2 = is_rec || (is_app_pattern head_pat) in
                 if uu___2
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1, asc_opt, t2, t3) ->
            let x =
              let uu___1 = tun_r t3.FStar_Parser_AST.range in
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                uu___1 in
            let t_bool =
              let uu___1 =
                let uu___2 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None in
                FStar_Syntax_Syntax.Tm_fvar uu___2 in
              mk uu___1 in
            let uu___1 = desugar_term_aq env t1 in
            (match uu___1 with
             | (t1', aq1) ->
                 let t1'1 =
                   FStar_Syntax_Util.ascribe t1'
                     ((FStar_Pervasives.Inl t_bool),
                       FStar_Pervasives_Native.None) in
                 let uu___2 =
                   match asc_opt with
                   | FStar_Pervasives_Native.None ->
                       (FStar_Pervasives_Native.None, [])
                   | FStar_Pervasives_Native.Some t ->
                       let uu___3 =
                         desugar_ascription env t
                           FStar_Pervasives_Native.None in
                       FStar_All.pipe_right uu___3
                         (fun uu___4 ->
                            match uu___4 with
                            | (t4, q) ->
                                ((FStar_Pervasives_Native.Some t4), q)) in
                 (match uu___2 with
                  | (asc_opt1, aq0) ->
                      let uu___3 = desugar_term_aq env t2 in
                      (match uu___3 with
                       | (t2', aq2) ->
                           let uu___4 = desugar_term_aq env t3 in
                           (match uu___4 with
                            | (t3', aq3) ->
                                let uu___5 =
                                  let uu___6 =
                                    let uu___7 =
                                      let uu___8 =
                                        let uu___9 =
                                          let uu___10 =
                                            FStar_Syntax_Syntax.withinfo
                                              (FStar_Syntax_Syntax.Pat_constant
                                                 (FStar_Const.Const_bool true))
                                              t1.FStar_Parser_AST.range in
                                          (uu___10,
                                            FStar_Pervasives_Native.None,
                                            t2') in
                                        let uu___10 =
                                          let uu___11 =
                                            let uu___12 =
                                              FStar_Syntax_Syntax.withinfo
                                                (FStar_Syntax_Syntax.Pat_wild
                                                   x)
                                                t1.FStar_Parser_AST.range in
                                            (uu___12,
                                              FStar_Pervasives_Native.None,
                                              t3') in
                                          [uu___11] in
                                        uu___9 :: uu___10 in
                                      (t1'1, asc_opt1, uu___8) in
                                    FStar_Syntax_Syntax.Tm_match uu___7 in
                                  mk uu___6 in
                                (uu___5, (join_aqs [aq1; aq0; aq2; aq3]))))))
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
        | FStar_Parser_AST.Match (e, topt, branches) ->
            let desugar_branch uu___1 =
              match uu___1 with
              | (pat, wopt, b) ->
                  let uu___2 = desugar_match_pat env pat in
                  (match uu___2 with
                   | (env1, pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu___3 = desugar_term env1 e1 in
                             FStar_Pervasives_Native.Some uu___3 in
                       let uu___3 = desugar_term_aq env1 b in
                       (match uu___3 with
                        | (b1, aq) ->
                            let uu___4 =
                              desugar_disjunctive_pattern pat1 wopt1 b1 in
                            (uu___4, aq))) in
            let uu___1 = desugar_term_aq env e in
            (match uu___1 with
             | (e1, aq) ->
                 let uu___2 =
                   match topt with
                   | FStar_Pervasives_Native.None ->
                       (FStar_Pervasives_Native.None, [])
                   | FStar_Pervasives_Native.Some t ->
                       let uu___3 =
                         desugar_ascription env t
                           FStar_Pervasives_Native.None in
                       FStar_All.pipe_right uu___3
                         (fun uu___4 ->
                            match uu___4 with
                            | (t1, q) ->
                                ((FStar_Pervasives_Native.Some t1), q)) in
                 (match uu___2 with
                  | (asc_opt, aq0) ->
                      let uu___3 =
                        let uu___4 =
                          let uu___5 = FStar_List.map desugar_branch branches in
                          FStar_All.pipe_right uu___5 FStar_List.unzip in
                        FStar_All.pipe_right uu___4
                          (fun uu___5 ->
                             match uu___5 with
                             | (x, y) -> ((FStar_List.flatten x), y)) in
                      (match uu___3 with
                       | (brs, aqs) ->
                           let uu___4 =
                             FStar_All.pipe_left mk
                               (FStar_Syntax_Syntax.Tm_match
                                  (e1, asc_opt, brs)) in
                           (uu___4, (join_aqs (aq :: aq0 :: aqs))))))
        | FStar_Parser_AST.Ascribed (e, t, tac_opt) ->
            let uu___1 = desugar_ascription env t tac_opt in
            (match uu___1 with
             | (asc, aq0) ->
                 let uu___2 = desugar_term_aq env e in
                 (match uu___2 with
                  | (e1, aq) ->
                      let uu___3 =
                        FStar_All.pipe_left mk
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, asc, FStar_Pervasives_Native.None)) in
                      (uu___3, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu___1, []) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt, fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range in
            let user_ns =
              let uu___1 = FStar_List.hd fields in
              match uu___1 with | (f, uu___2) -> FStar_Ident.ns_of_lid f in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu___1 ->
                        match uu___1 with
                        | (g, uu___2) ->
                            let uu___3 = FStar_Ident.string_of_id f in
                            let uu___4 =
                              let uu___5 = FStar_Ident.ident_of_lid g in
                              FStar_Ident.string_of_id uu___5 in
                            uu___3 = uu___4)) in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f]) in
              match found with
              | FStar_Pervasives_Native.Some (uu___1, e) -> (fn, e)
              | FStar_Pervasives_Native.None ->
                  (match xopt with
                   | FStar_Pervasives_Native.None ->
                       let uu___1 =
                         let uu___2 =
                           let uu___3 = FStar_Ident.string_of_id f in
                           let uu___4 =
                             FStar_Ident.string_of_lid
                               record.FStar_Syntax_DsEnv.typename in
                           FStar_Util.format2
                             "Field %s of record type %s is missing" uu___3
                             uu___4 in
                         (FStar_Errors.Fatal_MissingFieldInRecord, uu___2) in
                       FStar_Errors.raise_error uu___1
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
                  let uu___1 =
                    let uu___2 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu___3 ->
                              match uu___3 with
                              | (f, uu___4) ->
                                  let uu___5 =
                                    let uu___6 =
                                      get_field FStar_Pervasives_Native.None
                                        f in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu___6 in
                                  (uu___5, FStar_Parser_AST.Nothing))) in
                    (user_constrname, uu___2) in
                  FStar_Parser_AST.Construct uu___1
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range in
                  let xterm =
                    let uu___1 =
                      let uu___2 = FStar_Ident.lid_of_ids [x] in
                      FStar_Parser_AST.Var uu___2 in
                    let uu___2 = FStar_Ident.range_of_id x in
                    FStar_Parser_AST.mk_term uu___1 uu___2
                      FStar_Parser_AST.Expr in
                  let record1 =
                    let uu___1 =
                      let uu___2 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu___3 ->
                                match uu___3 with
                                | (f, uu___4) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f)) in
                      (FStar_Pervasives_Native.None, uu___2) in
                    FStar_Parser_AST.Record uu___1 in
                  let uu___1 =
                    let uu___2 =
                      let uu___3 =
                        let uu___4 =
                          let uu___5 =
                            let uu___6 = FStar_Ident.range_of_id x in
                            FStar_Parser_AST.mk_pattern
                              (FStar_Parser_AST.PatVar
                                 (x, FStar_Pervasives_Native.None, []))
                              uu___6 in
                          (uu___5, e) in
                        (FStar_Pervasives_Native.None, uu___4) in
                      [uu___3] in
                    (FStar_Parser_AST.NoLetQualifier, uu___2,
                      (FStar_Parser_AST.mk_term record1
                         top.FStar_Parser_AST.range
                         top.FStar_Parser_AST.level)) in
                  FStar_Parser_AST.Let uu___1 in
            let recterm1 =
              FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level in
            let uu___1 = desugar_term_aq env recterm1 in
            (match uu___1 with
             | (e, s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu___2;
                         FStar_Syntax_Syntax.vars = uu___3;_},
                       args)
                      ->
                      let uu___4 =
                        let uu___5 =
                          let uu___6 =
                            let uu___7 =
                              let uu___8 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos in
                              let uu___9 =
                                let uu___10 =
                                  let uu___11 =
                                    let uu___12 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst) in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu___12) in
                                  FStar_Syntax_Syntax.Record_ctor uu___11 in
                                FStar_Pervasives_Native.Some uu___10 in
                              FStar_Syntax_Syntax.fvar uu___8
                                FStar_Syntax_Syntax.delta_constant uu___9 in
                            (uu___7, args) in
                          FStar_Syntax_Syntax.Tm_app uu___6 in
                        FStar_All.pipe_left mk uu___5 in
                      (uu___4, s)
                  | uu___2 -> (e, s)))
        | FStar_Parser_AST.Project (e, f) ->
            let uu___1 =
              FStar_Syntax_DsEnv.fail_or env
                (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f in
            (match uu___1 with
             | (constrname, is_rec) ->
                 let uu___2 = desugar_term_aq env e in
                 (match uu___2 with
                  | (e1, s) ->
                      let projname =
                        let uu___3 = FStar_Ident.ident_of_lid f in
                        FStar_Syntax_Util.mk_field_projector_name_from_ident
                          constrname uu___3 in
                      let qual =
                        if is_rec
                        then
                          let uu___3 =
                            let uu___4 =
                              let uu___5 = FStar_Ident.ident_of_lid f in
                              (constrname, uu___5) in
                            FStar_Syntax_Syntax.Record_projector uu___4 in
                          FStar_Pervasives_Native.Some uu___3
                        else FStar_Pervasives_Native.None in
                      let uu___3 =
                        let uu___4 =
                          let uu___5 =
                            let uu___6 =
                              let uu___7 =
                                FStar_Ident.set_lid_range projname
                                  top.FStar_Parser_AST.range in
                              FStar_Syntax_Syntax.fvar uu___7
                                (FStar_Syntax_Syntax.Delta_equational_at_level
                                   Prims.int_one) qual in
                            let uu___7 =
                              let uu___8 = FStar_Syntax_Syntax.as_arg e1 in
                              [uu___8] in
                            (uu___6, uu___7) in
                          FStar_Syntax_Syntax.Tm_app uu___5 in
                        FStar_All.pipe_left mk uu___4 in
                      (uu___3, s)))
        | FStar_Parser_AST.NamedTyp (n, e) ->
            ((let uu___2 = FStar_Ident.range_of_id n in
              FStar_Errors.log_issue uu___2
                (FStar_Errors.Warning_IgnoredBinding,
                  "This name is being ignored"));
             desugar_term_aq env e)
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e in
            let uu___1 =
              let uu___2 = FStar_Syntax_Subst.compress tm in
              uu___2.FStar_Syntax_Syntax.n in
            (match uu___1 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu___2 =
                   let uu___3 =
                     let uu___4 =
                       let uu___5 = FStar_Syntax_Syntax.lid_of_fv fv in
                       FStar_Ident.string_of_lid uu___5 in
                     FStar_Syntax_Util.exp_string uu___4 in
                   {
                     FStar_Syntax_Syntax.n = (uu___3.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___3.FStar_Syntax_Syntax.vars)
                   } in
                 (uu___2, noaqs)
             | uu___2 ->
                 let uu___3 =
                   let uu___4 =
                     let uu___5 = FStar_Syntax_Print.term_to_string tm in
                     Prims.op_Hat "VQuote, expected an fvar, got: " uu___5 in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu___4) in
                 FStar_Errors.raise_error uu___3 top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e, FStar_Parser_AST.Static) ->
            let uu___1 = desugar_term_aq env e in
            (match uu___1 with
             | (tm, vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   } in
                 let uu___2 =
                   FStar_All.pipe_left mk
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi)) in
                 (uu___2, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun in
            let uu___1 = FStar_Syntax_Syntax.bv_to_name bv in
            let uu___2 =
              let uu___3 = let uu___4 = desugar_term env e in (bv, uu___4) in
              [uu___3] in
            (uu___1, uu___2)
        | FStar_Parser_AST.Quote (e, FStar_Parser_AST.Dynamic) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              } in
            let uu___1 =
              let uu___2 =
                let uu___3 = let uu___4 = desugar_term env e in (uu___4, qi) in
                FStar_Syntax_Syntax.Tm_quoted uu___3 in
              FStar_All.pipe_left mk uu___2 in
            (uu___1, noaqs)
        | FStar_Parser_AST.CalcProof (rel, init_expr, steps) ->
            let is_impl rel1 =
              let is_impl_t t =
                match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.imp_lid
                | uu___1 -> false in
              let uu___1 =
                let uu___2 = unparen rel1 in uu___2.FStar_Parser_AST.tm in
              match uu___1 with
              | FStar_Parser_AST.Op (id, uu___2) ->
                  let uu___3 = op_as_term env (Prims.of_int (2)) id in
                  (match uu___3 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None -> false)
              | FStar_Parser_AST.Var lid ->
                  let uu___2 = desugar_name' (fun x -> x) env true lid in
                  (match uu___2 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None -> false)
              | FStar_Parser_AST.Tvar id ->
                  let uu___2 = FStar_Syntax_DsEnv.try_lookup_id env id in
                  (match uu___2 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None -> false)
              | uu___2 -> false in
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
                   (FStar_Parser_AST.PatVar
                      (x, FStar_Pervasives_Native.None, []))
                   rel1.FStar_Parser_AST.range;
                FStar_Parser_AST.mk_pattern
                  (FStar_Parser_AST.PatVar
                     (y, FStar_Pervasives_Native.None, []))
                  rel1.FStar_Parser_AST.range] in
              let uu___1 =
                let uu___2 =
                  let uu___3 =
                    let uu___4 =
                      let uu___5 =
                        let uu___6 =
                          FStar_Parser_AST.mkApp rel1
                            [(xt, FStar_Parser_AST.Nothing);
                            (yt, FStar_Parser_AST.Nothing)]
                            rel1.FStar_Parser_AST.range in
                        let uu___7 =
                          let uu___8 =
                            let uu___9 = FStar_Ident.lid_of_str "Type0" in
                            FStar_Parser_AST.Name uu___9 in
                          FStar_Parser_AST.mk_term uu___8
                            rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr in
                        (uu___6, uu___7, FStar_Pervasives_Native.None) in
                      FStar_Parser_AST.Ascribed uu___5 in
                    FStar_Parser_AST.mk_term uu___4
                      rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr in
                  (pats, uu___3) in
                FStar_Parser_AST.Abs uu___2 in
              FStar_Parser_AST.mk_term uu___1 rel1.FStar_Parser_AST.range
                FStar_Parser_AST.Expr in
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
              let uu___1 = FStar_List.last steps in
              match uu___1 with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.CalcStep
                  (uu___2, uu___3, last_expr1)) -> last_expr1
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
            let uu___1 =
              FStar_List.fold_left
                (fun uu___2 ->
                   fun uu___3 ->
                     match (uu___2, uu___3) with
                     | ((e1, prev), FStar_Parser_AST.CalcStep
                        (rel2, just, next_expr)) ->
                         let just1 =
                           let uu___4 = is_impl rel2 in
                           if uu___4
                           then
                             let uu___5 =
                               let uu___6 =
                                 let uu___7 = FStar_Parser_AST.thunk just in
                                 (uu___7, FStar_Parser_AST.Nothing) in
                               [uu___6] in
                             FStar_Parser_AST.mkApp
                               (push_impl just.FStar_Parser_AST.range) uu___5
                               just.FStar_Parser_AST.range
                           else just in
                         let pf =
                           let uu___4 =
                             let uu___5 =
                               let uu___6 =
                                 let uu___7 =
                                   let uu___8 =
                                     let uu___9 = eta_and_annot rel2 in
                                     (uu___9, FStar_Parser_AST.Nothing) in
                                   let uu___9 =
                                     let uu___10 =
                                       let uu___11 =
                                         let uu___12 =
                                           FStar_Parser_AST.thunk e1 in
                                         (uu___12, FStar_Parser_AST.Nothing) in
                                       let uu___12 =
                                         let uu___13 =
                                           let uu___14 =
                                             FStar_Parser_AST.thunk just1 in
                                           (uu___14,
                                             FStar_Parser_AST.Nothing) in
                                         [uu___13] in
                                       uu___11 :: uu___12 in
                                     (next_expr, FStar_Parser_AST.Nothing) ::
                                       uu___10 in
                                   uu___8 :: uu___9 in
                                 (prev, FStar_Parser_AST.Hash) :: uu___7 in
                               (init_expr, FStar_Parser_AST.Hash) :: uu___6 in
                             ((wild rel2.FStar_Parser_AST.range),
                               FStar_Parser_AST.Hash) :: uu___5 in
                           FStar_Parser_AST.mkApp
                             (step rel2.FStar_Parser_AST.range) uu___4
                             FStar_Range.dummyRange in
                         (pf, next_expr)) (e, init_expr) steps in
            (match uu___1 with
             | (e1, uu___2) ->
                 let e2 =
                   let uu___3 =
                     let uu___4 =
                       let uu___5 =
                         let uu___6 =
                           let uu___7 = FStar_Parser_AST.thunk e1 in
                           (uu___7, FStar_Parser_AST.Nothing) in
                         [uu___6] in
                       (last_expr, FStar_Parser_AST.Hash) :: uu___5 in
                     (init_expr, FStar_Parser_AST.Hash) :: uu___4 in
                   FStar_Parser_AST.mkApp finish uu___3
                     top.FStar_Parser_AST.range in
                 desugar_term_maybe_top top_level env e2)
        | uu___1 when top.FStar_Parser_AST.level = FStar_Parser_AST.Formula
            -> let uu___2 = desugar_formula env top in (uu___2, noaqs)
        | uu___1 ->
            let uu___2 =
              let uu___3 =
                let uu___4 = FStar_Parser_AST.term_to_string top in
                Prims.op_Hat "Unexpected term: " uu___4 in
              (FStar_Errors.Fatal_UnexpectedTerm, uu___3) in
            FStar_Errors.raise_error uu___2 top.FStar_Parser_AST.range
and (desugar_ascription :
  env_t ->
    FStar_Parser_AST.term ->
      FStar_Parser_AST.term FStar_Pervasives_Native.option ->
        (((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
          FStar_Pervasives.either * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option) *
          (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax) Prims.list))
  =
  fun env ->
    fun t ->
      fun tac_opt ->
        let uu___ =
          let uu___1 = is_comp_type env t in
          if uu___1
          then
            let comp = desugar_comp t.FStar_Parser_AST.range true env t in
            ((FStar_Pervasives.Inr comp), [])
          else
            (let uu___3 = desugar_term_aq env t in
             match uu___3 with | (tm, aq) -> ((FStar_Pervasives.Inl tm), aq)) in
        match uu___ with
        | (annot, aq0) ->
            let uu___1 =
              let uu___2 = FStar_Util.map_opt tac_opt (desugar_term env) in
              (annot, uu___2) in
            (uu___1, aq0)
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
           (fun uu___ ->
              match uu___ with
              | (a, imp) ->
                  let uu___1 = desugar_term env a in arg_withimp_e imp uu___1))
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
          let is_requires uu___ =
            match uu___ with
            | (t1, uu___1) ->
                let uu___2 =
                  let uu___3 = unparen t1 in uu___3.FStar_Parser_AST.tm in
                (match uu___2 with
                 | FStar_Parser_AST.Requires uu___3 -> true
                 | uu___3 -> false) in
          let is_ensures uu___ =
            match uu___ with
            | (t1, uu___1) ->
                let uu___2 =
                  let uu___3 = unparen t1 in uu___3.FStar_Parser_AST.tm in
                (match uu___2 with
                 | FStar_Parser_AST.Ensures uu___3 -> true
                 | uu___3 -> false) in
          let is_decreases uu___ =
            match uu___ with
            | (t1, uu___1) ->
                let uu___2 =
                  let uu___3 = unparen t1 in uu___3.FStar_Parser_AST.tm in
                (match uu___2 with
                 | FStar_Parser_AST.Decreases uu___3 -> true
                 | uu___3 -> false) in
          let is_smt_pat uu___ =
            match uu___ with
            | (t1, uu___1) ->
                let uu___2 =
                  let uu___3 = unparen t1 in uu___3.FStar_Parser_AST.tm in
                (match uu___2 with
                 | FStar_Parser_AST.Construct
                     (cons,
                      ({
                         FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                           (smtpat, uu___3);
                         FStar_Parser_AST.range = uu___4;
                         FStar_Parser_AST.level = uu___5;_},
                       uu___6)::uu___7::[])
                     ->
                     (FStar_Ident.lid_equals cons FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s ->
                             let uu___8 = FStar_Ident.string_of_lid smtpat in
                             uu___8 = s) ["SMTPat"; "SMTPatT"; "SMTPatOr"])
                 | FStar_Parser_AST.Construct
                     (cons,
                      ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var smtpat;
                         FStar_Parser_AST.range = uu___3;
                         FStar_Parser_AST.level = uu___4;_},
                       uu___5)::uu___6::[])
                     ->
                     (FStar_Ident.lid_equals cons FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s ->
                             let uu___7 = FStar_Ident.string_of_lid smtpat in
                             uu___7 = s) ["smt_pat"; "smt_pat_or"])
                 | uu___3 -> false) in
          let pre_process_comp_typ t1 =
            let uu___ = head_and_args t1 in
            match uu___ with
            | (head, args) ->
                (match head.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Name lemma when
                     let uu___1 =
                       let uu___2 = FStar_Ident.ident_of_lid lemma in
                       FStar_Ident.string_of_id uu___2 in
                     uu___1 = "Lemma" ->
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
                     let thunk_ens uu___1 =
                       match uu___1 with
                       | (e, i) ->
                           let uu___2 = FStar_Parser_AST.thunk e in
                           (uu___2, i) in
                     let fail_lemma uu___1 =
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
                           let uu___1 =
                             let uu___2 =
                               let uu___3 = thunk_ens ens in
                               [uu___3; nil_pat] in
                             req_true :: uu___2 in
                           unit_tm :: uu___1
                       | req::ens::[] when
                           (is_requires req) && (is_ensures ens) ->
                           let uu___1 =
                             let uu___2 =
                               let uu___3 = thunk_ens ens in
                               [uu___3; nil_pat] in
                             req :: uu___2 in
                           unit_tm :: uu___1
                       | ens::smtpat::[] when
                           (((let uu___1 = is_requires ens in
                              Prims.op_Negation uu___1) &&
                               (let uu___1 = is_smt_pat ens in
                                Prims.op_Negation uu___1))
                              &&
                              (let uu___1 = is_decreases ens in
                               Prims.op_Negation uu___1))
                             && (is_smt_pat smtpat)
                           ->
                           let uu___1 =
                             let uu___2 =
                               let uu___3 = thunk_ens ens in [uu___3; smtpat] in
                             req_true :: uu___2 in
                           unit_tm :: uu___1
                       | ens::dec::[] when
                           (is_ensures ens) && (is_decreases dec) ->
                           let uu___1 =
                             let uu___2 =
                               let uu___3 = thunk_ens ens in
                               [uu___3; nil_pat; dec] in
                             req_true :: uu___2 in
                           unit_tm :: uu___1
                       | ens::dec::smtpat::[] when
                           ((is_ensures ens) && (is_decreases dec)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu___1 =
                             let uu___2 =
                               let uu___3 = thunk_ens ens in
                               [uu___3; smtpat; dec] in
                             req_true :: uu___2 in
                           unit_tm :: uu___1
                       | req::ens::dec::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_decreases dec)
                           ->
                           let uu___1 =
                             let uu___2 =
                               let uu___3 = thunk_ens ens in
                               [uu___3; nil_pat; dec] in
                             req :: uu___2 in
                           unit_tm :: uu___1
                       | req::ens::smtpat::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu___1 =
                             let uu___2 =
                               let uu___3 = thunk_ens ens in [uu___3; smtpat] in
                             req :: uu___2 in
                           unit_tm :: uu___1
                       | req::ens::dec::smtpat::[] when
                           (((is_requires req) && (is_ensures ens)) &&
                              (is_smt_pat smtpat))
                             && (is_decreases dec)
                           ->
                           let uu___1 =
                             let uu___2 =
                               let uu___3 = thunk_ens ens in
                               [uu___3; dec; smtpat] in
                             req :: uu___2 in
                           unit_tm :: uu___1
                       | _other -> fail_lemma () in
                     let head_and_attributes =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) lemma in
                     (head_and_attributes, args1)
                 | FStar_Parser_AST.Name l when
                     FStar_Syntax_DsEnv.is_effect_name env l ->
                     let uu___1 =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) l in
                     (uu___1, args)
                 | FStar_Parser_AST.Name l when
                     (let uu___1 = FStar_Syntax_DsEnv.current_module env in
                      FStar_Ident.lid_equals uu___1
                        FStar_Parser_Const.prims_lid)
                       &&
                       (let uu___1 =
                          let uu___2 = FStar_Ident.ident_of_lid l in
                          FStar_Ident.string_of_id uu___2 in
                        uu___1 = "Tot")
                     ->
                     let uu___1 =
                       let uu___2 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head.FStar_Parser_AST.range in
                       (uu___2, []) in
                     (uu___1, args)
                 | FStar_Parser_AST.Name l when
                     (let uu___1 = FStar_Syntax_DsEnv.current_module env in
                      FStar_Ident.lid_equals uu___1
                        FStar_Parser_Const.prims_lid)
                       &&
                       (let uu___1 =
                          let uu___2 = FStar_Ident.ident_of_lid l in
                          FStar_Ident.string_of_id uu___2 in
                        uu___1 = "GTot")
                     ->
                     let uu___1 =
                       let uu___2 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_GTot_lid
                           head.FStar_Parser_AST.range in
                       (uu___2, []) in
                     (uu___1, args)
                 | FStar_Parser_AST.Name l when
                     ((let uu___1 =
                         let uu___2 = FStar_Ident.ident_of_lid l in
                         FStar_Ident.string_of_id uu___2 in
                       uu___1 = "Type") ||
                        (let uu___1 =
                           let uu___2 = FStar_Ident.ident_of_lid l in
                           FStar_Ident.string_of_id uu___2 in
                         uu___1 = "Type0"))
                       ||
                       (let uu___1 =
                          let uu___2 = FStar_Ident.ident_of_lid l in
                          FStar_Ident.string_of_id uu___2 in
                        uu___1 = "Effect")
                     ->
                     let uu___1 =
                       let uu___2 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head.FStar_Parser_AST.range in
                       (uu___2, []) in
                     (uu___1, [(t1, FStar_Parser_AST.Nothing)])
                 | uu___1 when allow_type_promotion ->
                     let default_effect =
                       let uu___2 = FStar_Options.ml_ish () in
                       if uu___2
                       then FStar_Parser_Const.effect_ML_lid
                       else
                         ((let uu___5 = FStar_Options.warn_default_effects () in
                           if uu___5
                           then
                             FStar_Errors.log_issue
                               head.FStar_Parser_AST.range
                               (FStar_Errors.Warning_UseDefaultEffect,
                                 "Using default effect Tot")
                           else ());
                          FStar_Parser_Const.effect_Tot_lid) in
                     let uu___2 =
                       let uu___3 =
                         FStar_Ident.set_lid_range default_effect
                           head.FStar_Parser_AST.range in
                       (uu___3, []) in
                     (uu___2, [(t1, FStar_Parser_AST.Nothing)])
                 | uu___1 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_EffectNotFound,
                         "Expected an effect constructor")
                       t1.FStar_Parser_AST.range) in
          let uu___ = pre_process_comp_typ t in
          match uu___ with
          | ((eff, cattributes), args) ->
              (if (FStar_List.length args) = Prims.int_zero
               then
                 (let uu___2 =
                    let uu___3 =
                      let uu___4 = FStar_Syntax_Print.lid_to_string eff in
                      FStar_Util.format1 "Not enough args to effect %s"
                        uu___4 in
                    (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu___3) in
                  fail uu___2)
               else ();
               (let is_universe uu___2 =
                  match uu___2 with
                  | (uu___3, imp) -> imp = FStar_Parser_AST.UnivApp in
                let uu___2 = FStar_Util.take is_universe args in
                match uu___2 with
                | (universes, args1) ->
                    let universes1 =
                      FStar_List.map
                        (fun uu___3 ->
                           match uu___3 with | (u, imp) -> desugar_universe u)
                        universes in
                    let uu___3 =
                      let uu___4 = FStar_List.hd args1 in
                      let uu___5 = FStar_List.tl args1 in (uu___4, uu___5) in
                    (match uu___3 with
                     | (result_arg, rest) ->
                         let result_typ =
                           desugar_typ env
                             (FStar_Pervasives_Native.fst result_arg) in
                         let uu___4 =
                           let is_decrease t1 =
                             let uu___5 =
                               let uu___6 =
                                 unparen (FStar_Pervasives_Native.fst t1) in
                               uu___6.FStar_Parser_AST.tm in
                             match uu___5 with
                             | FStar_Parser_AST.Decreases uu___6 -> true
                             | uu___6 -> false in
                           FStar_All.pipe_right rest
                             (FStar_List.partition is_decrease) in
                         (match uu___4 with
                          | (dec, rest1) ->
                              let rest2 = desugar_args env rest1 in
                              let decreases_clause =
                                FStar_All.pipe_right dec
                                  (FStar_List.map
                                     (fun t1 ->
                                        let uu___5 =
                                          let uu___6 =
                                            unparen
                                              (FStar_Pervasives_Native.fst t1) in
                                          uu___6.FStar_Parser_AST.tm in
                                        match uu___5 with
                                        | FStar_Parser_AST.Decreases
                                            (t2, uu___6) ->
                                            let dec_order =
                                              let t3 = unparen t2 in
                                              match t3.FStar_Parser_AST.tm
                                              with
                                              | FStar_Parser_AST.LexList l ->
                                                  let uu___7 =
                                                    FStar_All.pipe_right l
                                                      (FStar_List.map
                                                         (desugar_term env)) in
                                                  FStar_All.pipe_right uu___7
                                                    (fun uu___8 ->
                                                       FStar_Syntax_Syntax.Decreases_lex
                                                         uu___8)
                                              | FStar_Parser_AST.WFOrder
                                                  (t11, t21) ->
                                                  let uu___7 =
                                                    let uu___8 =
                                                      desugar_term env t11 in
                                                    let uu___9 =
                                                      desugar_term env t21 in
                                                    (uu___8, uu___9) in
                                                  FStar_All.pipe_right uu___7
                                                    (fun uu___8 ->
                                                       FStar_Syntax_Syntax.Decreases_wf
                                                         uu___8)
                                              | uu___7 ->
                                                  let uu___8 =
                                                    let uu___9 =
                                                      desugar_term env t3 in
                                                    [uu___9] in
                                                  FStar_All.pipe_right uu___8
                                                    (fun uu___9 ->
                                                       FStar_Syntax_Syntax.Decreases_lex
                                                         uu___9) in
                                            FStar_Syntax_Syntax.DECREASES
                                              dec_order
                                        | uu___6 ->
                                            fail
                                              (FStar_Errors.Fatal_UnexpectedComputationTypeForLetRec,
                                                "Unexpected decreases clause"))) in
                              let no_additional_args =
                                let is_empty l =
                                  match l with | [] -> true | uu___5 -> false in
                                (((is_empty decreases_clause) &&
                                    (is_empty rest2))
                                   && (is_empty cattributes))
                                  && (is_empty universes1) in
                              let uu___5 =
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_Tot_lid) in
                              if uu___5
                              then FStar_Syntax_Syntax.mk_Total result_typ
                              else
                                (let uu___7 =
                                   no_additional_args &&
                                     (FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_GTot_lid) in
                                 if uu___7
                                 then
                                   FStar_Syntax_Syntax.mk_GTotal result_typ
                                 else
                                   (let flags =
                                      let uu___9 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid in
                                      if uu___9
                                      then [FStar_Syntax_Syntax.LEMMA]
                                      else
                                        (let uu___11 =
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_Tot_lid in
                                         if uu___11
                                         then [FStar_Syntax_Syntax.TOTAL]
                                         else
                                           (let uu___13 =
                                              FStar_Ident.lid_equals eff
                                                FStar_Parser_Const.effect_ML_lid in
                                            if uu___13
                                            then
                                              [FStar_Syntax_Syntax.MLEFFECT]
                                            else
                                              (let uu___15 =
                                                 FStar_Ident.lid_equals eff
                                                   FStar_Parser_Const.effect_GTot_lid in
                                               if uu___15
                                               then
                                                 [FStar_Syntax_Syntax.SOMETRIVIAL]
                                               else []))) in
                                    let flags1 =
                                      FStar_List.append flags cattributes in
                                    let rest3 =
                                      let uu___9 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid in
                                      if uu___9
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
                                                    let uu___10 =
                                                      FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos in
                                                    FStar_Syntax_Syntax.fvar
                                                      uu___10
                                                      FStar_Syntax_Syntax.delta_constant
                                                      FStar_Pervasives_Native.None in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    nil
                                                    [(pattern,
                                                       (FStar_Pervasives_Native.Some
                                                          FStar_Syntax_Syntax.imp_tag))]
                                                    pat.FStar_Syntax_Syntax.pos
                                              | uu___10 -> pat in
                                            let uu___10 =
                                              let uu___11 =
                                                let uu___12 =
                                                  let uu___13 =
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (pat1,
                                                           (FStar_Syntax_Syntax.Meta_desugared
                                                              FStar_Syntax_Syntax.Meta_smt_pat)))
                                                      pat1.FStar_Syntax_Syntax.pos in
                                                  (uu___13, aq) in
                                                [uu___12] in
                                              ens :: uu___11 in
                                            req :: uu___10
                                        | uu___10 -> rest2
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
        let uu___ = t in
        {
          FStar_Syntax_Syntax.n = (uu___.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars = (uu___.FStar_Syntax_Syntax.vars)
        } in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___ = b in
             {
               FStar_Parser_AST.b = (uu___.FStar_Parser_AST.b);
               FStar_Parser_AST.brange = (uu___.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual = (uu___.FStar_Parser_AST.aqual);
               FStar_Parser_AST.battributes =
                 (uu___.FStar_Parser_AST.battributes)
             }) in
        let with_pats env1 uu___ body1 =
          match uu___ with
          | (names, pats1) ->
              (match (names, pats1) with
               | ([], []) -> body1
               | ([], uu___1::uu___2) ->
                   failwith
                     "Impossible: Annotated pattern without binders in scope"
               | uu___1 ->
                   let names1 =
                     FStar_All.pipe_right names
                       (FStar_List.map
                          (fun i ->
                             let uu___2 =
                               FStar_Syntax_DsEnv.fail_or2
                                 (FStar_Syntax_DsEnv.try_lookup_id env1) i in
                             let uu___3 = FStar_Ident.range_of_id i in
                             {
                               FStar_Syntax_Syntax.n =
                                 (uu___2.FStar_Syntax_Syntax.n);
                               FStar_Syntax_Syntax.pos = uu___3;
                               FStar_Syntax_Syntax.vars =
                                 (uu___2.FStar_Syntax_Syntax.vars)
                             })) in
                   let pats2 =
                     FStar_All.pipe_right pats1
                       (FStar_List.map
                          (fun es ->
                             FStar_All.pipe_right es
                               (FStar_List.map
                                  (fun e ->
                                     let uu___2 = desugar_term env1 e in
                                     FStar_All.pipe_left
                                       (arg_withimp_t
                                          FStar_Parser_AST.Nothing) uu___2)))) in
                   mk
                     (FStar_Syntax_Syntax.Tm_meta
                        (body1,
                          (FStar_Syntax_Syntax.Meta_pattern (names1, pats2))))) in
        match tk with
        | (FStar_Pervasives_Native.Some a, k, uu___) ->
            let uu___1 = FStar_Syntax_DsEnv.push_bv env a in
            (match uu___1 with
             | (env1, a1) ->
                 let a2 =
                   let uu___2 = a1 in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___2.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___2.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   } in
                 let body1 = desugar_formula env1 body in
                 let body2 = with_pats env1 pats body1 in
                 let body3 =
                   let uu___2 =
                     let uu___3 =
                       let uu___4 = FStar_Syntax_Syntax.mk_binder a2 in
                       [uu___4] in
                     no_annot_abs uu___3 body2 in
                   FStar_All.pipe_left setpos uu___2 in
                 let uu___2 =
                   let uu___3 =
                     let uu___4 =
                       let uu___5 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange in
                       FStar_Syntax_Syntax.fvar uu___5
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            Prims.int_one) FStar_Pervasives_Native.None in
                     let uu___5 =
                       let uu___6 = FStar_Syntax_Syntax.as_arg body3 in
                       [uu___6] in
                     (uu___4, uu___5) in
                   FStar_Syntax_Syntax.Tm_app uu___3 in
                 FStar_All.pipe_left mk uu___2)
        | uu___ -> failwith "impossible" in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest in
            let body1 =
              let uu___ = q (rest, pats, body) in
              let uu___1 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range in
              FStar_Parser_AST.mk_term uu___ uu___1 FStar_Parser_AST.Formula in
            let uu___ = q ([b], ([], []), body1) in
            FStar_Parser_AST.mk_term uu___ f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu___ -> failwith "impossible" in
      let uu___ = let uu___1 = unparen f in uu___1.FStar_Parser_AST.tm in
      match uu___ with
      | FStar_Parser_AST.Labeled (f1, l, p) ->
          let f2 = desugar_formula env f1 in
          FStar_All.pipe_left mk
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([], uu___1, uu___2) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([], uu___1, uu___2) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3, pats, body) ->
          let binders = _1 :: _2 :: _3 in
          let uu___1 =
            push_quant (fun x -> FStar_Parser_AST.QForall x) binders pats
              body in
          desugar_formula env uu___1
      | FStar_Parser_AST.QExists (_1::_2::_3, pats, body) ->
          let binders = _1 :: _2 :: _3 in
          let uu___1 =
            push_quant (fun x -> FStar_Parser_AST.QExists x) binders pats
              body in
          desugar_formula env uu___1
      | FStar_Parser_AST.QForall (b::[], pats, body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[], pats, body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu___1 -> desugar_term env f
and (desugar_binder :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Ident.ident FStar_Pervasives_Native.option *
        FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list))
  =
  fun env ->
    fun b ->
      let attrs =
        FStar_All.pipe_right b.FStar_Parser_AST.battributes
          (FStar_List.map (desugar_term env)) in
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.TAnnotated (x, t) ->
          let uu___ = desugar_typ env t in
          ((FStar_Pervasives_Native.Some x), uu___, attrs)
      | FStar_Parser_AST.Annotated (x, t) ->
          let uu___ = desugar_typ env t in
          ((FStar_Pervasives_Native.Some x), uu___, attrs)
      | FStar_Parser_AST.TVariable x ->
          let uu___ =
            let uu___1 = FStar_Ident.range_of_id x in
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              uu___1 in
          ((FStar_Pervasives_Native.Some x), uu___, attrs)
      | FStar_Parser_AST.NoName t ->
          let uu___ = desugar_typ env t in
          (FStar_Pervasives_Native.None, uu___, attrs)
      | FStar_Parser_AST.Variable x ->
          let uu___ = let uu___1 = FStar_Ident.range_of_id x in tun_r uu___1 in
          ((FStar_Pervasives_Native.Some x), uu___, attrs)
and (as_binder :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      (FStar_Ident.ident FStar_Pervasives_Native.option *
        FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.attribute Prims.list)
        -> (FStar_Syntax_Syntax.binder * FStar_Syntax_DsEnv.env))
  =
  fun env ->
    fun imp ->
      fun uu___ ->
        match uu___ with
        | (FStar_Pervasives_Native.None, k, attrs) ->
            let uu___1 =
              let uu___2 = FStar_Syntax_Syntax.null_bv k in
              let uu___3 = trans_aqual env imp in
              FStar_Syntax_Syntax.mk_binder_with_attrs uu___2 uu___3 attrs in
            (uu___1, env)
        | (FStar_Pervasives_Native.Some a, k, attrs) ->
            let uu___1 = FStar_Syntax_DsEnv.push_bv env a in
            (match uu___1 with
             | (env1, a1) ->
                 let uu___2 =
                   let uu___3 = trans_aqual env1 imp in
                   FStar_Syntax_Syntax.mk_binder_with_attrs
                     (let uu___4 = a1 in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___4.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___4.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = k
                      }) uu___3 attrs in
                 (uu___2, env1))
and (trans_aqual :
  env_t ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env ->
    fun uu___ ->
      match uu___ with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu___1 =
            let uu___2 = desugar_term env t in
            FStar_Syntax_Syntax.Meta uu___2 in
          FStar_Pervasives_Native.Some uu___1
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * FStar_Syntax_Syntax.binders))
  =
  fun env ->
    fun bs ->
      let uu___ =
        FStar_List.fold_left
          (fun uu___1 ->
             fun b ->
               match uu___1 with
               | (env1, out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___2 = b in
                        {
                          FStar_Parser_AST.b = (uu___2.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___2.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___2.FStar_Parser_AST.aqual);
                          FStar_Parser_AST.battributes =
                            (uu___2.FStar_Parser_AST.battributes)
                        }) in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a, k, attrs) ->
                        let uu___2 = FStar_Syntax_DsEnv.push_bv env1 a in
                        (match uu___2 with
                         | (env2, a1) ->
                             let a2 =
                               let uu___3 = a1 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               } in
                             let uu___3 =
                               let uu___4 =
                                 let uu___5 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual in
                                 FStar_Syntax_Syntax.mk_binder_with_attrs a2
                                   uu___5 attrs in
                               uu___4 :: out in
                             (env2, uu___3))
                    | uu___2 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs in
      match uu___ with | (env1, tpars) -> (env1, (FStar_List.rev tpars))
let (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun env ->
    fun cattributes ->
      let desugar_attribute t =
        let uu___ = let uu___1 = unparen t in uu___1.FStar_Parser_AST.tm in
        match uu___ with
        | FStar_Parser_AST.Var lid when
            let uu___1 = FStar_Ident.string_of_lid lid in uu___1 = "cps" ->
            FStar_Syntax_Syntax.CPS
        | uu___1 ->
            let uu___2 =
              let uu___3 =
                let uu___4 = FStar_Parser_AST.term_to_string t in
                Prims.op_Hat "Unknown attribute " uu___4 in
              (FStar_Errors.Fatal_UnknownAttribute, uu___3) in
            FStar_Errors.raise_error uu___2 t.FStar_Parser_AST.range in
      FStar_List.map desugar_attribute cattributes
let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x, uu___) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x, uu___) -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu___ -> FStar_Pervasives_Native.None
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs ->
    FStar_List.collect
      (fun b ->
         let uu___ = binder_ident b in FStar_Common.list_of_option uu___) bs
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
               (fun uu___ ->
                  match uu___ with
                  | FStar_Syntax_Syntax.NoExtract -> true
                  | FStar_Syntax_Syntax.Private -> true
                  | uu___1 -> false)) in
        let quals2 q =
          let uu___ =
            (let uu___1 = FStar_Syntax_DsEnv.iface env in
             Prims.op_Negation uu___1) ||
              (FStar_Syntax_DsEnv.admitted_iface env) in
          if uu___
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1 in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d in
                let uu___ = FStar_Ident.range_of_lid disc_name in
                let uu___1 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d] in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu___;
                  FStar_Syntax_Syntax.sigquals = uu___1;
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
            let uu___ =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i ->
                      fun fld ->
                        let x = fld.FStar_Syntax_Syntax.binder_bv in
                        let field_name =
                          FStar_Syntax_Util.mk_field_projector_name lid x i in
                        let only_decl =
                          ((let uu___1 =
                              FStar_Syntax_DsEnv.current_module env in
                            FStar_Ident.lid_equals
                              FStar_Parser_Const.prims_lid uu___1)
                             || (fvq <> FStar_Syntax_Syntax.Data_ctor))
                            ||
                            (let uu___1 =
                               let uu___2 =
                                 FStar_Syntax_DsEnv.current_module env in
                               FStar_Ident.string_of_lid uu___2 in
                             FStar_Options.dont_gen_projectors uu___1) in
                        let no_decl =
                          FStar_Syntax_Syntax.is_type
                            x.FStar_Syntax_Syntax.sort in
                        let quals q =
                          if only_decl
                          then FStar_Syntax_Syntax.Assumption :: q
                          else q in
                        let quals1 =
                          let iquals1 =
                            FStar_All.pipe_right iquals
                              (FStar_List.filter
                                 (fun uu___1 ->
                                    match uu___1 with
                                    | FStar_Syntax_Syntax.NoExtract -> true
                                    | FStar_Syntax_Syntax.Private -> true
                                    | uu___2 -> false)) in
                          quals (FStar_Syntax_Syntax.OnlyName ::
                            (FStar_Syntax_Syntax.Projector
                               (lid, (x.FStar_Syntax_Syntax.ppname))) ::
                            iquals1) in
                        let decl =
                          let uu___1 = FStar_Ident.range_of_lid field_name in
                          {
                            FStar_Syntax_Syntax.sigel =
                              (FStar_Syntax_Syntax.Sig_declare_typ
                                 (field_name, [], FStar_Syntax_Syntax.tun));
                            FStar_Syntax_Syntax.sigrng = uu___1;
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
                             FStar_Syntax_Syntax.Delta_equational_at_level
                               Prims.int_one in
                           let lb =
                             let uu___2 =
                               let uu___3 =
                                 FStar_Syntax_Syntax.lid_as_fv field_name dd
                                   FStar_Pervasives_Native.None in
                               FStar_Pervasives.Inr uu___3 in
                             {
                               FStar_Syntax_Syntax.lbname = uu___2;
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
                             let uu___2 =
                               let uu___3 =
                                 let uu___4 =
                                   let uu___5 =
                                     let uu___6 =
                                       FStar_All.pipe_right
                                         lb.FStar_Syntax_Syntax.lbname
                                         FStar_Util.right in
                                     FStar_All.pipe_right uu___6
                                       (fun fv ->
                                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                   [uu___5] in
                                 ((false, [lb]), uu___4) in
                               FStar_Syntax_Syntax.Sig_let uu___3 in
                             {
                               FStar_Syntax_Syntax.sigel = uu___2;
                               FStar_Syntax_Syntax.sigrng = p;
                               FStar_Syntax_Syntax.sigquals = quals1;
                               FStar_Syntax_Syntax.sigmeta =
                                 FStar_Syntax_Syntax.default_sigmeta;
                               FStar_Syntax_Syntax.sigattrs = [];
                               FStar_Syntax_Syntax.sigopts =
                                 FStar_Pervasives_Native.None
                             } in
                           if no_decl then [impl] else [decl; impl]))) in
            FStar_All.pipe_right uu___ FStar_List.flatten
let (mk_data_projector_names :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_DsEnv.env ->
      FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun iquals ->
    fun env ->
      fun se ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_datacon (lid, uu___, t, uu___1, n, uu___2)
            ->
            let uu___3 = FStar_Syntax_Util.arrow_formals t in
            (match uu___3 with
             | (formals, uu___4) ->
                 (match formals with
                  | [] -> []
                  | uu___5 ->
                      let filter_records uu___6 =
                        match uu___6 with
                        | FStar_Syntax_Syntax.RecordConstructor (uu___7, fns)
                            ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu___7 -> FStar_Pervasives_Native.None in
                      let fv_qual =
                        let uu___6 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records in
                        match uu___6 with
                        | FStar_Pervasives_Native.None ->
                            FStar_Syntax_Syntax.Data_ctor
                        | FStar_Pervasives_Native.Some q -> q in
                      let uu___6 = FStar_Util.first_N n formals in
                      (match uu___6 with
                       | (uu___7, rest) ->
                           mk_indexed_projector_names iquals fv_qual env lid
                             rest)))
        | uu___ -> []
let (mk_typ_abbrev :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.decl ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.univ_name Prims.list ->
          FStar_Syntax_Syntax.binder Prims.list ->
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
                        let uu___ =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env lid in
                        FStar_All.pipe_right uu___
                          FStar_Pervasives_Native.snd in
                      let dd = FStar_Syntax_Util.incr_delta_qualifier t in
                      let lb =
                        let uu___ =
                          let uu___1 =
                            FStar_Syntax_Syntax.lid_as_fv lid dd
                              FStar_Pervasives_Native.None in
                          FStar_Pervasives.Inr uu___1 in
                        let uu___1 =
                          if FStar_Util.is_some kopt
                          then
                            let uu___2 =
                              let uu___3 =
                                FStar_All.pipe_right kopt FStar_Util.must in
                              FStar_Syntax_Syntax.mk_Total uu___3 in
                            FStar_Syntax_Util.arrow typars uu___2
                          else FStar_Syntax_Syntax.tun in
                        let uu___2 = no_annot_abs typars t in
                        {
                          FStar_Syntax_Syntax.lbname = uu___;
                          FStar_Syntax_Syntax.lbunivs = uvs;
                          FStar_Syntax_Syntax.lbtyp = uu___1;
                          FStar_Syntax_Syntax.lbeff =
                            FStar_Parser_Const.effect_Tot_lid;
                          FStar_Syntax_Syntax.lbdef = uu___2;
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
          let tycon_id uu___ =
            match uu___ with
            | FStar_Parser_AST.TyconAbstract (id, uu___1, uu___2) -> id
            | FStar_Parser_AST.TyconAbbrev (id, uu___1, uu___2, uu___3) -> id
            | FStar_Parser_AST.TyconRecord (id, uu___1, uu___2, uu___3) -> id
            | FStar_Parser_AST.TyconVariant (id, uu___1, uu___2, uu___3) ->
                id in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x, uu___) ->
                let uu___1 =
                  let uu___2 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu___2 in
                let uu___2 = FStar_Ident.range_of_id x in
                FStar_Parser_AST.mk_term uu___1 uu___2 FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu___ =
                  let uu___1 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu___1 in
                let uu___1 = FStar_Ident.range_of_id x in
                FStar_Parser_AST.mk_term uu___ uu___1 FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a, uu___) ->
                let uu___1 = FStar_Ident.range_of_id a in
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a) uu___1
                  FStar_Parser_AST.Type_level
            | FStar_Parser_AST.TVariable a ->
                let uu___ = FStar_Ident.range_of_id a in
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a) uu___
                  FStar_Parser_AST.Type_level
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
              | uu___ -> FStar_Parser_AST.Nothing in
            FStar_List.fold_left
              (fun out ->
                 fun b ->
                   let uu___ =
                     let uu___1 =
                       let uu___2 = binder_to_term b in
                       (out, uu___2, (imp_of_aqual b)) in
                     FStar_Parser_AST.App uu___1 in
                   FStar_Parser_AST.mk_term uu___ out.FStar_Parser_AST.range
                     out.FStar_Parser_AST.level) t binders in
          let tycon_record_as_variant uu___ =
            match uu___ with
            | FStar_Parser_AST.TyconRecord (id, parms, kopt, fields) ->
                let constrName =
                  let uu___1 =
                    let uu___2 =
                      let uu___3 = FStar_Ident.string_of_id id in
                      Prims.op_Hat "Mk" uu___3 in
                    let uu___3 = FStar_Ident.range_of_id id in
                    (uu___2, uu___3) in
                  FStar_Ident.mk_ident uu___1 in
                let mfields =
                  FStar_List.map
                    (fun uu___1 ->
                       match uu___1 with
                       | (x, q, attrs, t) ->
                           let uu___2 = FStar_Ident.range_of_id x in
                           FStar_Parser_AST.mk_binder_with_attrs
                             (FStar_Parser_AST.Annotated (x, t)) uu___2
                             FStar_Parser_AST.Expr q attrs) fields in
                let result =
                  let uu___1 =
                    let uu___2 =
                      let uu___3 = FStar_Ident.lid_of_ids [id] in
                      FStar_Parser_AST.Var uu___3 in
                    let uu___3 = FStar_Ident.range_of_id id in
                    FStar_Parser_AST.mk_term uu___2 uu___3
                      FStar_Parser_AST.Type_level in
                  apply_binders uu___1 parms in
                let constrTyp =
                  let uu___1 = FStar_Ident.range_of_id id in
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result))) uu___1
                    FStar_Parser_AST.Type_level in
                let names = let uu___1 = binder_idents parms in id :: uu___1 in
                (FStar_List.iter
                   (fun uu___2 ->
                      match uu___2 with
                      | (f, uu___3, uu___4, uu___5) ->
                          let uu___6 =
                            FStar_Util.for_some
                              (fun i -> FStar_Ident.ident_equals f i) names in
                          if uu___6
                          then
                            let uu___7 =
                              let uu___8 =
                                let uu___9 = FStar_Ident.string_of_id f in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu___9 in
                              (FStar_Errors.Error_FieldShadow, uu___8) in
                            let uu___8 = FStar_Ident.range_of_id f in
                            FStar_Errors.raise_error uu___7 uu___8
                          else ()) fields;
                 (let uu___2 =
                    FStar_All.pipe_right fields
                      (FStar_List.map
                         (fun uu___3 ->
                            match uu___3 with
                            | (f, uu___4, uu___5, uu___6) -> f)) in
                  ((FStar_Parser_AST.TyconVariant
                      (id, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp), false)])),
                    uu___2)))
            | uu___1 -> failwith "impossible" in
          let desugar_abstract_tc quals1 _env mutuals uu___ =
            match uu___ with
            | FStar_Parser_AST.TyconAbstract (id, binders, kopt) ->
                let uu___1 = typars_of_binders _env binders in
                (match uu___1 with
                 | (_env', typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k1 ->
                           desugar_term _env' k1 in
                     let tconstr =
                       let uu___2 =
                         let uu___3 =
                           let uu___4 = FStar_Ident.lid_of_ids [id] in
                           FStar_Parser_AST.Var uu___4 in
                         let uu___4 = FStar_Ident.range_of_id id in
                         FStar_Parser_AST.mk_term uu___3 uu___4
                           FStar_Parser_AST.Type_level in
                       apply_binders uu___2 binders in
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
                     let uu___2 =
                       FStar_Syntax_DsEnv.push_top_level_rec_binding _env id
                         FStar_Syntax_Syntax.delta_constant in
                     (match uu___2 with
                      | (_env1, uu___3) ->
                          let uu___4 =
                            FStar_Syntax_DsEnv.push_top_level_rec_binding
                              _env' id FStar_Syntax_Syntax.delta_constant in
                          (match uu___4 with
                           | (_env2, uu___5) -> (_env1, _env2, se, tconstr))))
            | uu___1 -> failwith "Unexpected tycon" in
          let push_tparams env1 bs =
            let uu___ =
              FStar_List.fold_left
                (fun uu___1 ->
                   fun b ->
                     match uu___1 with
                     | (env2, tps) ->
                         let uu___2 =
                           FStar_Syntax_DsEnv.push_bv env2
                             (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.ppname in
                         (match uu___2 with
                          | (env3, y) ->
                              let uu___3 =
                                let uu___4 =
                                  FStar_Syntax_Syntax.mk_binder_with_attrs y
                                    b.FStar_Syntax_Syntax.binder_qual
                                    b.FStar_Syntax_Syntax.binder_attrs in
                                uu___4 :: tps in
                              (env3, uu___3))) (env1, []) bs in
            match uu___ with | (env2, bs1) -> (env2, (FStar_List.rev bs1)) in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id, bs, kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None ->
                    let uu___ =
                      let uu___1 = FStar_Ident.range_of_id id in
                      tm_type_z uu___1 in
                    FStar_Pervasives_Native.Some uu___
                | uu___ -> kopt in
              let tc = FStar_Parser_AST.TyconAbstract (id, bs, kopt1) in
              let uu___ = desugar_abstract_tc quals env [] tc in
              (match uu___ with
               | (uu___1, uu___2, se, uu___3) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l, uu___4, typars, k, [], []) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu___7 =
                                 let uu___8 = FStar_Options.ml_ish () in
                                 Prims.op_Negation uu___8 in
                               if uu___7
                               then
                                 let uu___8 =
                                   let uu___9 =
                                     let uu___10 =
                                       FStar_Syntax_Print.lid_to_string l in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu___10 in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu___9) in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu___8
                               else ());
                              FStar_Syntax_Syntax.Assumption
                              ::
                              FStar_Syntax_Syntax.New
                              ::
                              quals1) in
                         let t =
                           match typars with
                           | [] -> k
                           | uu___5 ->
                               let uu___6 =
                                 let uu___7 =
                                   let uu___8 =
                                     FStar_Syntax_Syntax.mk_Total k in
                                   (typars, uu___8) in
                                 FStar_Syntax_Syntax.Tm_arrow uu___7 in
                               FStar_Syntax_Syntax.mk uu___6
                                 se.FStar_Syntax_Syntax.sigrng in
                         let uu___5 = se in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___5.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___5.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___5.FStar_Syntax_Syntax.sigattrs);
                           FStar_Syntax_Syntax.sigopts =
                             (uu___5.FStar_Syntax_Syntax.sigopts)
                         }
                     | uu___4 -> failwith "Impossible" in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1 in
                   (env1, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t))::[] ->
              let uu___ = typars_of_binders env binders in
              (match uu___ with
               | (env', typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None ->
                         let uu___1 =
                           FStar_Util.for_some
                             (fun uu___2 ->
                                match uu___2 with
                                | FStar_Syntax_Syntax.Effect -> true
                                | uu___3 -> false) quals in
                         if uu___1
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu___1 = desugar_term env' k in
                         FStar_Pervasives_Native.Some uu___1 in
                   let t0 = t in
                   let quals1 =
                     let uu___1 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___2 ->
                               match uu___2 with
                               | FStar_Syntax_Syntax.Logic -> true
                               | uu___3 -> false)) in
                     if uu___1
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals in
                   let qlid = FStar_Syntax_DsEnv.qualify env id in
                   let se =
                     let uu___1 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect) in
                     if uu___1
                     then
                       let uu___2 =
                         let uu___3 =
                           let uu___4 = unparen t in
                           uu___4.FStar_Parser_AST.tm in
                         match uu___3 with
                         | FStar_Parser_AST.Construct (head, args) ->
                             let uu___4 =
                               match FStar_List.rev args with
                               | (last_arg, uu___5)::args_rev ->
                                   let uu___6 =
                                     let uu___7 = unparen last_arg in
                                     uu___7.FStar_Parser_AST.tm in
                                   (match uu___6 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu___7 -> ([], args))
                               | uu___5 -> ([], args) in
                             (match uu___4 with
                              | (cattributes, args1) ->
                                  let uu___5 =
                                    desugar_attributes env cattributes in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu___5))
                         | uu___4 -> (t, []) in
                       match uu___2 with
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
                                  (fun uu___3 ->
                                     match uu___3 with
                                     | FStar_Syntax_Syntax.Effect -> false
                                     | uu___4 -> true)) in
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
          | (FStar_Parser_AST.TyconRecord uu___)::[] ->
              let trec = FStar_List.hd tcs in
              let uu___1 = tycon_record_as_variant trec in
              (match uu___1 with
               | (t, fs) ->
                   let uu___2 =
                     let uu___3 =
                       let uu___4 =
                         let uu___5 =
                           let uu___6 = FStar_Syntax_DsEnv.current_module env in
                           FStar_Ident.ids_of_lid uu___6 in
                         (uu___5, fs) in
                       FStar_Syntax_Syntax.RecordType uu___4 in
                     uu___3 :: quals in
                   desugar_tycon env d uu___2 [t])
          | uu___::uu___1 ->
              let env0 = env in
              let mutuals =
                FStar_List.map
                  (fun x ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs in
              let rec collect_tcs quals1 et tc =
                let uu___2 = et in
                match uu___2 with
                | (env1, tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu___3 ->
                         let trec = tc in
                         let uu___4 = tycon_record_as_variant trec in
                         (match uu___4 with
                          | (t, fs) ->
                              let uu___5 =
                                let uu___6 =
                                  let uu___7 =
                                    let uu___8 =
                                      let uu___9 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1 in
                                      FStar_Ident.ids_of_lid uu___9 in
                                    (uu___8, fs) in
                                  FStar_Syntax_Syntax.RecordType uu___7 in
                                uu___6 :: quals1 in
                              collect_tcs uu___5 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id, binders, kopt, constructors) ->
                         let uu___3 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt)) in
                         (match uu___3 with
                          | (env2, uu___4, se, tconstr) ->
                              (env2,
                                ((FStar_Pervasives.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t) ->
                         let uu___3 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt)) in
                         (match uu___3 with
                          | (env2, uu___4, se, tconstr) ->
                              (env2,
                                ((FStar_Pervasives.Inr
                                    (se, binders, t, quals1)) :: tcs1)))
                     | uu___3 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng) in
              let uu___2 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs in
              (match uu___2 with
               | (env1, tcs1) ->
                   let tcs2 = FStar_List.rev tcs1 in
                   let tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___3 ->
                             match uu___3 with
                             | FStar_Pervasives.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id, uvs, tpars, k, uu___4, uu___5);
                                    FStar_Syntax_Syntax.sigrng = uu___6;
                                    FStar_Syntax_Syntax.sigquals = uu___7;
                                    FStar_Syntax_Syntax.sigmeta = uu___8;
                                    FStar_Syntax_Syntax.sigattrs = uu___9;
                                    FStar_Syntax_Syntax.sigopts = uu___10;_},
                                  binders, t, quals1)
                                 ->
                                 let t1 =
                                   let uu___11 =
                                     typars_of_binders env1 binders in
                                   match uu___11 with
                                   | (env2, tpars1) ->
                                       let uu___12 = push_tparams env2 tpars1 in
                                       (match uu___12 with
                                        | (env_tps, tpars2) ->
                                            let t2 = desugar_typ env_tps t in
                                            let tpars3 =
                                              FStar_Syntax_Subst.close_binders
                                                tpars2 in
                                            FStar_Syntax_Subst.close tpars3
                                              t2) in
                                 let uu___11 =
                                   let uu___12 =
                                     mk_typ_abbrev env1 d id uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id] quals1 rng in
                                   ([], uu___12) in
                                 [uu___11]
                             | FStar_Pervasives.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname, univs, tpars, k, mutuals1,
                                       uu___4);
                                    FStar_Syntax_Syntax.sigrng = uu___5;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu___6;
                                    FStar_Syntax_Syntax.sigattrs = uu___7;
                                    FStar_Syntax_Syntax.sigopts = uu___8;_},
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
                                 let uu___9 = push_tparams env1 tpars in
                                 (match uu___9 with
                                  | (env_tps, tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun tp ->
                                             let uu___10 = tp in
                                             {
                                               FStar_Syntax_Syntax.binder_bv
                                                 =
                                                 (uu___10.FStar_Syntax_Syntax.binder_bv);
                                               FStar_Syntax_Syntax.binder_qual
                                                 =
                                                 (FStar_Pervasives_Native.Some
                                                    (FStar_Syntax_Syntax.Implicit
                                                       true));
                                               FStar_Syntax_Syntax.binder_attrs
                                                 =
                                                 (uu___10.FStar_Syntax_Syntax.binder_attrs)
                                             }) tps in
                                      let tot_tconstr = mk_tot tconstr in
                                      let attrs =
                                        FStar_List.map (desugar_term env1)
                                          d.FStar_Parser_AST.attrs in
                                      let val_attrs =
                                        let uu___10 =
                                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                                            env1 tname in
                                        FStar_All.pipe_right uu___10
                                          FStar_Pervasives_Native.snd in
                                      let uu___10 =
                                        let uu___11 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu___12 ->
                                                  match uu___12 with
                                                  | (id, topt, of_notation)
                                                      ->
                                                      let t =
                                                        if of_notation
                                                        then
                                                          match topt with
                                                          | FStar_Pervasives_Native.Some
                                                              t1 ->
                                                              FStar_Parser_AST.mk_term
                                                                (FStar_Parser_AST.Product
                                                                   ([
                                                                    FStar_Parser_AST.mk_binder
                                                                    (FStar_Parser_AST.NoName
                                                                    t1)
                                                                    t1.FStar_Parser_AST.range
                                                                    t1.FStar_Parser_AST.level
                                                                    FStar_Pervasives_Native.None],
                                                                    tot_tconstr))
                                                                t1.FStar_Parser_AST.range
                                                                t1.FStar_Parser_AST.level
                                                          | FStar_Pervasives_Native.None
                                                              -> tconstr
                                                        else
                                                          (match topt with
                                                           | FStar_Pervasives_Native.None
                                                               ->
                                                               failwith
                                                                 "Impossible"
                                                           | FStar_Pervasives_Native.Some
                                                               t1 -> t1) in
                                                      let t1 =
                                                        let uu___13 =
                                                          close env_tps t in
                                                        desugar_term env_tps
                                                          uu___13 in
                                                      let name =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env1 id in
                                                      let quals2 =
                                                        FStar_All.pipe_right
                                                          tname_quals
                                                          (FStar_List.collect
                                                             (fun uu___13 ->
                                                                match uu___13
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu___14 ->
                                                                    [])) in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars in
                                                      let uu___13 =
                                                        let uu___14 =
                                                          let uu___15 =
                                                            let uu___16 =
                                                              let uu___17 =
                                                                let uu___18 =
                                                                  let uu___19
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu___19 in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu___18 in
                                                              (name, univs,
                                                                uu___17,
                                                                tname, ntps,
                                                                mutuals1) in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu___16 in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu___15;
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
                                                        (tps, uu___14) in
                                                      (name, uu___13))) in
                                        FStar_All.pipe_left FStar_List.split
                                          uu___11 in
                                      (match uu___10 with
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
                             | uu___4 -> failwith "impossible")) in
                   let sigelts =
                     FStar_All.pipe_right tps_sigelts
                       (FStar_List.map
                          (fun uu___3 ->
                             match uu___3 with | (uu___4, se) -> se)) in
                   let uu___3 =
                     let uu___4 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu___4 rng in
                   (match uu___3 with
                    | (bundle, abbrevs) ->
                        let env2 = FStar_Syntax_DsEnv.push_sigelt env0 bundle in
                        let env3 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env2 abbrevs in
                        let data_ops =
                          FStar_All.pipe_right tps_sigelts
                            (FStar_List.collect
                               (fun uu___4 ->
                                  match uu___4 with
                                  | (tps, se) ->
                                      mk_data_projector_names quals env3 se)) in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname, uu___4, tps, k, uu___5,
                                       constrs)
                                      ->
                                      let quals1 =
                                        se.FStar_Syntax_Syntax.sigquals in
                                      let uu___6 =
                                        FStar_All.pipe_right constrs
                                          (FStar_List.filter
                                             (fun data_lid ->
                                                let data_quals =
                                                  let data_se =
                                                    let uu___7 =
                                                      FStar_All.pipe_right
                                                        sigelts
                                                        (FStar_List.find
                                                           (fun se1 ->
                                                              match se1.FStar_Syntax_Syntax.sigel
                                                              with
                                                              | FStar_Syntax_Syntax.Sig_datacon
                                                                  (name,
                                                                   uu___8,
                                                                   uu___9,
                                                                   uu___10,
                                                                   uu___11,
                                                                   uu___12)
                                                                  ->
                                                                  FStar_Ident.lid_equals
                                                                    name
                                                                    data_lid
                                                              | uu___8 ->
                                                                  false)) in
                                                    FStar_All.pipe_right
                                                      uu___7 FStar_Util.must in
                                                  data_se.FStar_Syntax_Syntax.sigquals in
                                                let uu___7 =
                                                  FStar_All.pipe_right
                                                    data_quals
                                                    (FStar_List.existsb
                                                       (fun uu___8 ->
                                                          match uu___8 with
                                                          | FStar_Syntax_Syntax.RecordConstructor
                                                              uu___9 -> true
                                                          | uu___9 -> false)) in
                                                Prims.op_Negation uu___7)) in
                                      mk_data_discriminators quals1 env3
                                        uu___6
                                  | uu___4 -> [])) in
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
      (FStar_Syntax_DsEnv.env * FStar_Syntax_Syntax.binder Prims.list))
  =
  fun env ->
    fun binders ->
      let uu___ =
        FStar_List.fold_left
          (fun uu___1 ->
             fun b ->
               match uu___1 with
               | (env1, binders1) ->
                   let uu___2 = desugar_binder env1 b in
                   (match uu___2 with
                    | (FStar_Pervasives_Native.Some a, k, attrs) ->
                        let uu___3 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k, attrs) in
                        (match uu___3 with
                         | (binder, env2) -> (env2, (binder :: binders1)))
                    | uu___3 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders in
      match uu___ with
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
          let uu___ =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___1 ->
                    match uu___1 with
                    | FStar_Syntax_Syntax.Reflectable uu___2 -> true
                    | uu___2 -> false)) in
          if uu___
          then
            let monad_env =
              let uu___1 = FStar_Ident.ident_of_lid effect_name in
              FStar_Syntax_DsEnv.enter_monad_scope env uu___1 in
            let reflect_lid =
              let uu___1 = FStar_Ident.id_of_text "reflect" in
              FStar_All.pipe_right uu___1
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
        let warn1 uu___ =
          if warn
          then
            let uu___1 =
              let uu___2 =
                let uu___3 = FStar_Ident.string_of_lid head in
                FStar_Util.format1
                  "Found ill-applied '%s', argument should be a non-empty list of integer literals"
                  uu___3 in
              (FStar_Errors.Warning_UnappliedFail, uu___2) in
            FStar_Errors.log_issue at.FStar_Syntax_Syntax.pos uu___1
          else () in
        let uu___ = FStar_Syntax_Util.head_and_args at in
        match uu___ with
        | (hd, args) ->
            let uu___1 =
              let uu___2 = FStar_Syntax_Subst.compress hd in
              uu___2.FStar_Syntax_Syntax.n in
            (match uu___1 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 FStar_Syntax_Syntax.fv_eq_lid fv head ->
                 (match args with
                  | [] -> ((FStar_Pervasives_Native.Some []), true)
                  | (a1, uu___2)::[] ->
                      let uu___3 =
                        let uu___4 =
                          let uu___5 =
                            FStar_Syntax_Embeddings.e_list
                              FStar_Syntax_Embeddings.e_int in
                          FStar_Syntax_Embeddings.unembed uu___5 a1 in
                        uu___4 true FStar_Syntax_Embeddings.id_norm_cb in
                      (match uu___3 with
                       | FStar_Pervasives_Native.Some es ->
                           let uu___4 =
                             let uu___5 =
                               FStar_List.map FStar_BigInt.to_int_fs es in
                             FStar_Pervasives_Native.Some uu___5 in
                           (uu___4, true)
                       | uu___4 ->
                           (warn1 (); (FStar_Pervasives_Native.None, true)))
                  | uu___2 ->
                      (warn1 (); (FStar_Pervasives_Native.None, true)))
             | uu___2 -> (FStar_Pervasives_Native.None, false))
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
      let uu___ = parse_attr_with_list warn at FStar_Parser_Const.fail_attr in
      match uu___ with
      | (res, matched) ->
          if matched
          then rebind res false
          else
            (let uu___2 =
               parse_attr_with_list warn at FStar_Parser_Const.fail_lax_attr in
             match uu___2 with | (res1, uu___3) -> rebind res1 true)
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
        | uu___ -> FStar_Pervasives_Native.None in
      FStar_List.fold_right
        (fun at ->
           fun acc -> let uu___ = get_fail_attr1 warn at in comb uu___ acc)
        ats FStar_Pervasives_Native.None
let (lookup_effect_lid :
  FStar_Syntax_DsEnv.env ->
    FStar_Ident.lident -> FStar_Range.range -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env ->
    fun l ->
      fun r ->
        let uu___ = FStar_Syntax_DsEnv.try_lookup_effect_defn env l in
        match uu___ with
        | FStar_Pervasives_Native.None ->
            let uu___1 =
              let uu___2 =
                let uu___3 =
                  let uu___4 = FStar_Syntax_Print.lid_to_string l in
                  Prims.op_Hat uu___4 " not found" in
                Prims.op_Hat "Effect name " uu___3 in
              (FStar_Errors.Fatal_EffectNotFound, uu___2) in
            FStar_Errors.raise_error uu___1 r
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
                    let uu___ = desugar_binders monad_env eff_binders in
                    match uu___ with
                    | (env1, binders) ->
                        let eff_t = desugar_term env1 eff_typ in
                        let num_indices =
                          let uu___1 =
                            let uu___2 =
                              FStar_Syntax_Util.arrow_formals eff_t in
                            FStar_Pervasives_Native.fst uu___2 in
                          FStar_List.length uu___1 in
                        (if is_layered && (num_indices <= Prims.int_one)
                         then
                           (let uu___2 =
                              let uu___3 =
                                let uu___4 =
                                  let uu___5 =
                                    FStar_Ident.string_of_id eff_name in
                                  Prims.op_Hat uu___5
                                    "is defined as a layered effect but has no indices" in
                                Prims.op_Hat "Effect " uu___4 in
                              (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                uu___3) in
                            FStar_Errors.raise_error uu___2
                              d.FStar_Parser_AST.drange)
                         else ();
                         (let for_free = num_indices = Prims.int_one in
                          if for_free
                          then
                            (let uu___3 =
                               let uu___4 =
                                 let uu___5 =
                                   FStar_Ident.string_of_id eff_name in
                                 FStar_Util.format1
                                   "DM4Free feature is deprecated and will be removed soon, use layered effects to define %s"
                                   uu___5 in
                               (FStar_Errors.Warning_DeprecatedGeneric,
                                 uu___4) in
                             FStar_Errors.log_issue d.FStar_Parser_AST.drange
                               uu___3)
                          else ();
                          (let mandatory_members =
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
                                 (uu___3, uu___4,
                                  (FStar_Parser_AST.TyconAbbrev
                                  (name, uu___5, uu___6, uu___7))::[])
                                 -> FStar_Ident.string_of_id name
                             | uu___3 ->
                                 failwith
                                   "Malformed effect member declaration." in
                           let uu___3 =
                             FStar_List.partition
                               (fun decl ->
                                  let uu___4 = name_of_eff_decl decl in
                                  FStar_List.mem uu___4 mandatory_members)
                               eff_decls in
                           match uu___3 with
                           | (mandatory_members_decls, actions) ->
                               let uu___4 =
                                 FStar_All.pipe_right mandatory_members_decls
                                   (FStar_List.fold_left
                                      (fun uu___5 ->
                                         fun decl ->
                                           match uu___5 with
                                           | (env2, out) ->
                                               let uu___6 =
                                                 desugar_decl env2 decl in
                                               (match uu___6 with
                                                | (env3, ses) ->
                                                    let uu___7 =
                                                      let uu___8 =
                                                        FStar_List.hd ses in
                                                      uu___8 :: out in
                                                    (env3, uu___7)))
                                      (env1, [])) in
                               (match uu___4 with
                                | (env2, decls) ->
                                    let binders1 =
                                      FStar_Syntax_Subst.close_binders
                                        binders in
                                    let actions1 =
                                      FStar_All.pipe_right actions
                                        (FStar_List.map
                                           (fun d1 ->
                                              match d1.FStar_Parser_AST.d
                                              with
                                              | FStar_Parser_AST.Tycon
                                                  (uu___5, uu___6,
                                                   (FStar_Parser_AST.TyconAbbrev
                                                   (name, action_params,
                                                    uu___7,
                                                    {
                                                      FStar_Parser_AST.tm =
                                                        FStar_Parser_AST.Construct
                                                        (uu___8,
                                                         (def, uu___9)::
                                                         (cps_type, uu___10)::[]);
                                                      FStar_Parser_AST.range
                                                        = uu___11;
                                                      FStar_Parser_AST.level
                                                        = uu___12;_}))::[])
                                                  when
                                                  Prims.op_Negation for_free
                                                  ->
                                                  let uu___13 =
                                                    desugar_binders env2
                                                      action_params in
                                                  (match uu___13 with
                                                   | (env3, action_params1)
                                                       ->
                                                       let action_params2 =
                                                         FStar_Syntax_Subst.close_binders
                                                           action_params1 in
                                                       let uu___14 =
                                                         FStar_Syntax_DsEnv.qualify
                                                           env3 name in
                                                       let uu___15 =
                                                         let uu___16 =
                                                           desugar_term env3
                                                             def in
                                                         FStar_Syntax_Subst.close
                                                           (FStar_List.append
                                                              binders1
                                                              action_params2)
                                                           uu___16 in
                                                       let uu___16 =
                                                         let uu___17 =
                                                           desugar_typ env3
                                                             cps_type in
                                                         FStar_Syntax_Subst.close
                                                           (FStar_List.append
                                                              binders1
                                                              action_params2)
                                                           uu___17 in
                                                       {
                                                         FStar_Syntax_Syntax.action_name
                                                           = uu___14;
                                                         FStar_Syntax_Syntax.action_unqualified_name
                                                           = name;
                                                         FStar_Syntax_Syntax.action_univs
                                                           = [];
                                                         FStar_Syntax_Syntax.action_params
                                                           = action_params2;
                                                         FStar_Syntax_Syntax.action_defn
                                                           = uu___15;
                                                         FStar_Syntax_Syntax.action_typ
                                                           = uu___16
                                                       })
                                              | FStar_Parser_AST.Tycon
                                                  (uu___5, uu___6,
                                                   (FStar_Parser_AST.TyconAbbrev
                                                   (name, action_params,
                                                    uu___7, defn))::[])
                                                  when for_free || is_layered
                                                  ->
                                                  let uu___8 =
                                                    desugar_binders env2
                                                      action_params in
                                                  (match uu___8 with
                                                   | (env3, action_params1)
                                                       ->
                                                       let action_params2 =
                                                         FStar_Syntax_Subst.close_binders
                                                           action_params1 in
                                                       let uu___9 =
                                                         FStar_Syntax_DsEnv.qualify
                                                           env3 name in
                                                       let uu___10 =
                                                         let uu___11 =
                                                           desugar_term env3
                                                             defn in
                                                         FStar_Syntax_Subst.close
                                                           (FStar_List.append
                                                              binders1
                                                              action_params2)
                                                           uu___11 in
                                                       {
                                                         FStar_Syntax_Syntax.action_name
                                                           = uu___9;
                                                         FStar_Syntax_Syntax.action_unqualified_name
                                                           = name;
                                                         FStar_Syntax_Syntax.action_univs
                                                           = [];
                                                         FStar_Syntax_Syntax.action_params
                                                           = action_params2;
                                                         FStar_Syntax_Syntax.action_defn
                                                           = uu___10;
                                                         FStar_Syntax_Syntax.action_typ
                                                           =
                                                           FStar_Syntax_Syntax.tun
                                                       })
                                              | uu___5 ->
                                                  FStar_Errors.raise_error
                                                    (FStar_Errors.Fatal_MalformedActionDeclaration,
                                                      "Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples).")
                                                    d1.FStar_Parser_AST.drange)) in
                                    let eff_t1 =
                                      FStar_Syntax_Subst.close binders1 eff_t in
                                    let lookup s =
                                      let l =
                                        let uu___5 =
                                          FStar_Ident.mk_ident
                                            (s, (d.FStar_Parser_AST.drange)) in
                                        FStar_Syntax_DsEnv.qualify env2
                                          uu___5 in
                                      let uu___5 =
                                        let uu___6 =
                                          FStar_Syntax_DsEnv.fail_or env2
                                            (FStar_Syntax_DsEnv.try_lookup_definition
                                               env2) l in
                                        FStar_All.pipe_left
                                          (FStar_Syntax_Subst.close binders1)
                                          uu___6 in
                                      ([], uu___5) in
                                    let mname =
                                      FStar_Syntax_DsEnv.qualify env0
                                        eff_name in
                                    let qualifiers =
                                      FStar_List.map
                                        (trans_qual d.FStar_Parser_AST.drange
                                           (FStar_Pervasives_Native.Some
                                              mname)) quals in
                                    let dummy_tscheme =
                                      ([], FStar_Syntax_Syntax.tun) in
                                    let combinators =
                                      if for_free
                                      then
                                        let uu___5 =
                                          let uu___6 =
                                            let uu___7 = lookup "repr" in
                                            FStar_Pervasives_Native.Some
                                              uu___7 in
                                          let uu___7 =
                                            let uu___8 = lookup "return" in
                                            FStar_Pervasives_Native.Some
                                              uu___8 in
                                          let uu___8 =
                                            let uu___9 = lookup "bind" in
                                            FStar_Pervasives_Native.Some
                                              uu___9 in
                                          {
                                            FStar_Syntax_Syntax.ret_wp =
                                              dummy_tscheme;
                                            FStar_Syntax_Syntax.bind_wp =
                                              dummy_tscheme;
                                            FStar_Syntax_Syntax.stronger =
                                              dummy_tscheme;
                                            FStar_Syntax_Syntax.if_then_else
                                              = dummy_tscheme;
                                            FStar_Syntax_Syntax.ite_wp =
                                              dummy_tscheme;
                                            FStar_Syntax_Syntax.close_wp =
                                              dummy_tscheme;
                                            FStar_Syntax_Syntax.trivial =
                                              dummy_tscheme;
                                            FStar_Syntax_Syntax.repr = uu___6;
                                            FStar_Syntax_Syntax.return_repr =
                                              uu___7;
                                            FStar_Syntax_Syntax.bind_repr =
                                              uu___8
                                          } in
                                        FStar_Syntax_Syntax.DM4F_eff uu___5
                                      else
                                        if is_layered
                                        then
                                          (let has_subcomp =
                                             FStar_List.existsb
                                               (fun decl ->
                                                  let uu___6 =
                                                    name_of_eff_decl decl in
                                                  uu___6 = "subcomp")
                                               eff_decls in
                                           let has_if_then_else =
                                             FStar_List.existsb
                                               (fun decl ->
                                                  let uu___6 =
                                                    name_of_eff_decl decl in
                                                  uu___6 = "if_then_else")
                                               eff_decls in
                                           let to_comb uu___6 =
                                             match uu___6 with
                                             | (us, t) ->
                                                 ((us, t), dummy_tscheme) in
                                           let uu___6 =
                                             let uu___7 =
                                               let uu___8 = lookup "repr" in
                                               FStar_All.pipe_right uu___8
                                                 to_comb in
                                             let uu___8 =
                                               let uu___9 = lookup "return" in
                                               FStar_All.pipe_right uu___9
                                                 to_comb in
                                             let uu___9 =
                                               let uu___10 = lookup "bind" in
                                               FStar_All.pipe_right uu___10
                                                 to_comb in
                                             let uu___10 =
                                               if has_subcomp
                                               then
                                                 let uu___11 =
                                                   lookup "subcomp" in
                                                 FStar_All.pipe_right uu___11
                                                   to_comb
                                               else
                                                 (dummy_tscheme,
                                                   dummy_tscheme) in
                                             let uu___11 =
                                               if has_if_then_else
                                               then
                                                 let uu___12 =
                                                   lookup "if_then_else" in
                                                 FStar_All.pipe_right uu___12
                                                   to_comb
                                               else
                                                 (dummy_tscheme,
                                                   dummy_tscheme) in
                                             {
                                               FStar_Syntax_Syntax.l_repr =
                                                 uu___7;
                                               FStar_Syntax_Syntax.l_return =
                                                 uu___8;
                                               FStar_Syntax_Syntax.l_bind =
                                                 uu___9;
                                               FStar_Syntax_Syntax.l_subcomp
                                                 = uu___10;
                                               FStar_Syntax_Syntax.l_if_then_else
                                                 = uu___11
                                             } in
                                           FStar_Syntax_Syntax.Layered_eff
                                             uu___6)
                                        else
                                          (let rr =
                                             FStar_Util.for_some
                                               (fun uu___7 ->
                                                  match uu___7 with
                                                  | FStar_Syntax_Syntax.Reifiable
                                                      -> true
                                                  | FStar_Syntax_Syntax.Reflectable
                                                      uu___8 -> true
                                                  | uu___8 -> false)
                                               qualifiers in
                                           let uu___7 =
                                             let uu___8 = lookup "return_wp" in
                                             let uu___9 = lookup "bind_wp" in
                                             let uu___10 = lookup "stronger" in
                                             let uu___11 =
                                               lookup "if_then_else" in
                                             let uu___12 = lookup "ite_wp" in
                                             let uu___13 = lookup "close_wp" in
                                             let uu___14 = lookup "trivial" in
                                             let uu___15 =
                                               if rr
                                               then
                                                 let uu___16 = lookup "repr" in
                                                 FStar_Pervasives_Native.Some
                                                   uu___16
                                               else
                                                 FStar_Pervasives_Native.None in
                                             let uu___16 =
                                               if rr
                                               then
                                                 let uu___17 =
                                                   lookup "return" in
                                                 FStar_Pervasives_Native.Some
                                                   uu___17
                                               else
                                                 FStar_Pervasives_Native.None in
                                             let uu___17 =
                                               if rr
                                               then
                                                 let uu___18 = lookup "bind" in
                                                 FStar_Pervasives_Native.Some
                                                   uu___18
                                               else
                                                 FStar_Pervasives_Native.None in
                                             {
                                               FStar_Syntax_Syntax.ret_wp =
                                                 uu___8;
                                               FStar_Syntax_Syntax.bind_wp =
                                                 uu___9;
                                               FStar_Syntax_Syntax.stronger =
                                                 uu___10;
                                               FStar_Syntax_Syntax.if_then_else
                                                 = uu___11;
                                               FStar_Syntax_Syntax.ite_wp =
                                                 uu___12;
                                               FStar_Syntax_Syntax.close_wp =
                                                 uu___13;
                                               FStar_Syntax_Syntax.trivial =
                                                 uu___14;
                                               FStar_Syntax_Syntax.repr =
                                                 uu___15;
                                               FStar_Syntax_Syntax.return_repr
                                                 = uu___16;
                                               FStar_Syntax_Syntax.bind_repr
                                                 = uu___17
                                             } in
                                           FStar_Syntax_Syntax.Primitive_eff
                                             uu___7) in
                                    let sigel =
                                      let uu___5 =
                                        let uu___6 =
                                          FStar_List.map (desugar_term env2)
                                            attrs in
                                        {
                                          FStar_Syntax_Syntax.mname = mname;
                                          FStar_Syntax_Syntax.cattributes =
                                            [];
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
                                            uu___6
                                        } in
                                      FStar_Syntax_Syntax.Sig_new_effect
                                        uu___5 in
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
                                           (fun env5 ->
                                              fun a ->
                                                let uu___5 =
                                                  FStar_Syntax_Util.action_as_lb
                                                    mname a
                                                    (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                                                FStar_Syntax_DsEnv.push_sigelt
                                                  env5 uu___5) env3) in
                                    let env5 =
                                      push_reflect_effect env4 qualifiers
                                        mname d.FStar_Parser_AST.drange in
                                    (env5, [se])))))
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
                let uu___ = desugar_binders env1 eff_binders in
                match uu___ with
                | (env2, binders) ->
                    let uu___1 =
                      let uu___2 = head_and_args defn in
                      match uu___2 with
                      | (head, args) ->
                          let lid =
                            match head.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu___3 ->
                                let uu___4 =
                                  let uu___5 =
                                    let uu___6 =
                                      let uu___7 =
                                        FStar_Parser_AST.term_to_string head in
                                      Prims.op_Hat uu___7 " not found" in
                                    Prims.op_Hat "Effect " uu___6 in
                                  (FStar_Errors.Fatal_EffectNotFound, uu___5) in
                                FStar_Errors.raise_error uu___4
                                  d.FStar_Parser_AST.drange in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid in
                          let uu___3 =
                            match FStar_List.rev args with
                            | (last_arg, uu___4)::args_rev ->
                                let uu___5 =
                                  let uu___6 = unparen last_arg in
                                  uu___6.FStar_Parser_AST.tm in
                                (match uu___5 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu___6 -> ([], args))
                            | uu___4 -> ([], args) in
                          (match uu___3 with
                           | (cattributes, args1) ->
                               let uu___4 = desugar_args env2 args1 in
                               let uu___5 =
                                 desugar_attributes env2 cattributes in
                               (lid, ed, uu___4, uu___5)) in
                    (match uu___1 with
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
                          (let uu___3 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit in
                           match uu___3 with
                           | (ed_binders, uu___4, ed_binders_opening) ->
                               let sub' shift_n uu___5 =
                                 match uu___5 with
                                 | (us, x) ->
                                     let x1 =
                                       let uu___6 =
                                         FStar_Syntax_Subst.shift_subst
                                           (shift_n + (FStar_List.length us))
                                           ed_binders_opening in
                                       FStar_Syntax_Subst.subst uu___6 x in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args in
                                     let uu___6 =
                                       let uu___7 =
                                         FStar_Syntax_Subst.subst s x1 in
                                       (us, uu___7) in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu___6 in
                               let sub = sub' Prims.int_zero in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name in
                               let ed1 =
                                 let uu___5 =
                                   sub ed.FStar_Syntax_Syntax.signature in
                                 let uu___6 =
                                   FStar_Syntax_Util.apply_eff_combinators
                                     sub ed.FStar_Syntax_Syntax.combinators in
                                 let uu___7 =
                                   FStar_List.map
                                     (fun action ->
                                        let nparam =
                                          FStar_List.length
                                            action.FStar_Syntax_Syntax.action_params in
                                        let uu___8 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name in
                                        let uu___9 =
                                          let uu___10 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn)) in
                                          FStar_Pervasives_Native.snd uu___10 in
                                        let uu___10 =
                                          let uu___11 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ)) in
                                          FStar_Pervasives_Native.snd uu___11 in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu___8;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu___9;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu___10
                                        }) ed.FStar_Syntax_Syntax.actions in
                                 {
                                   FStar_Syntax_Syntax.mname = mname;
                                   FStar_Syntax_Syntax.cattributes =
                                     cattributes;
                                   FStar_Syntax_Syntax.univs =
                                     (ed.FStar_Syntax_Syntax.univs);
                                   FStar_Syntax_Syntax.binders = binders1;
                                   FStar_Syntax_Syntax.signature = uu___5;
                                   FStar_Syntax_Syntax.combinators = uu___6;
                                   FStar_Syntax_Syntax.actions = uu___7;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 } in
                               let se =
                                 let uu___5 =
                                   let uu___6 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname) in
                                   FStar_List.map uu___6 quals in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (FStar_Syntax_Syntax.Sig_new_effect ed1);
                                   FStar_Syntax_Syntax.sigrng =
                                     (d.FStar_Parser_AST.drange);
                                   FStar_Syntax_Syntax.sigquals = uu___5;
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
                                      (fun env5 ->
                                         fun a ->
                                           let uu___5 =
                                             FStar_Syntax_Util.action_as_lb
                                               mname a
                                               (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                                           FStar_Syntax_DsEnv.push_sigelt
                                             env5 uu___5) env3) in
                               let env5 =
                                 let uu___5 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable) in
                                 if uu___5
                                 then
                                   let reflect_lid =
                                     let uu___6 =
                                       FStar_Ident.id_of_text "reflect" in
                                     FStar_All.pipe_right uu___6
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
             let uu___ = get_fail_attr1 false at in FStar_Option.isNone uu___)
          ats in
      let env0 =
        let uu___ = FStar_Syntax_DsEnv.snapshot env in
        FStar_All.pipe_right uu___ FStar_Pervasives_Native.snd in
      let attrs = FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs in
      let uu___ =
        let uu___1 = get_fail_attr false attrs in
        match uu___1 with
        | FStar_Pervasives_Native.Some (expected_errs, lax) ->
            let d1 =
              let uu___2 = d in
              {
                FStar_Parser_AST.d = (uu___2.FStar_Parser_AST.d);
                FStar_Parser_AST.drange = (uu___2.FStar_Parser_AST.drange);
                FStar_Parser_AST.quals = (uu___2.FStar_Parser_AST.quals);
                FStar_Parser_AST.attrs = []
              } in
            let uu___2 =
              FStar_Errors.catch_errors
                (fun uu___3 ->
                   FStar_Options.with_saved_options
                     (fun uu___4 -> desugar_decl_noattrs env d1)) in
            (match uu___2 with
             | (errs, r) ->
                 (match (errs, r) with
                  | ([], FStar_Pervasives_Native.Some (env1, ses)) ->
                      let ses1 =
                        FStar_List.map
                          (fun se ->
                             let uu___3 = se in
                             let uu___4 = no_fail_attrs attrs in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (uu___3.FStar_Syntax_Syntax.sigel);
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___3.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___3.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___3.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs = uu___4;
                               FStar_Syntax_Syntax.sigopts =
                                 (uu___3.FStar_Syntax_Syntax.sigopts)
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
                        (let uu___4 =
                           FStar_Errors.find_multiset_discrepancy
                             expected_errs errnos in
                         match uu___4 with
                         | FStar_Pervasives_Native.None -> (env0, [])
                         | FStar_Pervasives_Native.Some (e, n1, n2) ->
                             (FStar_List.iter FStar_Errors.print_issue errs1;
                              (let uu___7 =
                                 let uu___8 =
                                   let uu___9 =
                                     FStar_Common.string_of_list
                                       FStar_Util.string_of_int expected_errs in
                                   let uu___10 =
                                     FStar_Common.string_of_list
                                       FStar_Util.string_of_int errnos in
                                   let uu___11 = FStar_Util.string_of_int e in
                                   let uu___12 = FStar_Util.string_of_int n2 in
                                   let uu___13 = FStar_Util.string_of_int n1 in
                                   FStar_Util.format5
                                     "This top-level definition was expected to raise error codes %s, but it raised %s (at desugaring time). Error #%s was raised %s times, instead of %s."
                                     uu___9 uu___10 uu___11 uu___12 uu___13 in
                                 (FStar_Errors.Error_DidNotFail, uu___8) in
                               FStar_Errors.log_issue
                                 d1.FStar_Parser_AST.drange uu___7);
                              (env0, [])))))
        | FStar_Pervasives_Native.None -> desugar_decl_noattrs env d in
      match uu___ with
      | (env1, sigelts) ->
          let rec val_attrs ses =
            match ses with
            | {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                  uu___1;
                FStar_Syntax_Syntax.sigrng = uu___2;
                FStar_Syntax_Syntax.sigquals = uu___3;
                FStar_Syntax_Syntax.sigmeta = uu___4;
                FStar_Syntax_Syntax.sigattrs = uu___5;
                FStar_Syntax_Syntax.sigopts = uu___6;_}::[] ->
                let uu___7 =
                  let uu___8 = FStar_List.hd sigelts in
                  FStar_Syntax_Util.lids_of_sigelt uu___8 in
                FStar_All.pipe_right uu___7
                  (FStar_List.collect
                     (fun nm ->
                        let uu___8 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env0 nm in
                        FStar_Pervasives_Native.snd uu___8))
            | {
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_inductive_typ uu___1;
                FStar_Syntax_Syntax.sigrng = uu___2;
                FStar_Syntax_Syntax.sigquals = uu___3;
                FStar_Syntax_Syntax.sigmeta = uu___4;
                FStar_Syntax_Syntax.sigattrs = uu___5;
                FStar_Syntax_Syntax.sigopts = uu___6;_}::uu___7 ->
                let uu___8 =
                  let uu___9 = FStar_List.hd sigelts in
                  FStar_Syntax_Util.lids_of_sigelt uu___9 in
                FStar_All.pipe_right uu___8
                  (FStar_List.collect
                     (fun nm ->
                        let uu___9 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env0 nm in
                        FStar_Pervasives_Native.snd uu___9))
            | {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_fail
                  (_errs, _lax, ses1);
                FStar_Syntax_Syntax.sigrng = uu___1;
                FStar_Syntax_Syntax.sigquals = uu___2;
                FStar_Syntax_Syntax.sigmeta = uu___3;
                FStar_Syntax_Syntax.sigattrs = uu___4;
                FStar_Syntax_Syntax.sigopts = uu___5;_}::[] ->
                FStar_List.collect (fun se -> val_attrs [se]) ses1
            | uu___1 -> [] in
          let attrs1 =
            let uu___1 = val_attrs sigelts in FStar_List.append attrs uu___1 in
          let uu___1 =
            FStar_List.map
              (fun sigelt ->
                 let uu___2 = sigelt in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___2.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___2.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___2.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___2.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs = attrs1;
                   FStar_Syntax_Syntax.sigopts =
                     (uu___2.FStar_Syntax_Syntax.sigopts)
                 }) sigelts in
          (env1, uu___1)
and (desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env ->
    fun d ->
      let uu___ = desugar_decl_aux env d in
      match uu___ with
      | (env1, ses) ->
          let uu___1 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs) in
          (env1, uu___1)
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
          let uu___ = FStar_Syntax_DsEnv.iface env in
          if uu___
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu___2 =
               let uu___3 =
                 let uu___4 = FStar_Syntax_DsEnv.dep_graph env in
                 let uu___5 = FStar_Syntax_DsEnv.current_module env in
                 FStar_Parser_Dep.module_has_interface uu___4 uu___5 in
               Prims.op_Negation uu___3 in
             if uu___2
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu___4 =
                  let uu___5 =
                    let uu___6 = FStar_Syntax_DsEnv.dep_graph env in
                    FStar_Parser_Dep.module_has_interface uu___6 lid in
                  Prims.op_Negation uu___5 in
                if uu___4
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu___6 =
                     let uu___7 =
                       let uu___8 = FStar_Syntax_DsEnv.dep_graph env in
                       FStar_Parser_Dep.deps_has_implementation uu___8 lid in
                     Prims.op_Negation uu___7 in
                   if uu___6
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x, l) ->
          let uu___ = FStar_Syntax_DsEnv.push_module_abbrev env x l in
          (uu___, [])
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
              | (FStar_Parser_AST.TyconRecord uu___)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu___ ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1 in
          let uu___ =
            let uu___1 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2 in
            desugar_tycon env d uu___1 tcs in
          (match uu___ with
           | (env1, ses) ->
               let mkclass lid =
                 let r = FStar_Ident.range_of_lid lid in
                 let uu___1 =
                   let uu___2 =
                     let uu___3 =
                       let uu___4 = tun_r r in
                       FStar_Syntax_Syntax.new_bv
                         (FStar_Pervasives_Native.Some r) uu___4 in
                     FStar_Syntax_Syntax.mk_binder uu___3 in
                   [uu___2] in
                 let uu___2 =
                   let uu___3 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid in
                   let uu___4 =
                     let uu___5 =
                       let uu___6 =
                         let uu___7 = FStar_Ident.string_of_lid lid in
                         FStar_Syntax_Util.exp_string uu___7 in
                       FStar_Syntax_Syntax.as_arg uu___6 in
                     [uu___5] in
                   FStar_Syntax_Util.mk_app uu___3 uu___4 in
                 FStar_Syntax_Util.abs uu___1 uu___2
                   FStar_Pervasives_Native.None in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector (uu___1, id))::uu___2 ->
                       FStar_Pervasives_Native.Some id
                   | uu___1::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None in
                 let uu___1 = get_fname se.FStar_Syntax_Syntax.sigquals in
                 match uu___1 with
                 | FStar_Pervasives_Native.None -> []
                 | FStar_Pervasives_Native.Some id ->
                     let uu___2 = FStar_Syntax_DsEnv.qualify env1 id in
                     [uu___2] in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1, uu___1) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid, uu___1, uu___2, uu___3, uu___4, uu___5) ->
                     let uu___6 =
                       let uu___7 =
                         let uu___8 =
                           let uu___9 = mkclass lid in (meths, uu___9) in
                         FStar_Syntax_Syntax.Sig_splice uu___8 in
                       {
                         FStar_Syntax_Syntax.sigel = uu___7;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = [];
                         FStar_Syntax_Syntax.sigopts =
                           FStar_Pervasives_Native.None
                       } in
                     [uu___6]
                 | uu___1 -> [] in
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
               | ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu___;
                    FStar_Parser_AST.prange = uu___1;_},
                  uu___2)::[] -> false
               | ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu___;
                    FStar_Parser_AST.prange = uu___1;_},
                  uu___2)::[] -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu___;
                         FStar_Parser_AST.prange = uu___1;_},
                       uu___2);
                    FStar_Parser_AST.prange = uu___3;_},
                  uu___4)::[] -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu___;
                         FStar_Parser_AST.prange = uu___1;_},
                       uu___2);
                    FStar_Parser_AST.prange = uu___3;_},
                  uu___4)::[] -> false
               | (p, uu___)::[] ->
                   let uu___1 = is_app_pattern p in Prims.op_Negation uu___1
               | uu___ -> false) in
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
            let uu___ = desugar_term_maybe_top true env as_inner_let in
            (match uu___ with
             | (ds_lets, aq) ->
                 (check_no_aq aq;
                  (let uu___2 =
                     let uu___3 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets in
                     uu___3.FStar_Syntax_Syntax.n in
                   match uu___2 with
                   | FStar_Syntax_Syntax.Tm_let (lbs, uu___3) ->
                       let fvs =
                         FStar_All.pipe_right
                           (FStar_Pervasives_Native.snd lbs)
                           (FStar_List.map
                              (fun lb ->
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname)) in
                       let uu___4 =
                         FStar_List.fold_right
                           (fun fv ->
                              fun uu___5 ->
                                match uu___5 with
                                | (qs, ats) ->
                                    let uu___6 =
                                      FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                                        env
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    (match uu___6 with
                                     | (qs', ats') ->
                                         ((FStar_List.append qs' qs),
                                           (FStar_List.append ats' ats))))
                           fvs ([], []) in
                       (match uu___4 with
                        | (val_quals, val_attrs) ->
                            let quals1 =
                              match quals with
                              | uu___5::uu___6 ->
                                  FStar_List.map
                                    (trans_qual1 FStar_Pervasives_Native.None)
                                    quals
                              | uu___5 -> val_quals in
                            let quals2 =
                              let uu___5 =
                                FStar_All.pipe_right lets1
                                  (FStar_Util.for_some
                                     (fun uu___6 ->
                                        match uu___6 with
                                        | (uu___7, (uu___8, t)) ->
                                            t.FStar_Parser_AST.level =
                                              FStar_Parser_AST.Formula)) in
                              if uu___5
                              then FStar_Syntax_Syntax.Logic :: quals1
                              else quals1 in
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
                                  (FStar_Syntax_Syntax.Sig_let (lbs, names));
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
                   | uu___3 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu___1 =
               match lets with
               | (pat, body)::[] -> (pat, body)
               | uu___2 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets" in
             match uu___1 with
             | (pat, body) ->
                 let fresh_toplevel_name =
                   FStar_Ident.gen FStar_Range.dummyRange in
                 let fresh_pat =
                   let var_pat =
                     FStar_Parser_AST.mk_pattern
                       (FStar_Parser_AST.PatVar
                          (fresh_toplevel_name, FStar_Pervasives_Native.None,
                            [])) FStar_Range.dummyRange in
                   match pat.FStar_Parser_AST.pat with
                   | FStar_Parser_AST.PatAscribed (pat1, ty) ->
                       let uu___2 = pat1 in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___2.FStar_Parser_AST.prange)
                       }
                   | uu___2 -> var_pat in
                 let main_let =
                   let quals1 =
                     if
                       FStar_List.mem FStar_Parser_AST.Private
                         d.FStar_Parser_AST.quals
                     then d.FStar_Parser_AST.quals
                     else FStar_Parser_AST.Private ::
                       (d.FStar_Parser_AST.quals) in
                   desugar_decl env
                     (let uu___2 = d in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___2.FStar_Parser_AST.drange);
                        FStar_Parser_AST.quals = quals1;
                        FStar_Parser_AST.attrs =
                          (uu___2.FStar_Parser_AST.attrs)
                      }) in
                 let main =
                   let uu___2 =
                     let uu___3 =
                       FStar_Ident.lid_of_ids [fresh_toplevel_name] in
                     FStar_Parser_AST.Var uu___3 in
                   FStar_Parser_AST.mk_term uu___2
                     pat.FStar_Parser_AST.prange FStar_Parser_AST.Expr in
                 let build_generic_projection uu___2 id_opt =
                   match uu___2 with
                   | (env1, ses) ->
                       let uu___3 =
                         match id_opt with
                         | FStar_Pervasives_Native.Some id ->
                             let lid = FStar_Ident.lid_of_ids [id] in
                             let branch =
                               let uu___4 = FStar_Ident.range_of_lid lid in
                               FStar_Parser_AST.mk_term
                                 (FStar_Parser_AST.Var lid) uu___4
                                 FStar_Parser_AST.Expr in
                             let bv_pat =
                               let uu___4 = FStar_Ident.range_of_id id in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatVar
                                    (id, FStar_Pervasives_Native.None, []))
                                 uu___4 in
                             (bv_pat, branch)
                         | FStar_Pervasives_Native.None ->
                             let id = FStar_Ident.gen FStar_Range.dummyRange in
                             let branch =
                               FStar_Parser_AST.mk_term
                                 (FStar_Parser_AST.Const
                                    FStar_Const.Const_unit)
                                 FStar_Range.dummyRange FStar_Parser_AST.Expr in
                             let bv_pat =
                               let uu___4 = FStar_Ident.range_of_id id in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatVar
                                    (id, FStar_Pervasives_Native.None, []))
                                 uu___4 in
                             let bv_pat1 =
                               let uu___4 =
                                 let uu___5 =
                                   let uu___6 =
                                     let uu___7 =
                                       let uu___8 =
                                         FStar_Ident.range_of_id id in
                                       unit_ty uu___8 in
                                     (uu___7, FStar_Pervasives_Native.None) in
                                   (bv_pat, uu___6) in
                                 FStar_Parser_AST.PatAscribed uu___5 in
                               let uu___5 = FStar_Ident.range_of_id id in
                               FStar_Parser_AST.mk_pattern uu___4 uu___5 in
                             (bv_pat1, branch) in
                       (match uu___3 with
                        | (bv_pat, branch) ->
                            let body1 =
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Match
                                   (main, FStar_Pervasives_Native.None,
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
                              let uu___4 = id_decl in
                              {
                                FStar_Parser_AST.d =
                                  (uu___4.FStar_Parser_AST.d);
                                FStar_Parser_AST.drange =
                                  (uu___4.FStar_Parser_AST.drange);
                                FStar_Parser_AST.quals =
                                  (d.FStar_Parser_AST.quals);
                                FStar_Parser_AST.attrs =
                                  (uu___4.FStar_Parser_AST.attrs)
                              } in
                            let uu___4 = desugar_decl env1 id_decl1 in
                            (match uu___4 with
                             | (env2, ses') ->
                                 (env2, (FStar_List.append ses ses')))) in
                 let build_projection uu___2 id =
                   match uu___2 with
                   | (env1, ses) ->
                       build_generic_projection (env1, ses)
                         (FStar_Pervasives_Native.Some id) in
                 let build_coverage_check uu___2 =
                   match uu___2 with
                   | (env1, ses) ->
                       build_generic_projection (env1, ses)
                         FStar_Pervasives_Native.None in
                 let bvs =
                   let uu___2 = gather_pattern_bound_vars pat in
                   FStar_All.pipe_right uu___2 FStar_Util.set_elements in
                 let uu___2 =
                   (FStar_List.isEmpty bvs) &&
                     (let uu___3 = is_var_pattern pat in
                      Prims.op_Negation uu___3) in
                 if uu___2
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
          let t1 = let uu___ = close_fun env t in desugar_term env uu___ in
          let quals1 =
            let uu___ =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env) in
            if uu___ then FStar_Parser_AST.Assumption :: quals else quals in
          let lid = FStar_Syntax_DsEnv.qualify env id in
          let attrs =
            FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs in
          let se =
            let uu___ =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1 in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu___;
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
                let t1 = desugar_term env term in
                let uu___ =
                  let uu___1 = FStar_Syntax_Syntax.null_binder t1 in [uu___1] in
                let uu___1 =
                  let uu___2 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu___2 in
                FStar_Syntax_Util.arrow uu___ uu___1 in
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
          uu___) ->
          failwith
            "Impossible: LayeredEffect (RedefineEffect _) (should not be parseable)"
      | FStar_Parser_AST.SubEffect l ->
          let src_ed =
            lookup_effect_lid env l.FStar_Parser_AST.msource
              d.FStar_Parser_AST.drange in
          let dst_ed =
            lookup_effect_lid env l.FStar_Parser_AST.mdest
              d.FStar_Parser_AST.drange in
          let uu___ =
            let uu___1 =
              (FStar_Syntax_Util.is_layered src_ed) ||
                (FStar_Syntax_Util.is_layered dst_ed) in
            Prims.op_Negation uu___1 in
          if uu___
          then
            let uu___1 =
              match l.FStar_Parser_AST.lift_op with
              | FStar_Parser_AST.NonReifiableLift t ->
                  let uu___2 =
                    let uu___3 =
                      let uu___4 = desugar_term env t in ([], uu___4) in
                    FStar_Pervasives_Native.Some uu___3 in
                  (uu___2, FStar_Pervasives_Native.None)
              | FStar_Parser_AST.ReifiableLift (wp, t) ->
                  let uu___2 =
                    let uu___3 =
                      let uu___4 = desugar_term env wp in ([], uu___4) in
                    FStar_Pervasives_Native.Some uu___3 in
                  let uu___3 =
                    let uu___4 =
                      let uu___5 = desugar_term env t in ([], uu___5) in
                    FStar_Pervasives_Native.Some uu___4 in
                  (uu___2, uu___3)
              | FStar_Parser_AST.LiftForFree t ->
                  let uu___2 =
                    let uu___3 =
                      let uu___4 = desugar_term env t in ([], uu___4) in
                    FStar_Pervasives_Native.Some uu___3 in
                  (FStar_Pervasives_Native.None, uu___2) in
            (match uu___1 with
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
                   let uu___2 =
                     let uu___3 =
                       let uu___4 = desugar_term env t in ([], uu___4) in
                     FStar_Pervasives_Native.Some uu___3 in
                   {
                     FStar_Syntax_Syntax.source =
                       (src_ed.FStar_Syntax_Syntax.mname);
                     FStar_Syntax_Syntax.target =
                       (dst_ed.FStar_Syntax_Syntax.mname);
                     FStar_Syntax_Syntax.lift_wp =
                       FStar_Pervasives_Native.None;
                     FStar_Syntax_Syntax.lift = uu___2
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
             | uu___2 ->
                 failwith
                   "Impossible! unexpected lift_op for lift to a layered effect")
      | FStar_Parser_AST.Polymonadic_bind (m_eff, n_eff, p_eff, bind) ->
          let m = lookup_effect_lid env m_eff d.FStar_Parser_AST.drange in
          let n = lookup_effect_lid env n_eff d.FStar_Parser_AST.drange in
          let p = lookup_effect_lid env p_eff d.FStar_Parser_AST.drange in
          let uu___ =
            let uu___1 =
              let uu___2 =
                let uu___3 =
                  let uu___4 =
                    let uu___5 = desugar_term env bind in ([], uu___5) in
                  ((m.FStar_Syntax_Syntax.mname),
                    (n.FStar_Syntax_Syntax.mname),
                    (p.FStar_Syntax_Syntax.mname), uu___4,
                    ([], FStar_Syntax_Syntax.tun)) in
                FStar_Syntax_Syntax.Sig_polymonadic_bind uu___3 in
              {
                FStar_Syntax_Syntax.sigel = uu___2;
                FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta;
                FStar_Syntax_Syntax.sigattrs = [];
                FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
              } in
            [uu___1] in
          (env, uu___)
      | FStar_Parser_AST.Polymonadic_subcomp (m_eff, n_eff, subcomp) ->
          let m = lookup_effect_lid env m_eff d.FStar_Parser_AST.drange in
          let n = lookup_effect_lid env n_eff d.FStar_Parser_AST.drange in
          let uu___ =
            let uu___1 =
              let uu___2 =
                let uu___3 =
                  let uu___4 =
                    let uu___5 = desugar_term env subcomp in ([], uu___5) in
                  ((m.FStar_Syntax_Syntax.mname),
                    (n.FStar_Syntax_Syntax.mname), uu___4,
                    ([], FStar_Syntax_Syntax.tun)) in
                FStar_Syntax_Syntax.Sig_polymonadic_subcomp uu___3 in
              {
                FStar_Syntax_Syntax.sigel = uu___2;
                FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta;
                FStar_Syntax_Syntax.sigattrs = [];
                FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
              } in
            [uu___1] in
          (env, uu___)
      | FStar_Parser_AST.Splice (ids, t) ->
          let t1 = desugar_term env t in
          let se =
            let uu___ =
              let uu___1 =
                let uu___2 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids in
                (uu___2, t1) in
              FStar_Syntax_Syntax.Sig_splice uu___1 in
            {
              FStar_Syntax_Syntax.sigel = uu___;
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
      let uu___ =
        FStar_List.fold_left
          (fun uu___1 ->
             fun d ->
               match uu___1 with
               | (env1, sigelts) ->
                   let uu___2 = desugar_decl env1 d in
                   (match uu___2 with
                    | (env2, se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls in
      match uu___ with | (env1, sigelts) -> (env1, sigelts)
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
          | (FStar_Pervasives_Native.None, uu___) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu___;
               FStar_Syntax_Syntax.is_interface = uu___1;_},
             FStar_Parser_AST.Module (current_lid, uu___2)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod, uu___) ->
              let uu___1 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod in
              FStar_Pervasives_Native.fst uu___1 in
        let uu___ =
          match m with
          | FStar_Parser_AST.Interface (mname, decls, admitted) ->
              let uu___1 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii in
              (uu___1, mname, decls, true)
          | FStar_Parser_AST.Module (mname, decls) ->
              let uu___1 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii in
              (uu___1, mname, decls, false) in
        match uu___ with
        | ((env2, pop_when_done), mname, decls, intf) ->
            let uu___1 = desugar_decls env2 decls in
            (match uu___1 with
             | (env3, sigelts) ->
                 let modul =
                   {
                     FStar_Syntax_Syntax.name = mname;
                     FStar_Syntax_Syntax.declarations = sigelts;
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
          let uu___ =
            (FStar_Options.interactive ()) &&
              (let uu___1 =
                 let uu___2 =
                   let uu___3 = FStar_Options.file_list () in
                   FStar_List.hd uu___3 in
                 FStar_Util.get_file_extension uu___2 in
               FStar_List.mem uu___1 ["fsti"; "fsi"]) in
          if uu___ then as_interface m else m in
        let uu___ = desugar_modul_common curmod env m1 in
        match uu___ with
        | (env1, modul, pop_when_done) ->
            if pop_when_done
            then let uu___1 = FStar_Syntax_DsEnv.pop () in (uu___1, modul)
            else (env1, modul)
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun env ->
    fun m ->
      let uu___ = desugar_modul_common FStar_Pervasives_Native.None env m in
      match uu___ with
      | (env1, modul, pop_when_done) ->
          let uu___1 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul in
          (match uu___1 with
           | (env2, modul1) ->
               ((let uu___3 =
                   let uu___4 =
                     FStar_Ident.string_of_lid
                       modul1.FStar_Syntax_Syntax.name in
                   FStar_Options.dump_module uu___4 in
                 if uu___3
                 then
                   let uu___4 = FStar_Syntax_Print.modul_to_string modul1 in
                   FStar_Util.print1 "Module after desugaring:\n%s\n" uu___4
                 else ());
                (let uu___3 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2 in
                 (uu___3, modul1))))
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
        (fun uu___ ->
           let uu___1 = desugar_modul env modul in
           match uu___1 with | (e, m) -> (m, e))
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls ->
    fun env ->
      with_options
        (fun uu___ ->
           let uu___1 = desugar_decls env decls in
           match uu___1 with | (env1, sigelts) -> (sigelts, env1))
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul ->
    fun a_modul ->
      fun env ->
        with_options
          (fun uu___ ->
             let uu___1 = desugar_partial_modul modul env a_modul in
             match uu___1 with | (env1, modul1) -> (modul1, env1))
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
              | uu___ ->
                  let t =
                    let uu___1 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Range.dummyRange in
                    erase_univs uu___1 in
                  let uu___1 =
                    let uu___2 = FStar_Syntax_Subst.compress t in
                    uu___2.FStar_Syntax_Syntax.n in
                  (match uu___1 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1, uu___2, uu___3) -> bs1
                   | uu___2 -> failwith "Impossible") in
            let uu___ =
              let uu___1 = erase_binders ed.FStar_Syntax_Syntax.binders in
              FStar_Syntax_Subst.open_term' uu___1 FStar_Syntax_Syntax.t_unit in
            match uu___ with
            | (binders, uu___1, binders_opening) ->
                let erase_term t =
                  let uu___2 =
                    let uu___3 = FStar_Syntax_Subst.subst binders_opening t in
                    erase_univs uu___3 in
                  FStar_Syntax_Subst.close binders uu___2 in
                let erase_tscheme uu___2 =
                  match uu___2 with
                  | (us, t) ->
                      let t1 =
                        let uu___3 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening in
                        FStar_Syntax_Subst.subst uu___3 t in
                      let uu___3 =
                        let uu___4 = erase_univs t1 in
                        FStar_Syntax_Subst.close binders uu___4 in
                      ([], uu___3) in
                let erase_action action =
                  let opening =
                    FStar_Syntax_Subst.shift_subst
                      (FStar_List.length
                         action.FStar_Syntax_Syntax.action_univs)
                      binders_opening in
                  let erased_action_params =
                    match action.FStar_Syntax_Syntax.action_params with
                    | [] -> []
                    | uu___2 ->
                        let bs =
                          let uu___3 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params in
                          FStar_All.pipe_left erase_binders uu___3 in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Range.dummyRange in
                        let uu___3 =
                          let uu___4 =
                            let uu___5 = FStar_Syntax_Subst.close binders t in
                            FStar_Syntax_Subst.compress uu___5 in
                          uu___4.FStar_Syntax_Syntax.n in
                        (match uu___3 with
                         | FStar_Syntax_Syntax.Tm_abs (bs1, uu___4, uu___5)
                             -> bs1
                         | uu___4 -> failwith "Impossible") in
                  let erase_term1 t =
                    let uu___2 =
                      let uu___3 = FStar_Syntax_Subst.subst opening t in
                      erase_univs uu___3 in
                    FStar_Syntax_Subst.close binders uu___2 in
                  let uu___2 = action in
                  let uu___3 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn in
                  let uu___4 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___2.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___2.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu___3;
                    FStar_Syntax_Syntax.action_typ = uu___4
                  } in
                let uu___2 = ed in
                let uu___3 = FStar_Syntax_Subst.close_binders binders in
                let uu___4 = erase_tscheme ed.FStar_Syntax_Syntax.signature in
                let uu___5 =
                  FStar_Syntax_Util.apply_eff_combinators erase_tscheme
                    ed.FStar_Syntax_Syntax.combinators in
                let uu___6 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions in
                {
                  FStar_Syntax_Syntax.mname =
                    (uu___2.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.cattributes =
                    (uu___2.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu___3;
                  FStar_Syntax_Syntax.signature = uu___4;
                  FStar_Syntax_Syntax.combinators = uu___5;
                  FStar_Syntax_Syntax.actions = uu___6;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___2.FStar_Syntax_Syntax.eff_attrs)
                } in
          let push_sigelt env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___ = se in
                  let uu___1 =
                    let uu___2 = erase_univs_ed ed in
                    FStar_Syntax_Syntax.Sig_new_effect uu___2 in
                  {
                    FStar_Syntax_Syntax.sigel = uu___1;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___.FStar_Syntax_Syntax.sigattrs);
                    FStar_Syntax_Syntax.sigopts =
                      (uu___.FStar_Syntax_Syntax.sigopts)
                  } in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se' in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu___ -> FStar_Syntax_DsEnv.push_sigelt env se in
          let uu___ =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii in
          match uu___ with
          | (en1, pop_when_done) ->
              let en2 =
                let uu___1 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name in
                FStar_List.fold_left push_sigelt uu___1
                  m.FStar_Syntax_Syntax.declarations in
              let env = FStar_Syntax_DsEnv.finish en2 m in
              let uu___1 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env in
              ((), uu___1)