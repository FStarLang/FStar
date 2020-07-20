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
             (fun uu____109 ->
                match uu____109 with
                | (pat, annots) ->
                    let branch1 =
                      FStar_List.fold_left
                        (fun br ->
                           fun uu____164 ->
                             match uu____164 with
                             | (bv, ty) ->
                                 let lb =
                                   let uu____182 =
                                     FStar_Syntax_Syntax.bv_to_name bv in
                                   FStar_Syntax_Util.mk_letbinding
                                     (FStar_Util.Inl bv) [] ty
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____182 [] br.FStar_Syntax_Syntax.pos in
                                 let branch1 =
                                   let uu____188 =
                                     let uu____189 =
                                       FStar_Syntax_Syntax.mk_binder bv in
                                     [uu____189] in
                                   FStar_Syntax_Subst.close uu____188 branch in
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
      fun uu___0_242 ->
        match uu___0_242 with
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
  fun uu___1_251 ->
    match uu___1_251 with
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
  fun uu___2_265 ->
    match uu___2_265 with
    | FStar_Parser_AST.Hash ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | uu____268 -> FStar_Pervasives_Native.None
let arg_withimp_e :
  'uuuuuu275 .
    FStar_Parser_AST.imp ->
      'uuuuuu275 ->
        ('uuuuuu275 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  = fun imp -> fun t -> (t, (as_imp imp))
let arg_withimp_t :
  'uuuuuu300 .
    FStar_Parser_AST.imp ->
      'uuuuuu300 ->
        ('uuuuuu300 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  =
  fun imp ->
    fun t ->
      match imp with
      | FStar_Parser_AST.Hash ->
          (t, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag))
      | uu____319 -> (t, FStar_Pervasives_Native.None)
let (contains_binder : FStar_Parser_AST.binder Prims.list -> Prims.bool) =
  fun binders ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____336 -> true
            | uu____341 -> false))
let rec (unparen : FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun t ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____348 -> t
let (tm_type_z : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r ->
    let uu____354 =
      let uu____355 = FStar_Ident.lid_of_path ["Type0"] r in
      FStar_Parser_AST.Name uu____355 in
    FStar_Parser_AST.mk_term uu____354 r FStar_Parser_AST.Kind
let (tm_type : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r ->
    let uu____361 =
      let uu____362 = FStar_Ident.lid_of_path ["Type"] r in
      FStar_Parser_AST.Name uu____362 in
    FStar_Parser_AST.mk_term uu____361 r FStar_Parser_AST.Kind
let rec (is_comp_type :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun env ->
    fun t ->
      let uu____373 =
        let uu____374 = unparen t in uu____374.FStar_Parser_AST.tm in
      match uu____373 with
      | FStar_Parser_AST.Name l ->
          let uu____376 = FStar_Syntax_DsEnv.try_lookup_effect_name env l in
          FStar_All.pipe_right uu____376 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l, uu____382) ->
          let uu____395 = FStar_Syntax_DsEnv.try_lookup_effect_name env l in
          FStar_All.pipe_right uu____395 FStar_Option.isSome
      | FStar_Parser_AST.App (head, uu____401, uu____402) ->
          is_comp_type env head
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1, uu____405, uu____406) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____411, t1) -> is_comp_type env t1
      | uu____413 -> false
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
  'uuuuuu501 .
    'uuuuuu501 ->
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
        let uu____547 =
          let uu____548 =
            let uu____549 =
              let uu____554 = FStar_Parser_AST.compile_op n s r in
              (uu____554, r) in
            FStar_Ident.mk_ident uu____549 in
          [uu____548] in
        FStar_All.pipe_right uu____547 FStar_Ident.lid_of_ids
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
          let uu____587 =
            let uu____588 =
              let uu____589 =
                let uu____590 = FStar_Ident.range_of_id op in
                FStar_Ident.set_lid_range l uu____590 in
              FStar_Syntax_Syntax.lid_as_fv uu____589 dd
                FStar_Pervasives_Native.None in
            FStar_All.pipe_right uu____588 FStar_Syntax_Syntax.fv_to_tm in
          FStar_Pervasives_Native.Some uu____587 in
        let fallback uu____598 =
          let uu____599 = FStar_Ident.string_of_id op in
          match uu____599 with
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
              let uu____602 = FStar_Options.ml_ish () in
              if uu____602
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
          | uu____606 -> FStar_Pervasives_Native.None in
        let uu____607 =
          let uu____610 =
            let uu____611 = FStar_Ident.string_of_id op in
            let uu____612 = FStar_Ident.range_of_id op in
            compile_op_lid arity uu____611 uu____612 in
          desugar_name'
            (fun t ->
               let uu___180_620 = t in
               let uu____621 = FStar_Ident.range_of_id op in
               {
                 FStar_Syntax_Syntax.n = (uu___180_620.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = uu____621;
                 FStar_Syntax_Syntax.vars =
                   (uu___180_620.FStar_Syntax_Syntax.vars)
               }) env true uu____610 in
        match uu____607 with
        | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
        | uu____625 -> fallback ()
let (sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list)
  =
  fun ftv ->
    let uu____639 =
      FStar_Util.remove_dups
        (fun x ->
           fun y ->
             let uu____648 = FStar_Ident.string_of_id x in
             let uu____649 = FStar_Ident.string_of_id y in
             uu____648 = uu____649) ftv in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x ->
            fun y ->
              let uu____660 = FStar_Ident.string_of_id x in
              let uu____661 = FStar_Ident.string_of_id y in
              FStar_String.compare uu____660 uu____661)) uu____639
let rec (free_type_vars_b :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Syntax_DsEnv.env * FStar_Ident.ident Prims.list))
  =
  fun env ->
    fun binder ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____694 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____698 = FStar_Syntax_DsEnv.push_bv env x in
          (match uu____698 with | (env1, uu____710) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____713, term) ->
          let uu____715 = free_type_vars env term in (env, uu____715)
      | FStar_Parser_AST.TAnnotated (id, uu____721) ->
          let uu____722 = FStar_Syntax_DsEnv.push_bv env id in
          (match uu____722 with | (env1, uu____734) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____738 = free_type_vars env t in (env, uu____738)
and (free_type_vars :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list)
  =
  fun env ->
    fun t ->
      let uu____745 =
        let uu____746 = unparen t in uu____746.FStar_Parser_AST.tm in
      match uu____745 with
      | FStar_Parser_AST.Labeled uu____749 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____759 = FStar_Syntax_DsEnv.try_lookup_id env a in
          (match uu____759 with
           | FStar_Pervasives_Native.None -> [a]
           | uu____764 -> [])
      | FStar_Parser_AST.Wild -> []
      | FStar_Parser_AST.Const uu____767 -> []
      | FStar_Parser_AST.Uvar uu____768 -> []
      | FStar_Parser_AST.Var uu____769 -> []
      | FStar_Parser_AST.Projector uu____770 -> []
      | FStar_Parser_AST.Discrim uu____775 -> []
      | FStar_Parser_AST.Name uu____776 -> []
      | FStar_Parser_AST.Requires (t1, uu____778) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1, uu____784) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____789, t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1, t', tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None -> []
             | FStar_Pervasives_Native.Some t2 -> [t2]) in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____807, ts) ->
          FStar_List.collect
            (fun uu____828 ->
               match uu____828 with
               | (t1, uu____836) -> free_type_vars env t1) ts
      | FStar_Parser_AST.Op (uu____837, ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1, t2, uu____845) ->
          let uu____846 = free_type_vars env t1 in
          let uu____849 = free_type_vars env t2 in
          FStar_List.append uu____846 uu____849
      | FStar_Parser_AST.Refine (b, t1) ->
          let uu____854 = free_type_vars_b env b in
          (match uu____854 with
           | (env1, f) ->
               let uu____869 = free_type_vars env1 t1 in
               FStar_List.append f uu____869)
      | FStar_Parser_AST.Sum (binders, body) ->
          let uu____886 =
            FStar_List.fold_left
              (fun uu____910 ->
                 fun bt ->
                   match uu____910 with
                   | (env1, free) ->
                       let uu____934 =
                         match bt with
                         | FStar_Util.Inl binder ->
                             free_type_vars_b env1 binder
                         | FStar_Util.Inr t1 ->
                             let uu____949 = free_type_vars env1 body in
                             (env1, uu____949) in
                       (match uu____934 with
                        | (env2, f) -> (env2, (FStar_List.append f free))))
              (env, []) binders in
          (match uu____886 with
           | (env1, free) ->
               let uu____978 = free_type_vars env1 body in
               FStar_List.append free uu____978)
      | FStar_Parser_AST.Product (binders, body) ->
          let uu____987 =
            FStar_List.fold_left
              (fun uu____1007 ->
                 fun binder ->
                   match uu____1007 with
                   | (env1, free) ->
                       let uu____1027 = free_type_vars_b env1 binder in
                       (match uu____1027 with
                        | (env2, f) -> (env2, (FStar_List.append f free))))
              (env, []) binders in
          (match uu____987 with
           | (env1, free) ->
               let uu____1058 = free_type_vars env1 body in
               FStar_List.append free uu____1058)
      | FStar_Parser_AST.Project (t1, uu____1062) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.CalcProof (rel, init, steps) ->
          let uu____1073 = free_type_vars env rel in
          let uu____1076 =
            let uu____1079 = free_type_vars env init in
            let uu____1082 =
              FStar_List.collect
                (fun uu____1091 ->
                   match uu____1091 with
                   | FStar_Parser_AST.CalcStep (rel1, just, next) ->
                       let uu____1097 = free_type_vars env rel1 in
                       let uu____1100 =
                         let uu____1103 = free_type_vars env just in
                         let uu____1106 = free_type_vars env next in
                         FStar_List.append uu____1103 uu____1106 in
                       FStar_List.append uu____1097 uu____1100) steps in
            FStar_List.append uu____1079 uu____1082 in
          FStar_List.append uu____1073 uu____1076
      | FStar_Parser_AST.Abs uu____1109 -> []
      | FStar_Parser_AST.Let uu____1116 -> []
      | FStar_Parser_AST.LetOpen uu____1137 -> []
      | FStar_Parser_AST.If uu____1142 -> []
      | FStar_Parser_AST.QForall uu____1149 -> []
      | FStar_Parser_AST.QExists uu____1168 -> []
      | FStar_Parser_AST.Record uu____1187 -> []
      | FStar_Parser_AST.Match uu____1200 -> []
      | FStar_Parser_AST.TryWith uu____1215 -> []
      | FStar_Parser_AST.Bind uu____1230 -> []
      | FStar_Parser_AST.Quote uu____1237 -> []
      | FStar_Parser_AST.VQuote uu____1242 -> []
      | FStar_Parser_AST.Antiquote uu____1243 -> []
      | FStar_Parser_AST.Seq uu____1244 -> []
let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun t ->
    let rec aux args t1 =
      let uu____1297 =
        let uu____1298 = unparen t1 in uu____1298.FStar_Parser_AST.tm in
      match uu____1297 with
      | FStar_Parser_AST.App (t2, arg, imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l, args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____1340 -> (t1, args) in
    aux [] t
let (close :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env ->
    fun t ->
      let ftv =
        let uu____1364 = free_type_vars env t in
        FStar_All.pipe_left sort_ftv uu____1364 in
      if (FStar_List.length ftv) = Prims.int_zero
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x ->
                   let uu____1383 =
                     let uu____1384 =
                       let uu____1389 =
                         let uu____1390 = FStar_Ident.range_of_id x in
                         tm_type uu____1390 in
                       (x, uu____1389) in
                     FStar_Parser_AST.TAnnotated uu____1384 in
                   let uu____1391 = FStar_Ident.range_of_id x in
                   FStar_Parser_AST.mk_binder uu____1383 uu____1391
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
        let uu____1408 = free_type_vars env t in
        FStar_All.pipe_left sort_ftv uu____1408 in
      if (FStar_List.length ftv) = Prims.int_zero
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x ->
                   let uu____1427 =
                     let uu____1428 =
                       let uu____1433 =
                         let uu____1434 = FStar_Ident.range_of_id x in
                         tm_type uu____1434 in
                       (x, uu____1433) in
                     FStar_Parser_AST.TAnnotated uu____1428 in
                   let uu____1435 = FStar_Ident.range_of_id x in
                   FStar_Parser_AST.mk_binder uu____1427 uu____1435
                     FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit))) in
         let t1 =
           let uu____1437 =
             let uu____1438 = unparen t in uu____1438.FStar_Parser_AST.tm in
           match uu____1437 with
           | FStar_Parser_AST.Product uu____1439 -> t
           | uu____1446 ->
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
      | uu____1482 -> (bs, t)
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild uu____1490 -> true
    | FStar_Parser_AST.PatTvar (uu____1493, uu____1494) -> true
    | FStar_Parser_AST.PatVar (uu____1499, uu____1500) -> true
    | FStar_Parser_AST.PatAscribed (p1, uu____1506) -> is_var_pattern p1
    | uu____1519 -> false
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1, uu____1526) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____1539;
           FStar_Parser_AST.prange = uu____1540;_},
         uu____1541)
        -> true
    | uu____1552 -> false
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
    | uu____1566 -> p
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
            let uu____1636 = destruct_app_pattern env is_top_level p1 in
            (match uu____1636 with
             | (name, args, uu____1679) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id, uu____1729);
               FStar_Parser_AST.prange = uu____1730;_},
             args)
            when is_top_level ->
            let uu____1740 =
              let uu____1745 = FStar_Syntax_DsEnv.qualify env id in
              FStar_Util.Inr uu____1745 in
            (uu____1740, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id, uu____1767);
               FStar_Parser_AST.prange = uu____1768;_},
             args)
            -> ((FStar_Util.Inl id), args, FStar_Pervasives_Native.None)
        | uu____1798 -> failwith "Not an app pattern"
let rec (gather_pattern_bound_vars_maybe_top :
  FStar_Ident.ident FStar_Util.set ->
    FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set)
  =
  fun acc ->
    fun p ->
      let gather_pattern_bound_vars_from_list =
        FStar_List.fold_left gather_pattern_bound_vars_maybe_top acc in
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatWild uu____1848 -> acc
      | FStar_Parser_AST.PatConst uu____1851 -> acc
      | FStar_Parser_AST.PatName uu____1852 -> acc
      | FStar_Parser_AST.PatOp uu____1853 -> acc
      | FStar_Parser_AST.PatApp (phead, pats) ->
          gather_pattern_bound_vars_from_list (phead :: pats)
      | FStar_Parser_AST.PatTvar (x, uu____1861) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatVar (x, uu____1867) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatTuple (pats, uu____1876) ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu____1891 =
            FStar_List.map FStar_Pervasives_Native.snd guarded_pats in
          gather_pattern_bound_vars_from_list uu____1891
      | FStar_Parser_AST.PatAscribed (pat, uu____1899) ->
          gather_pattern_bound_vars_maybe_top acc pat
let (gather_pattern_bound_vars :
  FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set) =
  let acc =
    FStar_Util.new_set
      (fun id1 ->
         fun id2 ->
           let uu____1926 =
             let uu____1927 = FStar_Ident.string_of_id id1 in
             let uu____1928 = FStar_Ident.string_of_id id2 in
             uu____1927 = uu____1928 in
           if uu____1926 then Prims.int_zero else Prims.int_one) in
  fun p -> gather_pattern_bound_vars_maybe_top acc p
type bnd =
  | LocalBinder of (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) 
  | LetBinder of (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)) 
let (uu___is_LocalBinder : bnd -> Prims.bool) =
  fun projectee ->
    match projectee with | LocalBinder _0 -> true | uu____1965 -> false
let (__proj__LocalBinder__item___0 :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun projectee -> match projectee with | LocalBinder _0 -> _0
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee ->
    match projectee with | LetBinder _0 -> true | uu____2000 -> false
let (__proj__LetBinder__item___0 :
  bnd ->
    (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)))
  = fun projectee -> match projectee with | LetBinder _0 -> _0
let (is_implicit : bnd -> Prims.bool) =
  fun b ->
    match b with
    | LocalBinder
        (uu____2042, FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____2043))
        -> true
    | uu____2044 -> false
let (binder_of_bnd :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun uu___3_2053 ->
    match uu___3_2053 with
    | LocalBinder (a, aq) -> (a, aq)
    | uu____2060 -> failwith "Impossible"
let (mk_lb :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list *
    (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Range.range)
    -> FStar_Syntax_Syntax.letbinding)
  =
  fun uu____2091 ->
    match uu____2091 with
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
      let uu____2171 =
        let uu____2188 =
          let uu____2191 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
          FStar_Syntax_Syntax.fv_to_tm uu____2191 in
        let uu____2192 =
          let uu____2203 =
            let uu____2212 = FStar_Syntax_Syntax.as_implicit false in
            (tm, uu____2212) in
          [uu____2203] in
        (uu____2188, uu____2192) in
      FStar_Syntax_Syntax.Tm_app uu____2171 in
    FStar_Syntax_Syntax.mk tm' tm.FStar_Syntax_Syntax.pos
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm ->
    let tm' =
      let uu____2259 =
        let uu____2276 =
          let uu____2279 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
          FStar_Syntax_Syntax.fv_to_tm uu____2279 in
        let uu____2280 =
          let uu____2291 =
            let uu____2300 = FStar_Syntax_Syntax.as_implicit false in
            (tm, uu____2300) in
          [uu____2291] in
        (uu____2276, uu____2280) in
      FStar_Syntax_Syntax.Tm_app uu____2259 in
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
          let uu____2361 =
            let uu____2378 =
              let uu____2381 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Syntax_Syntax.fv_to_tm uu____2381 in
            let uu____2382 =
              let uu____2393 =
                let uu____2402 = FStar_Syntax_Syntax.as_implicit false in
                (t1, uu____2402) in
              let uu____2409 =
                let uu____2420 =
                  let uu____2429 = FStar_Syntax_Syntax.as_implicit false in
                  (t2, uu____2429) in
                [uu____2420] in
              uu____2393 :: uu____2409 in
            (uu____2378, uu____2382) in
          FStar_Syntax_Syntax.Tm_app uu____2361 in
        FStar_Syntax_Syntax.mk tm pos
let rec (generalize_annotated_univs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun s ->
    let bs_univnames bs =
      let uu____2487 =
        let uu____2502 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name in
        FStar_List.fold_left
          (fun uvs ->
             fun uu____2521 ->
               match uu____2521 with
               | ({ FStar_Syntax_Syntax.ppname = uu____2532;
                    FStar_Syntax_Syntax.index = uu____2533;
                    FStar_Syntax_Syntax.sort = t;_},
                  uu____2535) ->
                   let uu____2542 = FStar_Syntax_Free.univnames t in
                   FStar_Util.set_union uvs uu____2542) uu____2502 in
      FStar_All.pipe_right bs uu____2487 in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____2558 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____2575 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs, lids) ->
        let uvs =
          let uu____2601 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs ->
                    fun se ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____2622, uu____2623, bs, t, uu____2626,
                             uu____2627)
                            ->
                            let uu____2636 = bs_univnames bs in
                            let uu____2639 = FStar_Syntax_Free.univnames t in
                            FStar_Util.set_union uu____2636 uu____2639
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____2642, uu____2643, t, uu____2645,
                             uu____2646, uu____2647)
                            -> FStar_Syntax_Free.univnames t
                        | uu____2652 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt" in
                      FStar_Util.set_union uvs se_univs) empty_set) in
          FStar_All.pipe_right uu____2601 FStar_Util.set_elements in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs in
        let uu___567_2660 = s in
        let uu____2661 =
          let uu____2662 =
            let uu____2671 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid, uu____2689, bs, t, lids1, lids2) ->
                          let uu___578_2702 = se in
                          let uu____2703 =
                            let uu____2704 =
                              let uu____2721 =
                                FStar_Syntax_Subst.subst_binders usubst bs in
                              let uu____2722 =
                                let uu____2723 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst in
                                FStar_Syntax_Subst.subst uu____2723 t in
                              (lid, uvs, uu____2721, uu____2722, lids1,
                                lids2) in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____2704 in
                          {
                            FStar_Syntax_Syntax.sigel = uu____2703;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___578_2702.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___578_2702.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___578_2702.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___578_2702.FStar_Syntax_Syntax.sigattrs);
                            FStar_Syntax_Syntax.sigopts =
                              (uu___578_2702.FStar_Syntax_Syntax.sigopts)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid, uu____2737, t, tlid, n, lids1) ->
                          let uu___588_2746 = se in
                          let uu____2747 =
                            let uu____2748 =
                              let uu____2763 =
                                FStar_Syntax_Subst.subst usubst t in
                              (lid, uvs, uu____2763, tlid, n, lids1) in
                            FStar_Syntax_Syntax.Sig_datacon uu____2748 in
                          {
                            FStar_Syntax_Syntax.sigel = uu____2747;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___588_2746.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___588_2746.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___588_2746.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___588_2746.FStar_Syntax_Syntax.sigattrs);
                            FStar_Syntax_Syntax.sigopts =
                              (uu___588_2746.FStar_Syntax_Syntax.sigopts)
                          }
                      | uu____2766 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt")) in
            (uu____2671, lids) in
          FStar_Syntax_Syntax.Sig_bundle uu____2662 in
        {
          FStar_Syntax_Syntax.sigel = uu____2661;
          FStar_Syntax_Syntax.sigrng =
            (uu___567_2660.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___567_2660.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___567_2660.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___567_2660.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___567_2660.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____2772, t) ->
        let uvs =
          let uu____2775 = FStar_Syntax_Free.univnames t in
          FStar_All.pipe_right uu____2775 FStar_Util.set_elements in
        let uu___597_2780 = s in
        let uu____2781 =
          let uu____2782 =
            let uu____2789 = FStar_Syntax_Subst.close_univ_vars uvs t in
            (lid, uvs, uu____2789) in
          FStar_Syntax_Syntax.Sig_declare_typ uu____2782 in
        {
          FStar_Syntax_Syntax.sigel = uu____2781;
          FStar_Syntax_Syntax.sigrng =
            (uu___597_2780.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___597_2780.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___597_2780.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___597_2780.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___597_2780.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_let ((b, lbs), lids) ->
        let lb_univnames lb =
          let uu____2811 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp in
          let uu____2814 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs, e, uu____2821) ->
                let uvs1 = bs_univnames bs in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____2854, (FStar_Util.Inl t, uu____2856),
                       uu____2857)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____2904, (FStar_Util.Inr c, uu____2906),
                       uu____2907)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____2954 -> empty_set in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_arrow (bs, uu____2956) ->
                bs_univnames bs
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____2977, (FStar_Util.Inl t, uu____2979), uu____2980) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____3027, (FStar_Util.Inr c, uu____3029), uu____3030) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____3077 -> empty_set in
          FStar_Util.set_union uu____2811 uu____2814 in
        let all_lb_univs =
          let uu____3081 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs ->
                    fun lb ->
                      let uu____3097 = lb_univnames lb in
                      FStar_Util.set_union uvs uu____3097) empty_set) in
          FStar_All.pipe_right uu____3081 FStar_Util.set_elements in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs in
        let uu___656_3107 = s in
        let uu____3108 =
          let uu____3109 =
            let uu____3116 =
              let uu____3117 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb ->
                        let uu___659_3129 = lb in
                        let uu____3130 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp in
                        let uu____3133 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___659_3129.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____3130;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___659_3129.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____3133;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___659_3129.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___659_3129.FStar_Syntax_Syntax.lbpos)
                        })) in
              (b, uu____3117) in
            (uu____3116, lids) in
          FStar_Syntax_Syntax.Sig_let uu____3109 in
        {
          FStar_Syntax_Syntax.sigel = uu____3108;
          FStar_Syntax_Syntax.sigrng =
            (uu___656_3107.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___656_3107.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___656_3107.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___656_3107.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___656_3107.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid, uu____3141, fml) ->
        let uvs =
          let uu____3144 = FStar_Syntax_Free.univnames fml in
          FStar_All.pipe_right uu____3144 FStar_Util.set_elements in
        let uu___667_3149 = s in
        let uu____3150 =
          let uu____3151 =
            let uu____3158 = FStar_Syntax_Subst.close_univ_vars uvs fml in
            (lid, uvs, uu____3158) in
          FStar_Syntax_Syntax.Sig_assume uu____3151 in
        {
          FStar_Syntax_Syntax.sigel = uu____3150;
          FStar_Syntax_Syntax.sigrng =
            (uu___667_3149.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___667_3149.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___667_3149.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___667_3149.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___667_3149.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uu____3160, bs, c, flags)
        ->
        let uvs =
          let uu____3169 =
            let uu____3172 = bs_univnames bs in
            let uu____3175 = FStar_Syntax_Free.univnames_comp c in
            FStar_Util.set_union uu____3172 uu____3175 in
          FStar_All.pipe_right uu____3169 FStar_Util.set_elements in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs in
        let uu___678_3183 = s in
        let uu____3184 =
          let uu____3185 =
            let uu____3198 = FStar_Syntax_Subst.subst_binders usubst bs in
            let uu____3199 = FStar_Syntax_Subst.subst_comp usubst c in
            (lid, uvs, uu____3198, uu____3199, flags) in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____3185 in
        {
          FStar_Syntax_Syntax.sigel = uu____3184;
          FStar_Syntax_Syntax.sigrng =
            (uu___678_3183.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___678_3183.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___678_3183.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___678_3183.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___678_3183.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_fail (errs, lax, ses) ->
        let uu___685_3213 = s in
        let uu____3214 =
          let uu____3215 =
            let uu____3226 = FStar_List.map generalize_annotated_univs ses in
            (errs, lax, uu____3226) in
          FStar_Syntax_Syntax.Sig_fail uu____3215 in
        {
          FStar_Syntax_Syntax.sigel = uu____3214;
          FStar_Syntax_Syntax.sigrng =
            (uu___685_3213.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___685_3213.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___685_3213.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___685_3213.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___685_3213.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_new_effect uu____3233 -> s
    | FStar_Syntax_Syntax.Sig_sub_effect uu____3234 -> s
    | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____3235 -> s
    | FStar_Syntax_Syntax.Sig_polymonadic_subcomp uu____3246 -> s
    | FStar_Syntax_Syntax.Sig_splice uu____3255 -> s
    | FStar_Syntax_Syntax.Sig_pragma uu____3262 -> s
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___4_3267 ->
    match uu___4_3267 with
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
    | uu____3268 -> false
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u ->
    fun n ->
      if n = Prims.int_zero
      then u
      else
        (let uu____3280 = sum_to_universe u (n - Prims.int_one) in
         FStar_Syntax_Syntax.U_succ uu____3280)
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n -> sum_to_universe FStar_Syntax_Syntax.U_zero n
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int, FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t ->
    let uu____3299 =
      let uu____3300 = unparen t in uu____3300.FStar_Parser_AST.tm in
    match uu____3299 with
    | FStar_Parser_AST.Wild -> FStar_Util.Inr FStar_Syntax_Syntax.U_unknown
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr, uu____3307)) ->
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
             let uu____3372 = sum_to_universe u n in
             FStar_Util.Inr uu____3372
         | (FStar_Util.Inr u, FStar_Util.Inl n) ->
             let uu____3383 = sum_to_universe u n in
             FStar_Util.Inr uu____3383
         | (FStar_Util.Inr u11, FStar_Util.Inr u21) ->
             let uu____3394 =
               let uu____3399 =
                 let uu____3400 = FStar_Parser_AST.term_to_string t in
                 Prims.op_Hat
                   "This universe might contain a sum of two universe variables "
                   uu____3400 in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____3399) in
             FStar_Errors.raise_error uu____3394 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____3405 ->
        let rec aux t1 univargs =
          let uu____3439 =
            let uu____3440 = unparen t1 in uu____3440.FStar_Parser_AST.tm in
          match uu____3439 with
          | FStar_Parser_AST.App (t2, targ, uu____3447) ->
              let uarg = desugar_maybe_non_constant_universe targ in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid ->
              if
                FStar_List.existsb
                  (fun uu___5_3470 ->
                     match uu___5_3470 with
                     | FStar_Util.Inr uu____3475 -> true
                     | uu____3476 -> false) univargs
              then
                let uu____3481 =
                  let uu____3482 =
                    FStar_List.map
                      (fun uu___6_3491 ->
                         match uu___6_3491 with
                         | FStar_Util.Inl n -> int_to_universe n
                         | FStar_Util.Inr u -> u) univargs in
                  FStar_Syntax_Syntax.U_max uu____3482 in
                FStar_Util.Inr uu____3481
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___7_3508 ->
                        match uu___7_3508 with
                        | FStar_Util.Inl n -> n
                        | FStar_Util.Inr uu____3514 -> failwith "impossible")
                     univargs in
                 let uu____3515 =
                   FStar_List.fold_left
                     (fun m -> fun n -> if m > n then m else n)
                     Prims.int_zero nargs in
                 FStar_Util.Inl uu____3515)
          | uu____3521 ->
              let uu____3522 =
                let uu____3527 =
                  let uu____3528 =
                    let uu____3529 = FStar_Parser_AST.term_to_string t1 in
                    Prims.op_Hat uu____3529 " in universe context" in
                  Prims.op_Hat "Unexpected term " uu____3528 in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3527) in
              FStar_Errors.raise_error uu____3522 t1.FStar_Parser_AST.range in
        aux t []
    | uu____3538 ->
        let uu____3539 =
          let uu____3544 =
            let uu____3545 =
              let uu____3546 = FStar_Parser_AST.term_to_string t in
              Prims.op_Hat uu____3546 " in universe context" in
            Prims.op_Hat "Unexpected term " uu____3545 in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3544) in
        FStar_Errors.raise_error uu____3539 t.FStar_Parser_AST.range
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
              FStar_Syntax_Syntax.antiquotes = uu____3576;_});
         FStar_Syntax_Syntax.pos = uu____3577;
         FStar_Syntax_Syntax.vars = uu____3578;_})::uu____3579
        ->
        let uu____3610 =
          let uu____3615 =
            let uu____3616 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____3616 in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____3615) in
        FStar_Errors.raise_error uu____3610 e.FStar_Syntax_Syntax.pos
    | (bv, e)::uu____3619 ->
        let uu____3638 =
          let uu____3643 =
            let uu____3644 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____3644 in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____3643) in
        FStar_Errors.raise_error uu____3638 e.FStar_Syntax_Syntax.pos
let check_fields :
  'uuuuuu3653 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident * 'uuuuuu3653) Prims.list ->
        FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env ->
    fun fields ->
      fun rg ->
        let uu____3681 = FStar_List.hd fields in
        match uu____3681 with
        | (f, uu____3691) ->
            let record =
              FStar_Syntax_DsEnv.fail_or env
                (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f in
            let check_field uu____3702 =
              match uu____3702 with
              | (f', uu____3708) ->
                  let uu____3709 =
                    FStar_Syntax_DsEnv.belongs_to_record env f' record in
                  if uu____3709
                  then ()
                  else
                    (let msg =
                       let uu____3712 = FStar_Ident.string_of_lid f in
                       let uu____3713 =
                         FStar_Ident.string_of_lid
                           record.FStar_Syntax_DsEnv.typename in
                       let uu____3714 = FStar_Ident.string_of_lid f' in
                       FStar_Util.format3
                         "Field %s belongs to record type %s, whereas field %s does not"
                         uu____3712 uu____3713 uu____3714 in
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FieldsNotBelongToSameRecordType,
                         msg) rg) in
            ((let uu____3716 = FStar_List.tl fields in
              FStar_List.iter check_field uu____3716);
             (match () with | () -> record))
let (check_linear_pattern_variables :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t Prims.list ->
    FStar_Range.range -> unit)
  =
  fun pats ->
    fun r ->
      let rec pat_vars p =
        match p.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_dot_term uu____3763 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_wild uu____3770 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_constant uu____3771 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_var x ->
            FStar_Util.set_add x FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_cons (uu____3773, pats1) ->
            let aux out uu____3811 =
              match uu____3811 with
              | (p1, uu____3823) ->
                  let intersection =
                    let uu____3831 = pat_vars p1 in
                    FStar_Util.set_intersect uu____3831 out in
                  let uu____3834 = FStar_Util.set_is_empty intersection in
                  if uu____3834
                  then
                    let uu____3837 = pat_vars p1 in
                    FStar_Util.set_union out uu____3837
                  else
                    (let duplicate_bv =
                       let uu____3842 = FStar_Util.set_elements intersection in
                       FStar_List.hd uu____3842 in
                     let uu____3845 =
                       let uu____3850 =
                         let uu____3851 =
                           FStar_Ident.string_of_id
                             duplicate_bv.FStar_Syntax_Syntax.ppname in
                         FStar_Util.format1
                           "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                           uu____3851 in
                       (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                         uu____3850) in
                     FStar_Errors.raise_error uu____3845 r) in
            FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1 in
      match pats with
      | [] -> ()
      | p::[] ->
          let uu____3871 = pat_vars p in
          FStar_All.pipe_right uu____3871 (fun uu____3876 -> ())
      | p::ps ->
          let pvars = pat_vars p in
          let aux p1 =
            let uu____3900 =
              let uu____3901 = pat_vars p1 in
              FStar_Util.set_eq pvars uu____3901 in
            if uu____3900
            then ()
            else
              (let nonlinear_vars =
                 let uu____3908 = pat_vars p1 in
                 FStar_Util.set_symmetric_difference pvars uu____3908 in
               let first_nonlinear_var =
                 let uu____3912 = FStar_Util.set_elements nonlinear_vars in
                 FStar_List.hd uu____3912 in
               let uu____3915 =
                 let uu____3920 =
                   let uu____3921 =
                     FStar_Ident.string_of_id
                       first_nonlinear_var.FStar_Syntax_Syntax.ppname in
                   FStar_Util.format1
                     "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                     uu____3921 in
                 (FStar_Errors.Fatal_IncoherentPatterns, uu____3920) in
               FStar_Errors.raise_error uu____3915 r) in
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
          let uu____4235 =
            FStar_Util.find_opt
              (fun y ->
                 let uu____4242 =
                   FStar_Ident.string_of_id y.FStar_Syntax_Syntax.ppname in
                 let uu____4243 = FStar_Ident.string_of_id x in
                 uu____4242 = uu____4243) l in
          match uu____4235 with
          | FStar_Pervasives_Native.Some y -> (l, e, y)
          | uu____4255 ->
              let uu____4258 = FStar_Syntax_DsEnv.push_bv e x in
              (match uu____4258 with | (e1, xbv) -> ((xbv :: l), e1, xbv)) in
        let rec aux' top loc env1 p1 =
          let pos q =
            FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange in
          let pos_r r q = FStar_Syntax_Syntax.withinfo q r in
          let orig = p1 in
          match p1.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOr uu____4397 ->
              failwith "impossible: PatOr handled below"
          | FStar_Parser_AST.PatOp op ->
              let id_op =
                let uu____4418 =
                  let uu____4423 =
                    let uu____4424 = FStar_Ident.string_of_id op in
                    let uu____4425 = FStar_Ident.range_of_id op in
                    FStar_Parser_AST.compile_op Prims.int_zero uu____4424
                      uu____4425 in
                  let uu____4426 = FStar_Ident.range_of_id op in
                  (uu____4423, uu____4426) in
                FStar_Ident.mk_ident uu____4418 in
              let p2 =
                let uu___912_4428 = p1 in
                {
                  FStar_Parser_AST.pat =
                    (FStar_Parser_AST.PatVar
                       (id_op, FStar_Pervasives_Native.None));
                  FStar_Parser_AST.prange =
                    (uu___912_4428.FStar_Parser_AST.prange)
                } in
              aux loc env1 p2
          | FStar_Parser_AST.PatAscribed (p2, (t, tacopt)) ->
              ((match tacopt with
                | FStar_Pervasives_Native.None -> ()
                | FStar_Pervasives_Native.Some uu____4445 ->
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                        "Type ascriptions within patterns cannot be associated with a tactic")
                      orig.FStar_Parser_AST.prange);
               (let uu____4446 = aux loc env1 p2 in
                match uu____4446 with
                | (loc1, env', binder, p3, annots) ->
                    let uu____4502 =
                      match binder with
                      | LetBinder uu____4523 -> failwith "impossible"
                      | LocalBinder (x, aq) ->
                          let t1 =
                            let uu____4547 = close_fun env1 t in
                            desugar_term env1 uu____4547 in
                          let x1 =
                            let uu___938_4549 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___938_4549.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___938_4549.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            } in
                          ([(x1, t1)], (LocalBinder (x1, aq))) in
                    (match uu____4502 with
                     | (annots', binder1) ->
                         ((match p3.FStar_Syntax_Syntax.v with
                           | FStar_Syntax_Syntax.Pat_var uu____4595 -> ()
                           | FStar_Syntax_Syntax.Pat_wild uu____4596 -> ()
                           | uu____4597 when top && top_level_ascr_allowed ->
                               ()
                           | uu____4598 ->
                               FStar_Errors.raise_error
                                 (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                                   "Type ascriptions within patterns are only allowed on variables")
                                 orig.FStar_Parser_AST.prange);
                          (loc1, env', binder1, p3,
                            (FStar_List.append annots' annots))))))
          | FStar_Parser_AST.PatWild aq ->
              let aq1 = trans_aqual env1 aq in
              let x =
                let uu____4614 = tun_r p1.FStar_Parser_AST.prange in
                FStar_Syntax_Syntax.new_bv
                  (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                  uu____4614 in
              let uu____4615 =
                FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x) in
              (loc, env1, (LocalBinder (x, aq1)), uu____4615, [])
          | FStar_Parser_AST.PatConst c ->
              let x =
                let uu____4628 = tun_r p1.FStar_Parser_AST.prange in
                FStar_Syntax_Syntax.new_bv
                  (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                  uu____4628 in
              let uu____4629 =
                FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c) in
              (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                uu____4629, [])
          | FStar_Parser_AST.PatTvar (x, aq) ->
              let aq1 = trans_aqual env1 aq in
              let uu____4647 = resolvex loc env1 x in
              (match uu____4647 with
               | (loc1, env2, xbv) ->
                   let uu____4679 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_var xbv) in
                   (loc1, env2, (LocalBinder (xbv, aq1)), uu____4679, []))
          | FStar_Parser_AST.PatVar (x, aq) ->
              let aq1 = trans_aqual env1 aq in
              let uu____4697 = resolvex loc env1 x in
              (match uu____4697 with
               | (loc1, env2, xbv) ->
                   let uu____4729 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_var xbv) in
                   (loc1, env2, (LocalBinder (xbv, aq1)), uu____4729, []))
          | FStar_Parser_AST.PatName l ->
              let l1 =
                FStar_Syntax_DsEnv.fail_or env1
                  (FStar_Syntax_DsEnv.try_lookup_datacon env1) l in
              let x =
                let uu____4743 = tun_r p1.FStar_Parser_AST.prange in
                FStar_Syntax_Syntax.new_bv
                  (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                  uu____4743 in
              let uu____4744 =
                FStar_All.pipe_left pos
                  (FStar_Syntax_Syntax.Pat_cons (l1, [])) in
              (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                uu____4744, [])
          | FStar_Parser_AST.PatApp
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                 FStar_Parser_AST.prange = uu____4770;_},
               args)
              ->
              let uu____4776 =
                FStar_List.fold_right
                  (fun arg ->
                     fun uu____4835 ->
                       match uu____4835 with
                       | (loc1, env2, annots, args1) ->
                           let uu____4912 = aux loc1 env2 arg in
                           (match uu____4912 with
                            | (loc2, env3, b, arg1, ans) ->
                                let imp = is_implicit b in
                                (loc2, env3, (FStar_List.append ans annots),
                                  ((arg1, imp) :: args1)))) args
                  (loc, env1, [], []) in
              (match uu____4776 with
               | (loc1, env2, annots, args1) ->
                   let l1 =
                     FStar_Syntax_DsEnv.fail_or env2
                       (FStar_Syntax_DsEnv.try_lookup_datacon env2) l in
                   let x =
                     let uu____5075 = tun_r p1.FStar_Parser_AST.prange in
                     FStar_Syntax_Syntax.new_bv
                       (FStar_Pervasives_Native.Some
                          (p1.FStar_Parser_AST.prange)) uu____5075 in
                   let uu____5076 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_cons (l1, args1)) in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None)),
                     uu____5076, annots))
          | FStar_Parser_AST.PatApp uu____5091 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                p1.FStar_Parser_AST.prange
          | FStar_Parser_AST.PatList pats ->
              let uu____5117 =
                FStar_List.fold_right
                  (fun pat ->
                     fun uu____5167 ->
                       match uu____5167 with
                       | (loc1, env2, annots, pats1) ->
                           let uu____5228 = aux loc1 env2 pat in
                           (match uu____5228 with
                            | (loc2, env3, uu____5267, pat1, ans) ->
                                (loc2, env3, (FStar_List.append ans annots),
                                  (pat1 :: pats1)))) pats (loc, env1, [], []) in
              (match uu____5117 with
               | (loc1, env2, annots, pats1) ->
                   let pat =
                     let uu____5361 =
                       let uu____5364 =
                         let uu____5371 =
                           FStar_Range.end_range p1.FStar_Parser_AST.prange in
                         pos_r uu____5371 in
                       let uu____5372 =
                         let uu____5373 =
                           let uu____5386 =
                             FStar_Syntax_Syntax.lid_as_fv
                               FStar_Parser_Const.nil_lid
                               FStar_Syntax_Syntax.delta_constant
                               (FStar_Pervasives_Native.Some
                                  FStar_Syntax_Syntax.Data_ctor) in
                           (uu____5386, []) in
                         FStar_Syntax_Syntax.Pat_cons uu____5373 in
                       FStar_All.pipe_left uu____5364 uu____5372 in
                     FStar_List.fold_right
                       (fun hd ->
                          fun tl ->
                            let r =
                              FStar_Range.union_ranges
                                hd.FStar_Syntax_Syntax.p
                                tl.FStar_Syntax_Syntax.p in
                            let uu____5418 =
                              let uu____5419 =
                                let uu____5432 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.cons_lid
                                    FStar_Syntax_Syntax.delta_constant
                                    (FStar_Pervasives_Native.Some
                                       FStar_Syntax_Syntax.Data_ctor) in
                                (uu____5432, [(hd, false); (tl, false)]) in
                              FStar_Syntax_Syntax.Pat_cons uu____5419 in
                            FStar_All.pipe_left (pos_r r) uu____5418) pats1
                       uu____5361 in
                   let x =
                     let uu____5466 = tun_r p1.FStar_Parser_AST.prange in
                     FStar_Syntax_Syntax.new_bv
                       (FStar_Pervasives_Native.Some
                          (p1.FStar_Parser_AST.prange)) uu____5466 in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None)), pat,
                     annots))
          | FStar_Parser_AST.PatTuple (args, dep) ->
              let uu____5479 =
                FStar_List.fold_left
                  (fun uu____5536 ->
                     fun p2 ->
                       match uu____5536 with
                       | (loc1, env2, annots, pats) ->
                           let uu____5614 = aux loc1 env2 p2 in
                           (match uu____5614 with
                            | (loc2, env3, uu____5657, pat, ans) ->
                                (loc2, env3, (FStar_List.append ans annots),
                                  ((pat, false) :: pats))))
                  (loc, env1, [], []) args in
              (match uu____5479 with
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
                     | uu____5806 -> failwith "impossible" in
                   let x =
                     let uu____5808 = tun_r p1.FStar_Parser_AST.prange in
                     FStar_Syntax_Syntax.new_bv
                       (FStar_Pervasives_Native.Some
                          (p1.FStar_Parser_AST.prange)) uu____5808 in
                   let uu____5809 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_cons (l1, args2)) in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None)),
                     uu____5809, annots))
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
                     (fun uu____5883 ->
                        match uu____5883 with
                        | (f, p2) ->
                            let uu____5894 = FStar_Ident.ident_of_lid f in
                            (uu____5894, p2))) in
              let args =
                FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                  (FStar_List.map
                     (fun uu____5914 ->
                        match uu____5914 with
                        | (f, uu____5920) ->
                            let uu____5921 =
                              FStar_All.pipe_right fields1
                                (FStar_List.tryFind
                                   (fun uu____5949 ->
                                      match uu____5949 with
                                      | (g, uu____5955) ->
                                          let uu____5956 =
                                            FStar_Ident.string_of_id f in
                                          let uu____5957 =
                                            FStar_Ident.string_of_id g in
                                          uu____5956 = uu____5957)) in
                            (match uu____5921 with
                             | FStar_Pervasives_Native.None ->
                                 FStar_Parser_AST.mk_pattern
                                   (FStar_Parser_AST.PatWild
                                      FStar_Pervasives_Native.None)
                                   p1.FStar_Parser_AST.prange
                             | FStar_Pervasives_Native.Some (uu____5962, p2)
                                 -> p2))) in
              let app =
                let uu____5969 =
                  let uu____5970 =
                    let uu____5977 =
                      let uu____5978 =
                        let uu____5979 =
                          let uu____5980 =
                            let uu____5981 =
                              FStar_Ident.ns_of_lid
                                record.FStar_Syntax_DsEnv.typename in
                            FStar_List.append uu____5981
                              [record.FStar_Syntax_DsEnv.constrname] in
                          FStar_Ident.lid_of_ids uu____5980 in
                        FStar_Parser_AST.PatName uu____5979 in
                      FStar_Parser_AST.mk_pattern uu____5978
                        p1.FStar_Parser_AST.prange in
                    (uu____5977, args) in
                  FStar_Parser_AST.PatApp uu____5970 in
                FStar_Parser_AST.mk_pattern uu____5969
                  p1.FStar_Parser_AST.prange in
              let uu____5986 = aux loc env1 app in
              (match uu____5986 with
               | (env2, e, b, p2, annots) ->
                   let p3 =
                     match p2.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_cons (fv, args1) ->
                         let uu____6061 =
                           let uu____6062 =
                             let uu____6075 =
                               let uu___1088_6076 = fv in
                               let uu____6077 =
                                 let uu____6080 =
                                   let uu____6081 =
                                     let uu____6088 =
                                       FStar_All.pipe_right
                                         record.FStar_Syntax_DsEnv.fields
                                         (FStar_List.map
                                            FStar_Pervasives_Native.fst) in
                                     ((record.FStar_Syntax_DsEnv.typename),
                                       uu____6088) in
                                   FStar_Syntax_Syntax.Record_ctor uu____6081 in
                                 FStar_Pervasives_Native.Some uu____6080 in
                               {
                                 FStar_Syntax_Syntax.fv_name =
                                   (uu___1088_6076.FStar_Syntax_Syntax.fv_name);
                                 FStar_Syntax_Syntax.fv_delta =
                                   (uu___1088_6076.FStar_Syntax_Syntax.fv_delta);
                                 FStar_Syntax_Syntax.fv_qual = uu____6077
                               } in
                             (uu____6075, args1) in
                           FStar_Syntax_Syntax.Pat_cons uu____6062 in
                         FStar_All.pipe_left pos uu____6061
                     | uu____6113 -> p2 in
                   (env2, e, b, p3, annots))
        and aux loc env1 p1 = aux' false loc env1 p1 in
        let aux_maybe_or env1 p1 =
          let loc = [] in
          match p1.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOr [] -> failwith "impossible"
          | FStar_Parser_AST.PatOr (p2::ps) ->
              let uu____6195 = aux' true loc env1 p2 in
              (match uu____6195 with
               | (loc1, env2, var, p3, ans) ->
                   let uu____6247 =
                     FStar_List.fold_left
                       (fun uu____6295 ->
                          fun p4 ->
                            match uu____6295 with
                            | (loc2, env3, ps1) ->
                                let uu____6360 = aux' true loc2 env3 p4 in
                                (match uu____6360 with
                                 | (loc3, env4, uu____6397, p5, ans1) ->
                                     (loc3, env4, ((p5, ans1) :: ps1))))
                       (loc1, env2, []) ps in
                   (match uu____6247 with
                    | (loc2, env3, ps1) ->
                        let pats = (p3, ans) :: (FStar_List.rev ps1) in
                        (env3, var, pats)))
          | uu____6558 ->
              let uu____6559 = aux' true loc env1 p1 in
              (match uu____6559 with
               | (loc1, env2, var, pat, ans) -> (env2, var, [(pat, ans)])) in
        let uu____6649 = aux_maybe_or env p in
        match uu____6649 with
        | (env1, b, pats) ->
            ((let uu____6704 =
                FStar_List.map FStar_Pervasives_Native.fst pats in
              check_linear_pattern_variables uu____6704
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
            let uu____6776 =
              let uu____6777 =
                let uu____6788 = FStar_Syntax_DsEnv.qualify env x in
                (uu____6788, (ty, tacopt)) in
              LetBinder uu____6777 in
            (env, uu____6776, []) in
          let op_to_ident x =
            let uu____6805 =
              let uu____6810 =
                let uu____6811 = FStar_Ident.string_of_id x in
                let uu____6812 = FStar_Ident.range_of_id x in
                FStar_Parser_AST.compile_op Prims.int_zero uu____6811
                  uu____6812 in
              let uu____6813 = FStar_Ident.range_of_id x in
              (uu____6810, uu____6813) in
            FStar_Ident.mk_ident uu____6805 in
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu____6823 = op_to_ident x in
              let uu____6824 =
                let uu____6825 = FStar_Ident.range_of_id x in
                tun_r uu____6825 in
              mklet uu____6823 uu____6824 FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x, uu____6827) ->
              let uu____6832 =
                let uu____6833 = FStar_Ident.range_of_id x in
                tun_r uu____6833 in
              mklet x uu____6832 FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu____6835;_},
               (t, tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env) in
              let uu____6851 = op_to_ident x in
              let uu____6852 = desugar_term env t in
              mklet uu____6851 uu____6852 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x, uu____6854);
                 FStar_Parser_AST.prange = uu____6855;_},
               (t, tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env) in
              let uu____6875 = desugar_term env t in
              mklet x uu____6875 tacopt1
          | uu____6876 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu____6886 = desugar_data_pat true env p in
           match uu____6886 with
           | (env1, binder, p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu____6915;
                      FStar_Syntax_Syntax.p = uu____6916;_},
                    uu____6917)::[] -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu____6930;
                      FStar_Syntax_Syntax.p = uu____6931;_},
                    uu____6932)::[] -> []
                 | uu____6945 -> p1 in
               (env1, binder, p2))
and (desugar_binding_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern -> (env_t * bnd * annotated_pat Prims.list))
  = fun env -> fun p -> desugar_binding_pat_maybe_top false env p
and (desugar_match_pat_maybe_top :
  Prims.bool ->
    env_t -> FStar_Parser_AST.pattern -> (env_t * annotated_pat Prims.list))
  =
  fun uu____6952 ->
    fun env ->
      fun pat ->
        let uu____6955 = desugar_data_pat false env pat in
        match uu____6955 with | (env1, uu____6971, pat1) -> (env1, pat1)
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
      let uu____6990 = desugar_term_aq env e in
      match uu____6990 with | (t, aq) -> (check_no_aq aq; t)
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
      let uu____7007 = desugar_typ_aq env e in
      match uu____7007 with | (t, aq) -> (check_no_aq aq; t)
and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness * FStar_Const.width) ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun repr ->
      fun uu____7017 ->
        fun range ->
          match uu____7017 with
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
              ((let uu____7027 =
                  let uu____7028 =
                    FStar_Const.within_bounds repr signedness width in
                  Prims.op_Negation uu____7028 in
                if uu____7027
                then
                  let uu____7029 =
                    let uu____7034 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm in
                    (FStar_Errors.Error_OutOfRange, uu____7034) in
                  FStar_Errors.log_issue range uu____7029
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
                  let uu____7039 = FStar_Ident.path_of_text intro_nm in
                  FStar_Ident.lid_of_path uu____7039 range in
                let lid1 =
                  let uu____7043 = FStar_Syntax_DsEnv.try_lookup_lid env lid in
                  match uu____7043 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____7053 =
                               FStar_Ident.path_of_text private_intro_nm in
                             FStar_Ident.lid_of_path uu____7053 range in
                           let private_fv =
                             let uu____7055 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____7055 fv.FStar_Syntax_Syntax.fv_qual in
                           let uu___1255_7056 = intro_term in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___1255_7056.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1255_7056.FStar_Syntax_Syntax.vars)
                           }
                       | uu____7057 ->
                           failwith
                             (Prims.op_Hat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None ->
                      let uu____7060 =
                        let uu____7065 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____7065) in
                      FStar_Errors.raise_error uu____7060 range in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None))) range in
                let uu____7081 =
                  let uu____7082 =
                    let uu____7099 =
                      let uu____7110 =
                        let uu____7119 =
                          FStar_Syntax_Syntax.as_implicit false in
                        (repr1, uu____7119) in
                      [uu____7110] in
                    (lid1, uu____7099) in
                  FStar_Syntax_Syntax.Tm_app uu____7082 in
                FStar_Syntax_Syntax.mk uu____7081 range))
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
          let uu___1271_7236 = e in
          {
            FStar_Syntax_Syntax.n = (uu___1271_7236.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___1271_7236.FStar_Syntax_Syntax.vars)
          } in
        let uu____7239 =
          let uu____7240 = unparen top in uu____7240.FStar_Parser_AST.tm in
        match uu____7239 with
        | FStar_Parser_AST.Wild -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____7245 ->
            let uu____7252 = desugar_formula env top in (uu____7252, noaqs)
        | FStar_Parser_AST.Requires (t, lopt) ->
            let uu____7259 = desugar_formula env t in (uu____7259, noaqs)
        | FStar_Parser_AST.Ensures (t, lopt) ->
            let uu____7266 = desugar_formula env t in (uu____7266, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i, FStar_Pervasives_Native.Some size)) ->
            let uu____7290 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range in
            (uu____7290, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____7292 = mk (FStar_Syntax_Syntax.Tm_constant c) in
            (uu____7292, noaqs)
        | FStar_Parser_AST.Op (id, args) when
            let uu____7299 = FStar_Ident.string_of_id id in
            uu____7299 = "=!=" ->
            let r = FStar_Ident.range_of_id id in
            let e =
              let uu____7302 =
                let uu____7303 =
                  let uu____7310 = FStar_Ident.mk_ident ("==", r) in
                  (uu____7310, args) in
                FStar_Parser_AST.Op uu____7303 in
              FStar_Parser_AST.mk_term uu____7302 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level in
            let uu____7313 =
              let uu____7314 =
                let uu____7315 =
                  let uu____7322 = FStar_Ident.mk_ident ("~", r) in
                  (uu____7322, [e]) in
                FStar_Parser_AST.Op uu____7315 in
              FStar_Parser_AST.mk_term uu____7314 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level in
            desugar_term_aq env uu____7313
        | FStar_Parser_AST.Op (op_star, lhs::rhs::[]) when
            (let uu____7332 = FStar_Ident.string_of_id op_star in
             uu____7332 = "*") &&
              (let uu____7334 = op_as_term env (Prims.of_int (2)) op_star in
               FStar_All.pipe_right uu____7334 FStar_Option.isNone)
            ->
            let rec flatten t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op (id, t1::t2::[]) when
                  (let uu____7356 = FStar_Ident.string_of_id id in
                   uu____7356 = "*") &&
                    (let uu____7358 =
                       op_as_term env (Prims.of_int (2)) op_star in
                     FStar_All.pipe_right uu____7358 FStar_Option.isNone)
                  ->
                  let uu____7363 = flatten t1 in
                  FStar_List.append uu____7363 [t2]
              | uu____7366 -> [t] in
            let terms = flatten lhs in
            let t =
              let uu___1316_7371 = top in
              let uu____7372 =
                let uu____7373 =
                  let uu____7384 =
                    FStar_List.map
                      (fun uu____7395 -> FStar_Util.Inr uu____7395) terms in
                  (uu____7384, rhs) in
                FStar_Parser_AST.Sum uu____7373 in
              {
                FStar_Parser_AST.tm = uu____7372;
                FStar_Parser_AST.range =
                  (uu___1316_7371.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1316_7371.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env t
        | FStar_Parser_AST.Tvar a ->
            let uu____7403 =
              let uu____7404 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a in
              FStar_All.pipe_left setpos uu____7404 in
            (uu____7403, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____7410 =
              let uu____7415 =
                let uu____7416 =
                  let uu____7417 = FStar_Ident.string_of_id u in
                  Prims.op_Hat uu____7417 " in non-universe context" in
                Prims.op_Hat "Unexpected universe variable " uu____7416 in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____7415) in
            FStar_Errors.raise_error uu____7410 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s, args) ->
            let uu____7428 = op_as_term env (FStar_List.length args) s in
            (match uu____7428 with
             | FStar_Pervasives_Native.None ->
                 let uu____7435 =
                   let uu____7440 =
                     let uu____7441 = FStar_Ident.string_of_id s in
                     Prims.op_Hat "Unexpected or unbound operator: "
                       uu____7441 in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____7440) in
                 FStar_Errors.raise_error uu____7435
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > Prims.int_zero
                 then
                   let uu____7451 =
                     let uu____7476 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t ->
                               let uu____7538 = desugar_term_aq env t in
                               match uu____7538 with
                               | (t', s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1))) in
                     FStar_All.pipe_right uu____7476 FStar_List.unzip in
                   (match uu____7451 with
                    | (args1, aqs) ->
                        let uu____7671 =
                          mk (FStar_Syntax_Syntax.Tm_app (op, args1)) in
                        (uu____7671, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n, (a, uu____7687)::[]) when
            let uu____7702 = FStar_Ident.string_of_lid n in
            uu____7702 = "SMTPat" ->
            let uu____7703 =
              let uu___1345_7704 = top in
              let uu____7705 =
                let uu____7706 =
                  let uu____7713 =
                    let uu___1347_7714 = top in
                    let uu____7715 =
                      let uu____7716 = smt_pat_lid top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____7716 in
                    {
                      FStar_Parser_AST.tm = uu____7715;
                      FStar_Parser_AST.range =
                        (uu___1347_7714.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1347_7714.FStar_Parser_AST.level)
                    } in
                  (uu____7713, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____7706 in
              {
                FStar_Parser_AST.tm = uu____7705;
                FStar_Parser_AST.range =
                  (uu___1345_7704.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1345_7704.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____7703
        | FStar_Parser_AST.Construct (n, (a, uu____7719)::[]) when
            let uu____7734 = FStar_Ident.string_of_lid n in
            uu____7734 = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____7736 =
                let uu___1357_7737 = top in
                let uu____7738 =
                  let uu____7739 =
                    let uu____7746 =
                      let uu___1359_7747 = top in
                      let uu____7748 =
                        let uu____7749 =
                          smt_pat_lid top.FStar_Parser_AST.range in
                        FStar_Parser_AST.Var uu____7749 in
                      {
                        FStar_Parser_AST.tm = uu____7748;
                        FStar_Parser_AST.range =
                          (uu___1359_7747.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___1359_7747.FStar_Parser_AST.level)
                      } in
                    (uu____7746, a, FStar_Parser_AST.Nothing) in
                  FStar_Parser_AST.App uu____7739 in
                {
                  FStar_Parser_AST.tm = uu____7738;
                  FStar_Parser_AST.range =
                    (uu___1357_7737.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___1357_7737.FStar_Parser_AST.level)
                } in
              desugar_term_maybe_top top_level env uu____7736))
        | FStar_Parser_AST.Construct (n, (a, uu____7752)::[]) when
            let uu____7767 = FStar_Ident.string_of_lid n in
            uu____7767 = "SMTPatOr" ->
            let uu____7768 =
              let uu___1368_7769 = top in
              let uu____7770 =
                let uu____7771 =
                  let uu____7778 =
                    let uu___1370_7779 = top in
                    let uu____7780 =
                      let uu____7781 =
                        smt_pat_or_lid top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____7781 in
                    {
                      FStar_Parser_AST.tm = uu____7780;
                      FStar_Parser_AST.range =
                        (uu___1370_7779.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1370_7779.FStar_Parser_AST.level)
                    } in
                  (uu____7778, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____7771 in
              {
                FStar_Parser_AST.tm = uu____7770;
                FStar_Parser_AST.range =
                  (uu___1368_7769.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1368_7769.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____7768
        | FStar_Parser_AST.Name lid when
            let uu____7783 = FStar_Ident.string_of_lid lid in
            uu____7783 = "Type0" ->
            let uu____7784 =
              mk (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero) in
            (uu____7784, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____7786 = FStar_Ident.string_of_lid lid in
            uu____7786 = "Type" ->
            let uu____7787 =
              mk (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown) in
            (uu____7787, noaqs)
        | FStar_Parser_AST.Construct (lid, (t, FStar_Parser_AST.UnivApp)::[])
            when
            let uu____7804 = FStar_Ident.string_of_lid lid in
            uu____7804 = "Type" ->
            let uu____7805 =
              let uu____7806 =
                let uu____7807 = desugar_universe t in
                FStar_Syntax_Syntax.Tm_type uu____7807 in
              mk uu____7806 in
            (uu____7805, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____7809 = FStar_Ident.string_of_lid lid in
            uu____7809 = "Effect" ->
            let uu____7810 =
              mk (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect) in
            (uu____7810, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____7812 = FStar_Ident.string_of_lid lid in
            uu____7812 = "True" ->
            let uu____7813 =
              let uu____7814 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range in
              FStar_Syntax_Syntax.fvar uu____7814
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None in
            (uu____7813, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____7816 = FStar_Ident.string_of_lid lid in
            uu____7816 = "False" ->
            let uu____7817 =
              let uu____7818 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range in
              FStar_Syntax_Syntax.fvar uu____7818
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None in
            (uu____7817, noaqs)
        | FStar_Parser_AST.Projector (eff_name, id) when
            (let uu____7823 = FStar_Ident.string_of_id id in
             is_special_effect_combinator uu____7823) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            let txt = FStar_Ident.string_of_id id in
            let uu____7825 =
              FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name in
            (match uu____7825 with
             | FStar_Pervasives_Native.Some ed ->
                 let lid = FStar_Syntax_Util.dm4f_lid ed txt in
                 let uu____7834 =
                   FStar_Syntax_Syntax.fvar lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None in
                 (uu____7834, noaqs)
             | FStar_Pervasives_Native.None ->
                 let uu____7835 =
                   let uu____7836 = FStar_Ident.string_of_lid eff_name in
                   FStar_Util.format2
                     "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                     uu____7836 txt in
                 failwith uu____7835)
        | FStar_Parser_AST.Var l ->
            let uu____7842 = desugar_name mk setpos env true l in
            (uu____7842, noaqs)
        | FStar_Parser_AST.Name l ->
            let uu____7849 = desugar_name mk setpos env true l in
            (uu____7849, noaqs)
        | FStar_Parser_AST.Projector (l, i) ->
            let name =
              let uu____7864 = FStar_Syntax_DsEnv.try_lookup_datacon env l in
              match uu____7864 with
              | FStar_Pervasives_Native.Some uu____7873 ->
                  FStar_Pervasives_Native.Some (true, l)
              | FStar_Pervasives_Native.None ->
                  let uu____7878 =
                    FStar_Syntax_DsEnv.try_lookup_root_effect_name env l in
                  (match uu____7878 with
                   | FStar_Pervasives_Native.Some new_name ->
                       FStar_Pervasives_Native.Some (false, new_name)
                   | uu____7892 -> FStar_Pervasives_Native.None) in
            (match name with
             | FStar_Pervasives_Native.Some (resolve, new_name) ->
                 let uu____7909 =
                   let uu____7910 =
                     FStar_Syntax_Util.mk_field_projector_name_from_ident
                       new_name i in
                   desugar_name mk setpos env resolve uu____7910 in
                 (uu____7909, noaqs)
             | uu____7916 ->
                 let uu____7923 =
                   let uu____7928 =
                     let uu____7929 = FStar_Ident.string_of_lid l in
                     FStar_Util.format1
                       "Data constructor or effect %s not found" uu____7929 in
                   (FStar_Errors.Fatal_EffectNotFound, uu____7928) in
                 FStar_Errors.raise_error uu____7923
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Discrim lid ->
            let uu____7935 = FStar_Syntax_DsEnv.try_lookup_datacon env lid in
            (match uu____7935 with
             | FStar_Pervasives_Native.None ->
                 let uu____7942 =
                   let uu____7947 =
                     let uu____7948 = FStar_Ident.string_of_lid lid in
                     FStar_Util.format1 "Data constructor %s not found"
                       uu____7948 in
                   (FStar_Errors.Fatal_DataContructorNotFound, uu____7947) in
                 FStar_Errors.raise_error uu____7942
                   top.FStar_Parser_AST.range
             | uu____7953 ->
                 let lid' = FStar_Syntax_Util.mk_discriminator lid in
                 let uu____7957 = desugar_name mk setpos env true lid' in
                 (uu____7957, noaqs))
        | FStar_Parser_AST.Construct (l, args) ->
            let uu____7977 = FStar_Syntax_DsEnv.try_lookup_datacon env l in
            (match uu____7977 with
             | FStar_Pervasives_Native.Some head ->
                 let head1 = mk (FStar_Syntax_Syntax.Tm_fvar head) in
                 (match args with
                  | [] -> (head1, noaqs)
                  | uu____7996 ->
                      let uu____8003 =
                        FStar_Util.take
                          (fun uu____8027 ->
                             match uu____8027 with
                             | (uu____8032, imp) ->
                                 imp = FStar_Parser_AST.UnivApp) args in
                      (match uu____8003 with
                       | (universes, args1) ->
                           let universes1 =
                             FStar_List.map
                               (fun x ->
                                  desugar_universe
                                    (FStar_Pervasives_Native.fst x))
                               universes in
                           let uu____8077 =
                             let uu____8102 =
                               FStar_List.map
                                 (fun uu____8145 ->
                                    match uu____8145 with
                                    | (t, imp) ->
                                        let uu____8162 =
                                          desugar_term_aq env t in
                                        (match uu____8162 with
                                         | (te, aq) ->
                                             ((arg_withimp_e imp te), aq)))
                                 args1 in
                             FStar_All.pipe_right uu____8102 FStar_List.unzip in
                           (match uu____8077 with
                            | (args2, aqs) ->
                                let head2 =
                                  if universes1 = []
                                  then head1
                                  else
                                    mk
                                      (FStar_Syntax_Syntax.Tm_uinst
                                         (head1, universes1)) in
                                let uu____8303 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_app
                                       (head2, args2)) in
                                (uu____8303, (join_aqs aqs)))))
             | FStar_Pervasives_Native.None ->
                 let err =
                   let uu____8321 =
                     FStar_Syntax_DsEnv.try_lookup_effect_name env l in
                   match uu____8321 with
                   | FStar_Pervasives_Native.None ->
                       let uu____8328 =
                         let uu____8329 =
                           let uu____8330 = FStar_Ident.string_of_lid l in
                           Prims.op_Hat uu____8330 " not found" in
                         Prims.op_Hat "Constructor " uu____8329 in
                       (FStar_Errors.Fatal_ConstructorNotFound, uu____8328)
                   | FStar_Pervasives_Native.Some uu____8331 ->
                       let uu____8332 =
                         let uu____8333 =
                           let uu____8334 = FStar_Ident.string_of_lid l in
                           Prims.op_Hat uu____8334
                             " used at an unexpected position" in
                         Prims.op_Hat "Effect " uu____8333 in
                       (FStar_Errors.Fatal_UnexpectedEffect, uu____8332) in
                 FStar_Errors.raise_error err top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Sum (binders, t) when
            FStar_Util.for_all
              (fun uu___8_8359 ->
                 match uu___8_8359 with
                 | FStar_Util.Inr uu____8364 -> true
                 | uu____8365 -> false) binders
            ->
            let terms =
              let uu____8373 =
                FStar_All.pipe_right binders
                  (FStar_List.map
                     (fun uu___9_8390 ->
                        match uu___9_8390 with
                        | FStar_Util.Inr x -> x
                        | FStar_Util.Inl uu____8396 -> failwith "Impossible")) in
              FStar_List.append uu____8373 [t] in
            let uu____8397 =
              let uu____8422 =
                FStar_All.pipe_right terms
                  (FStar_List.map
                     (fun t1 ->
                        let uu____8479 = desugar_typ_aq env t1 in
                        match uu____8479 with
                        | (t', aq) ->
                            let uu____8490 = FStar_Syntax_Syntax.as_arg t' in
                            (uu____8490, aq))) in
              FStar_All.pipe_right uu____8422 FStar_List.unzip in
            (match uu____8397 with
             | (targs, aqs) ->
                 let tup =
                   let uu____8600 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____8600 in
                 let uu____8609 =
                   mk (FStar_Syntax_Syntax.Tm_app (tup, targs)) in
                 (uu____8609, (join_aqs aqs)))
        | FStar_Parser_AST.Sum (binders, t) ->
            let uu____8636 =
              let uu____8653 =
                let uu____8660 =
                  let uu____8667 =
                    FStar_All.pipe_left
                      (fun uu____8676 -> FStar_Util.Inl uu____8676)
                      (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                         FStar_Pervasives_Native.None) in
                  [uu____8667] in
                FStar_List.append binders uu____8660 in
              FStar_List.fold_left
                (fun uu____8721 ->
                   fun b ->
                     match uu____8721 with
                     | (env1, tparams, typs) ->
                         let uu____8782 =
                           match b with
                           | FStar_Util.Inl b1 -> desugar_binder env1 b1
                           | FStar_Util.Inr t1 ->
                               let uu____8797 = desugar_typ env1 t1 in
                               (FStar_Pervasives_Native.None, uu____8797) in
                         (match uu____8782 with
                          | (xopt, t1) ->
                              let uu____8822 =
                                match xopt with
                                | FStar_Pervasives_Native.None ->
                                    let uu____8831 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        (setpos FStar_Syntax_Syntax.tun) in
                                    (env1, uu____8831)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x in
                              (match uu____8822 with
                               | (env2, x) ->
                                   let uu____8851 =
                                     let uu____8854 =
                                       let uu____8857 =
                                         let uu____8858 =
                                           no_annot_abs tparams t1 in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____8858 in
                                       [uu____8857] in
                                     FStar_List.append typs uu____8854 in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___1499_8884 = x in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___1499_8884.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___1499_8884.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____8851)))) (env, [], []) uu____8653 in
            (match uu____8636 with
             | (env1, uu____8912, targs) ->
                 let tup =
                   let uu____8935 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____8935 in
                 let uu____8936 =
                   FStar_All.pipe_left mk
                     (FStar_Syntax_Syntax.Tm_app (tup, targs)) in
                 (uu____8936, noaqs))
        | FStar_Parser_AST.Product (binders, t) ->
            let uu____8955 = uncurry binders t in
            (match uu____8955 with
             | (bs, t1) ->
                 let rec aux env1 bs1 uu___10_8999 =
                   match uu___10_8999 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range true env1 t1 in
                       let uu____9015 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod in
                       FStar_All.pipe_left setpos uu____9015
                   | hd::tl ->
                       let bb = desugar_binder env1 hd in
                       let uu____9039 =
                         as_binder env1 hd.FStar_Parser_AST.aqual bb in
                       (match uu____9039 with
                        | (b, env2) -> aux env2 (b :: bs1) tl) in
                 let uu____9072 = aux env [] bs in (uu____9072, noaqs))
        | FStar_Parser_AST.Refine (b, f) ->
            let uu____9081 = desugar_binder env b in
            (match uu____9081 with
             | (FStar_Pervasives_Native.None, uu____9092) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____9106 =
                   as_binder env FStar_Pervasives_Native.None b1 in
                 (match uu____9106 with
                  | ((x, uu____9122), env1) ->
                      let f1 = desugar_formula env1 f in
                      let uu____9135 =
                        let uu____9136 = FStar_Syntax_Util.refine x f1 in
                        FStar_All.pipe_left setpos uu____9136 in
                      (uu____9135, noaqs)))
        | FStar_Parser_AST.Abs (binders, body) ->
            let bvss = FStar_List.map gather_pattern_bound_vars binders in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set::sets2 ->
                    let i = FStar_Util.set_intersect acc set in
                    let uu____9214 = FStar_Util.set_is_empty i in
                    if uu____9214
                    then
                      let uu____9217 = FStar_Util.set_union acc set in
                      aux uu____9217 sets2
                    else
                      (let uu____9221 =
                         let uu____9222 = FStar_Util.set_elements i in
                         FStar_List.hd uu____9222 in
                       FStar_Pervasives_Native.Some uu____9221) in
              let uu____9225 = FStar_Syntax_Syntax.new_id_set () in
              aux uu____9225 sets in
            ((let uu____9229 = check_disjoint bvss in
              match uu____9229 with
              | FStar_Pervasives_Native.None -> ()
              | FStar_Pervasives_Native.Some id ->
                  let uu____9233 =
                    let uu____9238 =
                      let uu____9239 = FStar_Ident.string_of_id id in
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        uu____9239 in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____9238) in
                  let uu____9240 = FStar_Ident.range_of_id id in
                  FStar_Errors.raise_error uu____9233 uu____9240);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern) in
              let uu____9248 =
                FStar_List.fold_left
                  (fun uu____9268 ->
                     fun pat ->
                       match uu____9268 with
                       | (env1, ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____9294,
                                 (t, FStar_Pervasives_Native.None))
                                ->
                                let uu____9304 =
                                  let uu____9307 = free_type_vars env1 t in
                                  FStar_List.append uu____9307 ftvs in
                                (env1, uu____9304)
                            | FStar_Parser_AST.PatAscribed
                                (uu____9312,
                                 (t, FStar_Pervasives_Native.Some tac))
                                ->
                                let uu____9323 =
                                  let uu____9326 = free_type_vars env1 t in
                                  let uu____9329 =
                                    let uu____9332 = free_type_vars env1 tac in
                                    FStar_List.append uu____9332 ftvs in
                                  FStar_List.append uu____9326 uu____9329 in
                                (env1, uu____9323)
                            | uu____9337 -> (env1, ftvs))) (env, []) binders1 in
              match uu____9248 with
              | (uu____9346, ftv) ->
                  let ftv1 = sort_ftv ftv in
                  let binders2 =
                    let uu____9358 =
                      FStar_All.pipe_right ftv1
                        (FStar_List.map
                           (fun a ->
                              FStar_Parser_AST.mk_pattern
                                (FStar_Parser_AST.PatTvar
                                   (a,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Parser_AST.Implicit)))
                                top.FStar_Parser_AST.range)) in
                    FStar_List.append uu____9358 binders1 in
                  let rec aux env1 bs sc_pat_opt pats =
                    match pats with
                    | [] ->
                        let uu____9438 = desugar_term_aq env1 body in
                        (match uu____9438 with
                         | (body1, aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc, pat) ->
                                   let body2 =
                                     let uu____9473 =
                                       let uu____9474 =
                                         FStar_Syntax_Syntax.pat_bvs pat in
                                       FStar_All.pipe_right uu____9474
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder) in
                                     FStar_Syntax_Subst.close uu____9473
                                       body1 in
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_match
                                        (sc,
                                          [(pat,
                                             FStar_Pervasives_Native.None,
                                             body2)]))
                                     body2.FStar_Syntax_Syntax.pos
                               | FStar_Pervasives_Native.None -> body1 in
                             let uu____9543 =
                               let uu____9544 =
                                 no_annot_abs (FStar_List.rev bs) body2 in
                               setpos uu____9544 in
                             (uu____9543, aq))
                    | p::rest ->
                        let uu____9557 = desugar_binding_pat env1 p in
                        (match uu____9557 with
                         | (env2, b, pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1, uu____9589)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____9604 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange in
                             let uu____9611 =
                               match b with
                               | LetBinder uu____9652 ->
                                   failwith "Impossible"
                               | LocalBinder (x, aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None,
                                        uu____9720) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some p1,
                                        FStar_Pervasives_Native.None) ->
                                         let uu____9774 =
                                           let uu____9783 =
                                             FStar_Syntax_Syntax.bv_to_name x in
                                           (uu____9783, p1) in
                                         FStar_Pervasives_Native.Some
                                           uu____9774
                                     | (FStar_Pervasives_Native.Some p1,
                                        FStar_Pervasives_Native.Some
                                        (sc, p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____9845, uu____9846) ->
                                              let tup2 =
                                                let uu____9848 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.of_int (2))
                                                    top.FStar_Parser_AST.range in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____9848
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor) in
                                              let sc1 =
                                                let uu____9852 =
                                                  let uu____9853 =
                                                    let uu____9870 =
                                                      mk
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tup2) in
                                                    let uu____9873 =
                                                      let uu____9884 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          sc in
                                                      let uu____9893 =
                                                        let uu____9904 =
                                                          let uu____9913 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____9913 in
                                                        [uu____9904] in
                                                      uu____9884 ::
                                                        uu____9893 in
                                                    (uu____9870, uu____9873) in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____9853 in
                                                FStar_Syntax_Syntax.mk
                                                  uu____9852
                                                  top.FStar_Parser_AST.range in
                                              let p2 =
                                                let uu____9961 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____9961 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____10004, args),
                                             FStar_Syntax_Syntax.Pat_cons
                                             (uu____10006, pats1)) ->
                                              let tupn =
                                                let uu____10049 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.int_one +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10049
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor) in
                                              let sc1 =
                                                let uu____10061 =
                                                  let uu____10062 =
                                                    let uu____10079 =
                                                      mk
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn) in
                                                    let uu____10082 =
                                                      let uu____10093 =
                                                        let uu____10104 =
                                                          let uu____10113 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____10113 in
                                                        [uu____10104] in
                                                      FStar_List.append args
                                                        uu____10093 in
                                                    (uu____10079,
                                                      uu____10082) in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____10062 in
                                                mk uu____10061 in
                                              let p2 =
                                                let uu____10161 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats1 [(p1, false)])))
                                                  uu____10161 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____10202 ->
                                              failwith "Impossible") in
                                   ((x, aq), sc_pat_opt1) in
                             (match uu____9611 with
                              | (b1, sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest)) in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____10293, uu____10294, FStar_Parser_AST.UnivApp) ->
            let rec aux universes e =
              let uu____10316 =
                let uu____10317 = unparen e in
                uu____10317.FStar_Parser_AST.tm in
              match uu____10316 with
              | FStar_Parser_AST.App (e1, t, FStar_Parser_AST.UnivApp) ->
                  let univ_arg = desugar_universe t in
                  aux (univ_arg :: universes) e1
              | uu____10327 ->
                  let uu____10328 = desugar_term_aq env e in
                  (match uu____10328 with
                   | (head, aq) ->
                       let uu____10341 =
                         mk (FStar_Syntax_Syntax.Tm_uinst (head, universes)) in
                       (uu____10341, aq)) in
            aux [] top
        | FStar_Parser_AST.App uu____10348 ->
            let rec aux args aqs e =
              let uu____10425 =
                let uu____10426 = unparen e in
                uu____10426.FStar_Parser_AST.tm in
              match uu____10425 with
              | FStar_Parser_AST.App (e1, t, imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____10444 = desugar_term_aq env t in
                  (match uu____10444 with
                   | (t1, aq) ->
                       let arg = arg_withimp_e imp t1 in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____10492 ->
                  let uu____10493 = desugar_term_aq env e in
                  (match uu____10493 with
                   | (head, aq) ->
                       let uu____10514 =
                         mk (FStar_Syntax_Syntax.Tm_app (head, args)) in
                       (uu____10514, (join_aqs (aq :: aqs)))) in
            aux [] [] top
        | FStar_Parser_AST.Bind (x, t1, t2) ->
            let xpat =
              let uu____10567 = FStar_Ident.range_of_id x in
              FStar_Parser_AST.mk_pattern
                (FStar_Parser_AST.PatVar (x, FStar_Pervasives_Native.None))
                uu____10567 in
            let k =
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Abs ([xpat], t2))
                t2.FStar_Parser_AST.range t2.FStar_Parser_AST.level in
            let bind_lid =
              let uu____10574 = FStar_Ident.range_of_id x in
              FStar_Ident.lid_of_path ["bind"] uu____10574 in
            let bind =
              let uu____10576 = FStar_Ident.range_of_id x in
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Var bind_lid)
                uu____10576 FStar_Parser_AST.Expr in
            let uu____10577 =
              FStar_Parser_AST.mkExplicitApp bind [t1; k]
                top.FStar_Parser_AST.range in
            desugar_term_aq env uu____10577
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
            let uu____10629 = desugar_term_aq env t in
            (match uu____10629 with
             | (tm, s) ->
                 let uu____10640 =
                   mk
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence))) in
                 (uu____10640, s))
        | FStar_Parser_AST.LetOpen (lid, e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid in
            let uu____10646 =
              let uu____10659 = FStar_Syntax_DsEnv.expect_typ env1 in
              if uu____10659 then desugar_typ_aq else desugar_term_aq in
            uu____10646 env1 e
        | FStar_Parser_AST.Let (qual, lbs, body) ->
            let is_rec = qual = FStar_Parser_AST.Rec in
            let ds_let_rec_or_app uu____10722 =
              let bindings = lbs in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____10865 ->
                        match uu____10865 with
                        | (attr_opt, (p, def)) ->
                            let uu____10923 = is_app_pattern p in
                            if uu____10923
                            then
                              let uu____10954 =
                                destruct_app_pattern env top_level p in
                              (attr_opt, uu____10954, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1, def1) ->
                                   let uu____11036 =
                                     destruct_app_pattern env top_level p1 in
                                   (attr_opt, uu____11036, def1)
                               | uu____11081 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id, uu____11119);
                                           FStar_Parser_AST.prange =
                                             uu____11120;_},
                                         t)
                                        ->
                                        if top_level
                                        then
                                          let uu____11168 =
                                            let uu____11189 =
                                              let uu____11194 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id in
                                              FStar_Util.Inr uu____11194 in
                                            (uu____11189, [],
                                              (FStar_Pervasives_Native.Some t)) in
                                          (attr_opt, uu____11168, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id, uu____11285) ->
                                        if top_level
                                        then
                                          let uu____11320 =
                                            let uu____11341 =
                                              let uu____11346 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id in
                                              FStar_Util.Inr uu____11346 in
                                            (uu____11341, [],
                                              FStar_Pervasives_Native.None) in
                                          (attr_opt, uu____11320, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____11436 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange)))) in
              let uu____11467 =
                FStar_List.fold_left
                  (fun uu____11554 ->
                     fun uu____11555 ->
                       match (uu____11554, uu____11555) with
                       | ((env1, fnames, rec_bindings, used_markers),
                          (_attr_opt, (f, uu____11682, uu____11683),
                           uu____11684)) ->
                           let uu____11815 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____11853 =
                                   FStar_Syntax_DsEnv.push_bv' env1 x in
                                 (match uu____11853 with
                                  | (env2, xx, used_marker) ->
                                      let dummy_ref = FStar_Util.mk_ref true in
                                      let uu____11884 =
                                        let uu____11887 =
                                          FStar_Syntax_Syntax.mk_binder xx in
                                        uu____11887 :: rec_bindings in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____11884, (used_marker ::
                                        used_markers)))
                             | FStar_Util.Inr l ->
                                 let uu____11901 =
                                   let uu____11908 =
                                     FStar_Ident.ident_of_lid l in
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 uu____11908
                                     FStar_Syntax_Syntax.delta_equational in
                                 (match uu____11901 with
                                  | (env2, used_marker) ->
                                      (env2, (FStar_Util.Inr l),
                                        rec_bindings, (used_marker ::
                                        used_markers))) in
                           (match uu____11815 with
                            | (env2, lbname, rec_bindings1, used_markers1) ->
                                (env2, (lbname :: fnames), rec_bindings1,
                                  used_markers1))) (env, [], [], []) funs in
              match uu____11467 with
              | (env', fnames, rec_bindings, used_markers) ->
                  let fnames1 = FStar_List.rev fnames in
                  let rec_bindings1 = FStar_List.rev rec_bindings in
                  let used_markers1 = FStar_List.rev used_markers in
                  let desugar_one_def env1 lbname uu____12139 =
                    match uu____12139 with
                    | (attrs_opt, (uu____12179, args, result_t), def) ->
                        let args1 =
                          FStar_All.pipe_right args
                            (FStar_List.map replace_unit_pattern) in
                        let pos = def.FStar_Parser_AST.range in
                        let def1 =
                          match result_t with
                          | FStar_Pervasives_Native.None -> def
                          | FStar_Pervasives_Native.Some (t, tacopt) ->
                              let t1 =
                                let uu____12271 = is_comp_type env1 t in
                                if uu____12271
                                then
                                  ((let uu____12273 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x ->
                                              let uu____12283 =
                                                is_var_pattern x in
                                              Prims.op_Negation uu____12283)) in
                                    match uu____12273 with
                                    | FStar_Pervasives_Native.None -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____12286 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____12288 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid in
                                         FStar_Option.isSome uu____12288))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             Prims.int_zero)) in
                                   if uu____12286
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t) in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed (def, t1, tacopt))
                                def.FStar_Parser_AST.range
                                FStar_Parser_AST.Expr in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____12295 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level in
                        let uu____12298 = desugar_term_aq env1 def2 in
                        (match uu____12298 with
                         | (body1, aq) ->
                             let lbname1 =
                               match lbname with
                               | FStar_Util.Inl x -> FStar_Util.Inl x
                               | FStar_Util.Inr l ->
                                   let uu____12320 =
                                     let uu____12321 =
                                       FStar_Syntax_Util.incr_delta_qualifier
                                         body1 in
                                     FStar_Syntax_Syntax.lid_as_fv l
                                       uu____12321
                                       FStar_Pervasives_Native.None in
                                   FStar_Util.Inr uu____12320 in
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
                  let uu____12360 =
                    let uu____12377 =
                      FStar_List.map2
                        (desugar_one_def (if is_rec then env' else env))
                        fnames1 funs in
                    FStar_All.pipe_right uu____12377 FStar_List.unzip in
                  (match uu____12360 with
                   | (lbs1, aqss) ->
                       let uu____12517 = desugar_term_aq env' body in
                       (match uu____12517 with
                        | (body1, aq) ->
                            (if is_rec
                             then
                               FStar_List.iter2
                                 (fun uu____12594 ->
                                    fun used_marker ->
                                      match uu____12594 with
                                      | (_attr_opt,
                                         (f, uu____12640, uu____12641),
                                         uu____12642) ->
                                          let uu____12699 =
                                            let uu____12700 =
                                              FStar_ST.op_Bang used_marker in
                                            Prims.op_Negation uu____12700 in
                                          if uu____12699
                                          then
                                            let uu____12707 =
                                              match f with
                                              | FStar_Util.Inl x ->
                                                  let uu____12721 =
                                                    FStar_Ident.string_of_id
                                                      x in
                                                  let uu____12722 =
                                                    FStar_Ident.range_of_id x in
                                                  (uu____12721, "Local",
                                                    uu____12722)
                                              | FStar_Util.Inr l ->
                                                  let uu____12724 =
                                                    FStar_Ident.string_of_lid
                                                      l in
                                                  let uu____12725 =
                                                    FStar_Ident.range_of_lid
                                                      l in
                                                  (uu____12724, "Global",
                                                    uu____12725) in
                                            (match uu____12707 with
                                             | (nm, gl, rng) ->
                                                 let uu____12729 =
                                                   let uu____12734 =
                                                     FStar_Util.format2
                                                       "%s binding %s is recursive but not used in its body"
                                                       gl nm in
                                                   (FStar_Errors.Warning_UnusedLetRec,
                                                     uu____12734) in
                                                 FStar_Errors.log_issue rng
                                                   uu____12729)
                                          else ()) funs used_markers1
                             else ();
                             (let uu____12737 =
                                let uu____12740 =
                                  let uu____12741 =
                                    let uu____12754 =
                                      FStar_Syntax_Subst.close rec_bindings1
                                        body1 in
                                    ((is_rec, lbs1), uu____12754) in
                                  FStar_Syntax_Syntax.Tm_let uu____12741 in
                                FStar_All.pipe_left mk uu____12740 in
                              (uu____12737,
                                (FStar_List.append aq
                                   (FStar_List.flatten aqss))))))) in
            let ds_non_rec attrs_opt pat t1 t2 =
              let attrs =
                match attrs_opt with
                | FStar_Pervasives_Native.None -> []
                | FStar_Pervasives_Native.Some l ->
                    FStar_List.map (desugar_term env) l in
              let uu____12854 = desugar_term_aq env t1 in
              match uu____12854 with
              | (t11, aq0) ->
                  let uu____12875 =
                    desugar_binding_pat_maybe_top top_level env pat in
                  (match uu____12875 with
                   | (env1, binder, pat1) ->
                       let uu____12905 =
                         match binder with
                         | LetBinder (l, (t, _tacopt)) ->
                             let uu____12947 = desugar_term_aq env1 t2 in
                             (match uu____12947 with
                              | (body1, aq) ->
                                  let fv =
                                    let uu____12969 =
                                      FStar_Syntax_Util.incr_delta_qualifier
                                        t11 in
                                    FStar_Syntax_Syntax.lid_as_fv l
                                      uu____12969
                                      FStar_Pervasives_Native.None in
                                  let uu____12970 =
                                    FStar_All.pipe_left mk
                                      (FStar_Syntax_Syntax.Tm_let
                                         ((false,
                                            [mk_lb
                                               (attrs, (FStar_Util.Inr fv),
                                                 t, t11,
                                                 (t11.FStar_Syntax_Syntax.pos))]),
                                           body1)) in
                                  (uu____12970, aq))
                         | LocalBinder (x, uu____13008) ->
                             let uu____13009 = desugar_term_aq env1 t2 in
                             (match uu____13009 with
                              | (body1, aq) ->
                                  let body2 =
                                    match pat1 with
                                    | [] -> body1
                                    | ({
                                         FStar_Syntax_Syntax.v =
                                           FStar_Syntax_Syntax.Pat_wild
                                           uu____13031;
                                         FStar_Syntax_Syntax.p = uu____13032;_},
                                       uu____13033)::[] -> body1
                                    | uu____13046 ->
                                        let uu____13049 =
                                          let uu____13050 =
                                            let uu____13073 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x in
                                            let uu____13076 =
                                              desugar_disjunctive_pattern
                                                pat1
                                                FStar_Pervasives_Native.None
                                                body1 in
                                            (uu____13073, uu____13076) in
                                          FStar_Syntax_Syntax.Tm_match
                                            uu____13050 in
                                        FStar_Syntax_Syntax.mk uu____13049
                                          top.FStar_Parser_AST.range in
                                  let uu____13113 =
                                    let uu____13116 =
                                      let uu____13117 =
                                        let uu____13130 =
                                          let uu____13133 =
                                            let uu____13134 =
                                              FStar_Syntax_Syntax.mk_binder x in
                                            [uu____13134] in
                                          FStar_Syntax_Subst.close
                                            uu____13133 body2 in
                                        ((false,
                                           [mk_lb
                                              (attrs, (FStar_Util.Inl x),
                                                (x.FStar_Syntax_Syntax.sort),
                                                t11,
                                                (t11.FStar_Syntax_Syntax.pos))]),
                                          uu____13130) in
                                      FStar_Syntax_Syntax.Tm_let uu____13117 in
                                    FStar_All.pipe_left mk uu____13116 in
                                  (uu____13113, aq)) in
                       (match uu____12905 with
                        | (tm, aq1) -> (tm, (FStar_List.append aq0 aq1)))) in
            let uu____13239 = FStar_List.hd lbs in
            (match uu____13239 with
             | (attrs, (head_pat, defn)) ->
                 let uu____13283 = is_rec || (is_app_pattern head_pat) in
                 if uu____13283
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1, t2, t3) ->
            let x =
              let uu____13293 = tun_r t3.FStar_Parser_AST.range in
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                uu____13293 in
            let t_bool =
              let uu____13297 =
                let uu____13298 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None in
                FStar_Syntax_Syntax.Tm_fvar uu____13298 in
              mk uu____13297 in
            let uu____13299 = desugar_term_aq env t1 in
            (match uu____13299 with
             | (t1', aq1) ->
                 let t1'1 =
                   FStar_Syntax_Util.ascribe t1'
                     ((FStar_Util.Inl t_bool), FStar_Pervasives_Native.None) in
                 let uu____13331 = desugar_term_aq env t2 in
                 (match uu____13331 with
                  | (t2', aq2) ->
                      let uu____13342 = desugar_term_aq env t3 in
                      (match uu____13342 with
                       | (t3', aq3) ->
                           let uu____13353 =
                             let uu____13354 =
                               let uu____13355 =
                                 let uu____13378 =
                                   let uu____13395 =
                                     let uu____13410 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t1.FStar_Parser_AST.range in
                                     (uu____13410,
                                       FStar_Pervasives_Native.None, t2') in
                                   let uu____13423 =
                                     let uu____13440 =
                                       let uu____13455 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t1.FStar_Parser_AST.range in
                                       (uu____13455,
                                         FStar_Pervasives_Native.None, t3') in
                                     [uu____13440] in
                                   uu____13395 :: uu____13423 in
                                 (t1'1, uu____13378) in
                               FStar_Syntax_Syntax.Tm_match uu____13355 in
                             mk uu____13354 in
                           (uu____13353, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____13648 =
              match uu____13648 with
              | (pat, wopt, b) ->
                  let uu____13670 = desugar_match_pat env pat in
                  (match uu____13670 with
                   | (env1, pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____13701 = desugar_term env1 e1 in
                             FStar_Pervasives_Native.Some uu____13701 in
                       let uu____13706 = desugar_term_aq env1 b in
                       (match uu____13706 with
                        | (b1, aq) ->
                            let uu____13719 =
                              desugar_disjunctive_pattern pat1 wopt1 b1 in
                            (uu____13719, aq))) in
            let uu____13724 = desugar_term_aq env e in
            (match uu____13724 with
             | (e1, aq) ->
                 let uu____13735 =
                   let uu____13766 =
                     let uu____13799 = FStar_List.map desugar_branch branches in
                     FStar_All.pipe_right uu____13799 FStar_List.unzip in
                   FStar_All.pipe_right uu____13766
                     (fun uu____14017 ->
                        match uu____14017 with
                        | (x, y) -> ((FStar_List.flatten x), y)) in
                 (match uu____13735 with
                  | (brs, aqs) ->
                      let uu____14236 =
                        FStar_All.pipe_left mk
                          (FStar_Syntax_Syntax.Tm_match (e1, brs)) in
                      (uu____14236, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e, t, tac_opt) ->
            let uu____14270 =
              let uu____14291 = is_comp_type env t in
              if uu____14291
              then
                let comp = desugar_comp t.FStar_Parser_AST.range true env t in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____14342 = desugar_term_aq env t in
                 match uu____14342 with
                 | (tm, aq) -> ((FStar_Util.Inl tm), aq)) in
            (match uu____14270 with
             | (annot, aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env) in
                 let uu____14434 = desugar_term_aq env e in
                 (match uu____14434 with
                  | (e1, aq) ->
                      let uu____14445 =
                        FStar_All.pipe_left mk
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None)) in
                      (uu____14445, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____14484, []) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt, fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range in
            let user_ns =
              let uu____14525 = FStar_List.hd fields in
              match uu____14525 with
              | (f, uu____14537) -> FStar_Ident.ns_of_lid f in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____14585 ->
                        match uu____14585 with
                        | (g, uu____14591) ->
                            let uu____14592 = FStar_Ident.string_of_id f in
                            let uu____14593 =
                              let uu____14594 = FStar_Ident.ident_of_lid g in
                              FStar_Ident.string_of_id uu____14594 in
                            uu____14592 = uu____14593)) in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f]) in
              match found with
              | FStar_Pervasives_Native.Some (uu____14600, e) -> (fn, e)
              | FStar_Pervasives_Native.None ->
                  (match xopt with
                   | FStar_Pervasives_Native.None ->
                       let uu____14614 =
                         let uu____14619 =
                           let uu____14620 = FStar_Ident.string_of_id f in
                           let uu____14621 =
                             FStar_Ident.string_of_lid
                               record.FStar_Syntax_DsEnv.typename in
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             uu____14620 uu____14621 in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____14619) in
                       FStar_Errors.raise_error uu____14614
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
                  let uu____14629 =
                    let uu____14640 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____14671 ->
                              match uu____14671 with
                              | (f, uu____14681) ->
                                  let uu____14682 =
                                    let uu____14683 =
                                      get_field FStar_Pervasives_Native.None
                                        f in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____14683 in
                                  (uu____14682, FStar_Parser_AST.Nothing))) in
                    (user_constrname, uu____14640) in
                  FStar_Parser_AST.Construct uu____14629
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range in
                  let xterm =
                    let uu____14701 =
                      let uu____14702 = FStar_Ident.lid_of_ids [x] in
                      FStar_Parser_AST.Var uu____14702 in
                    let uu____14703 = FStar_Ident.range_of_id x in
                    FStar_Parser_AST.mk_term uu____14701 uu____14703
                      FStar_Parser_AST.Expr in
                  let record1 =
                    let uu____14705 =
                      let uu____14718 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____14748 ->
                                match uu____14748 with
                                | (f, uu____14758) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f)) in
                      (FStar_Pervasives_Native.None, uu____14718) in
                    FStar_Parser_AST.Record uu____14705 in
                  let uu____14767 =
                    let uu____14788 =
                      let uu____14803 =
                        let uu____14816 =
                          let uu____14821 =
                            let uu____14822 = FStar_Ident.range_of_id x in
                            FStar_Parser_AST.mk_pattern
                              (FStar_Parser_AST.PatVar
                                 (x, FStar_Pervasives_Native.None))
                              uu____14822 in
                          (uu____14821, e) in
                        (FStar_Pervasives_Native.None, uu____14816) in
                      [uu____14803] in
                    (FStar_Parser_AST.NoLetQualifier, uu____14788,
                      (FStar_Parser_AST.mk_term record1
                         top.FStar_Parser_AST.range
                         top.FStar_Parser_AST.level)) in
                  FStar_Parser_AST.Let uu____14767 in
            let recterm1 =
              FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level in
            let uu____14874 = desugar_term_aq env recterm1 in
            (match uu____14874 with
             | (e, s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____14890;
                         FStar_Syntax_Syntax.vars = uu____14891;_},
                       args)
                      ->
                      let uu____14917 =
                        let uu____14918 =
                          let uu____14919 =
                            let uu____14936 =
                              let uu____14939 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos in
                              let uu____14940 =
                                let uu____14943 =
                                  let uu____14944 =
                                    let uu____14951 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst) in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____14951) in
                                  FStar_Syntax_Syntax.Record_ctor uu____14944 in
                                FStar_Pervasives_Native.Some uu____14943 in
                              FStar_Syntax_Syntax.fvar uu____14939
                                FStar_Syntax_Syntax.delta_constant
                                uu____14940 in
                            (uu____14936, args) in
                          FStar_Syntax_Syntax.Tm_app uu____14919 in
                        FStar_All.pipe_left mk uu____14918 in
                      (uu____14917, s)
                  | uu____14980 -> (e, s)))
        | FStar_Parser_AST.Project (e, f) ->
            let uu____14983 =
              FStar_Syntax_DsEnv.fail_or env
                (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f in
            (match uu____14983 with
             | (constrname, is_rec) ->
                 let uu____14998 = desugar_term_aq env e in
                 (match uu____14998 with
                  | (e1, s) ->
                      let projname =
                        let uu____15010 = FStar_Ident.ident_of_lid f in
                        FStar_Syntax_Util.mk_field_projector_name_from_ident
                          constrname uu____15010 in
                      let qual =
                        if is_rec
                        then
                          let uu____15016 =
                            let uu____15017 =
                              let uu____15022 = FStar_Ident.ident_of_lid f in
                              (constrname, uu____15022) in
                            FStar_Syntax_Syntax.Record_projector uu____15017 in
                          FStar_Pervasives_Native.Some uu____15016
                        else FStar_Pervasives_Native.None in
                      let uu____15024 =
                        let uu____15025 =
                          let uu____15026 =
                            let uu____15043 =
                              let uu____15046 =
                                FStar_Ident.set_lid_range projname
                                  top.FStar_Parser_AST.range in
                              FStar_Syntax_Syntax.fvar uu____15046
                                (FStar_Syntax_Syntax.Delta_equational_at_level
                                   Prims.int_one) qual in
                            let uu____15047 =
                              let uu____15058 = FStar_Syntax_Syntax.as_arg e1 in
                              [uu____15058] in
                            (uu____15043, uu____15047) in
                          FStar_Syntax_Syntax.Tm_app uu____15026 in
                        FStar_All.pipe_left mk uu____15025 in
                      (uu____15024, s)))
        | FStar_Parser_AST.NamedTyp (n, e) ->
            ((let uu____15098 = FStar_Ident.range_of_id n in
              FStar_Errors.log_issue uu____15098
                (FStar_Errors.Warning_IgnoredBinding,
                  "This name is being ignored"));
             desugar_term_aq env e)
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e in
            let uu____15106 =
              let uu____15107 = FStar_Syntax_Subst.compress tm in
              uu____15107.FStar_Syntax_Syntax.n in
            (match uu____15106 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____15115 =
                   let uu___2068_15116 =
                     let uu____15117 =
                       let uu____15118 = FStar_Syntax_Syntax.lid_of_fv fv in
                       FStar_Ident.string_of_lid uu____15118 in
                     FStar_Syntax_Util.exp_string uu____15117 in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___2068_15116.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___2068_15116.FStar_Syntax_Syntax.vars)
                   } in
                 (uu____15115, noaqs)
             | uu____15119 ->
                 let uu____15120 =
                   let uu____15125 =
                     let uu____15126 = FStar_Syntax_Print.term_to_string tm in
                     Prims.op_Hat "VQuote, expected an fvar, got: "
                       uu____15126 in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____15125) in
                 FStar_Errors.raise_error uu____15120
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e, FStar_Parser_AST.Static) ->
            let uu____15132 = desugar_term_aq env e in
            (match uu____15132 with
             | (tm, vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   } in
                 let uu____15144 =
                   FStar_All.pipe_left mk
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi)) in
                 (uu____15144, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun in
            let uu____15149 = FStar_Syntax_Syntax.bv_to_name bv in
            let uu____15150 =
              let uu____15151 =
                let uu____15158 = desugar_term env e in (bv, uu____15158) in
              [uu____15151] in
            (uu____15149, uu____15150)
        | FStar_Parser_AST.Quote (e, FStar_Parser_AST.Dynamic) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              } in
            let uu____15183 =
              let uu____15184 =
                let uu____15185 =
                  let uu____15192 = desugar_term env e in (uu____15192, qi) in
                FStar_Syntax_Syntax.Tm_quoted uu____15185 in
              FStar_All.pipe_left mk uu____15184 in
            (uu____15183, noaqs)
        | FStar_Parser_AST.CalcProof (rel, init_expr, steps) ->
            let is_impl rel1 =
              let is_impl_t t =
                match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.imp_lid
                | uu____15217 -> false in
              let uu____15218 =
                let uu____15219 = unparen rel1 in
                uu____15219.FStar_Parser_AST.tm in
              match uu____15218 with
              | FStar_Parser_AST.Op (id, uu____15221) ->
                  let uu____15226 = op_as_term env (Prims.of_int (2)) id in
                  (match uu____15226 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None -> false)
              | FStar_Parser_AST.Var lid ->
                  let uu____15231 = desugar_name' (fun x -> x) env true lid in
                  (match uu____15231 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None -> false)
              | FStar_Parser_AST.Tvar id ->
                  let uu____15239 = FStar_Syntax_DsEnv.try_lookup_id env id in
                  (match uu____15239 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None -> false)
              | uu____15243 -> false in
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
              let uu____15261 =
                let uu____15262 =
                  let uu____15269 =
                    let uu____15270 =
                      let uu____15271 =
                        let uu____15280 =
                          FStar_Parser_AST.mkApp rel1
                            [(xt, FStar_Parser_AST.Nothing);
                            (yt, FStar_Parser_AST.Nothing)]
                            rel1.FStar_Parser_AST.range in
                        let uu____15293 =
                          let uu____15294 =
                            let uu____15295 = FStar_Ident.lid_of_str "Type0" in
                            FStar_Parser_AST.Name uu____15295 in
                          FStar_Parser_AST.mk_term uu____15294
                            rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr in
                        (uu____15280, uu____15293,
                          FStar_Pervasives_Native.None) in
                      FStar_Parser_AST.Ascribed uu____15271 in
                    FStar_Parser_AST.mk_term uu____15270
                      rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr in
                  (pats, uu____15269) in
                FStar_Parser_AST.Abs uu____15262 in
              FStar_Parser_AST.mk_term uu____15261
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
              let uu____15315 = FStar_List.last steps in
              match uu____15315 with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.CalcStep
                  (uu____15318, uu____15319, last_expr)) -> last_expr
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
            let uu____15345 =
              FStar_List.fold_left
                (fun uu____15363 ->
                   fun uu____15364 ->
                     match (uu____15363, uu____15364) with
                     | ((e1, prev), FStar_Parser_AST.CalcStep
                        (rel2, just, next_expr)) ->
                         let just1 =
                           let uu____15387 = is_impl rel2 in
                           if uu____15387
                           then
                             let uu____15388 =
                               let uu____15395 =
                                 let uu____15400 =
                                   FStar_Parser_AST.thunk just in
                                 (uu____15400, FStar_Parser_AST.Nothing) in
                               [uu____15395] in
                             FStar_Parser_AST.mkApp
                               (push_impl just.FStar_Parser_AST.range)
                               uu____15388 just.FStar_Parser_AST.range
                           else just in
                         let pf =
                           let uu____15411 =
                             let uu____15418 =
                               let uu____15425 =
                                 let uu____15432 =
                                   let uu____15439 =
                                     let uu____15444 = eta_and_annot rel2 in
                                     (uu____15444, FStar_Parser_AST.Nothing) in
                                   let uu____15445 =
                                     let uu____15452 =
                                       let uu____15459 =
                                         let uu____15464 =
                                           FStar_Parser_AST.thunk e1 in
                                         (uu____15464,
                                           FStar_Parser_AST.Nothing) in
                                       let uu____15465 =
                                         let uu____15472 =
                                           let uu____15477 =
                                             FStar_Parser_AST.thunk just1 in
                                           (uu____15477,
                                             FStar_Parser_AST.Nothing) in
                                         [uu____15472] in
                                       uu____15459 :: uu____15465 in
                                     (next_expr, FStar_Parser_AST.Nothing) ::
                                       uu____15452 in
                                   uu____15439 :: uu____15445 in
                                 (prev, FStar_Parser_AST.Hash) :: uu____15432 in
                               (init_expr, FStar_Parser_AST.Hash) ::
                                 uu____15425 in
                             ((wild rel2.FStar_Parser_AST.range),
                               FStar_Parser_AST.Hash) :: uu____15418 in
                           FStar_Parser_AST.mkApp
                             (step rel2.FStar_Parser_AST.range) uu____15411
                             FStar_Range.dummyRange in
                         (pf, next_expr)) (e, init_expr) steps in
            (match uu____15345 with
             | (e1, uu____15515) ->
                 let e2 =
                   let uu____15517 =
                     let uu____15524 =
                       let uu____15531 =
                         let uu____15538 =
                           let uu____15543 = FStar_Parser_AST.thunk e1 in
                           (uu____15543, FStar_Parser_AST.Nothing) in
                         [uu____15538] in
                       (last_expr, FStar_Parser_AST.Hash) :: uu____15531 in
                     (init_expr, FStar_Parser_AST.Hash) :: uu____15524 in
                   FStar_Parser_AST.mkApp finish uu____15517
                     top.FStar_Parser_AST.range in
                 desugar_term_maybe_top top_level env e2)
        | uu____15560 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____15561 = desugar_formula env top in (uu____15561, noaqs)
        | uu____15562 ->
            let uu____15563 =
              let uu____15568 =
                let uu____15569 = FStar_Parser_AST.term_to_string top in
                Prims.op_Hat "Unexpected term: " uu____15569 in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____15568) in
            FStar_Errors.raise_error uu____15563 top.FStar_Parser_AST.range
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
           (fun uu____15610 ->
              match uu____15610 with
              | (a, imp) ->
                  let uu____15623 = desugar_term env a in
                  arg_withimp_e imp uu____15623))
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
          let is_requires uu____15656 =
            match uu____15656 with
            | (t1, uu____15662) ->
                let uu____15663 =
                  let uu____15664 = unparen t1 in
                  uu____15664.FStar_Parser_AST.tm in
                (match uu____15663 with
                 | FStar_Parser_AST.Requires uu____15665 -> true
                 | uu____15672 -> false) in
          let is_ensures uu____15682 =
            match uu____15682 with
            | (t1, uu____15688) ->
                let uu____15689 =
                  let uu____15690 = unparen t1 in
                  uu____15690.FStar_Parser_AST.tm in
                (match uu____15689 with
                 | FStar_Parser_AST.Ensures uu____15691 -> true
                 | uu____15698 -> false) in
          let is_app head uu____15713 =
            match uu____15713 with
            | (t1, uu____15719) ->
                let uu____15720 =
                  let uu____15721 = unparen t1 in
                  uu____15721.FStar_Parser_AST.tm in
                (match uu____15720 with
                 | FStar_Parser_AST.App
                     ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                        FStar_Parser_AST.range = uu____15723;
                        FStar_Parser_AST.level = uu____15724;_},
                      uu____15725, uu____15726)
                     ->
                     let uu____15727 =
                       let uu____15728 = FStar_Ident.ident_of_lid d in
                       FStar_Ident.string_of_id uu____15728 in
                     uu____15727 = head
                 | uu____15729 -> false) in
          let is_smt_pat uu____15739 =
            match uu____15739 with
            | (t1, uu____15745) ->
                let uu____15746 =
                  let uu____15747 = unparen t1 in
                  uu____15747.FStar_Parser_AST.tm in
                (match uu____15746 with
                 | FStar_Parser_AST.Construct
                     (cons,
                      ({
                         FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                           (smtpat, uu____15750);
                         FStar_Parser_AST.range = uu____15751;
                         FStar_Parser_AST.level = uu____15752;_},
                       uu____15753)::uu____15754::[])
                     ->
                     (FStar_Ident.lid_equals cons FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s ->
                             let uu____15792 =
                               FStar_Ident.string_of_lid smtpat in
                             uu____15792 = s)
                          ["SMTPat"; "SMTPatT"; "SMTPatOr"])
                 | FStar_Parser_AST.Construct
                     (cons,
                      ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var smtpat;
                         FStar_Parser_AST.range = uu____15795;
                         FStar_Parser_AST.level = uu____15796;_},
                       uu____15797)::uu____15798::[])
                     ->
                     (FStar_Ident.lid_equals cons FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s ->
                             let uu____15824 =
                               FStar_Ident.string_of_lid smtpat in
                             uu____15824 = s) ["smt_pat"; "smt_pat_or"])
                 | uu____15825 -> false) in
          let is_decreases = is_app "decreases" in
          let pre_process_comp_typ t1 =
            let uu____15857 = head_and_args t1 in
            match uu____15857 with
            | (head, args) ->
                (match head.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Name lemma when
                     let uu____15915 =
                       let uu____15916 = FStar_Ident.ident_of_lid lemma in
                       FStar_Ident.string_of_id uu____15916 in
                     uu____15915 = "Lemma" ->
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
                     let thunk_ens uu____15948 =
                       match uu____15948 with
                       | (e, i) ->
                           let uu____15959 = FStar_Parser_AST.thunk e in
                           (uu____15959, i) in
                     let fail_lemma uu____15971 =
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
                           let uu____16051 =
                             let uu____16058 =
                               let uu____16065 = thunk_ens ens in
                               [uu____16065; nil_pat] in
                             req_true :: uu____16058 in
                           unit_tm :: uu____16051
                       | req::ens::[] when
                           (is_requires req) && (is_ensures ens) ->
                           let uu____16112 =
                             let uu____16119 =
                               let uu____16126 = thunk_ens ens in
                               [uu____16126; nil_pat] in
                             req :: uu____16119 in
                           unit_tm :: uu____16112
                       | ens::smtpat::[] when
                           (((let uu____16175 = is_requires ens in
                              Prims.op_Negation uu____16175) &&
                               (let uu____16177 = is_smt_pat ens in
                                Prims.op_Negation uu____16177))
                              &&
                              (let uu____16179 = is_decreases ens in
                               Prims.op_Negation uu____16179))
                             && (is_smt_pat smtpat)
                           ->
                           let uu____16180 =
                             let uu____16187 =
                               let uu____16194 = thunk_ens ens in
                               [uu____16194; smtpat] in
                             req_true :: uu____16187 in
                           unit_tm :: uu____16180
                       | ens::dec::[] when
                           (is_ensures ens) && (is_decreases dec) ->
                           let uu____16241 =
                             let uu____16248 =
                               let uu____16255 = thunk_ens ens in
                               [uu____16255; nil_pat; dec] in
                             req_true :: uu____16248 in
                           unit_tm :: uu____16241
                       | ens::dec::smtpat::[] when
                           ((is_ensures ens) && (is_decreases dec)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____16315 =
                             let uu____16322 =
                               let uu____16329 = thunk_ens ens in
                               [uu____16329; smtpat; dec] in
                             req_true :: uu____16322 in
                           unit_tm :: uu____16315
                       | req::ens::dec::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_decreases dec)
                           ->
                           let uu____16389 =
                             let uu____16396 =
                               let uu____16403 = thunk_ens ens in
                               [uu____16403; nil_pat; dec] in
                             req :: uu____16396 in
                           unit_tm :: uu____16389
                       | req::ens::smtpat::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____16463 =
                             let uu____16470 =
                               let uu____16477 = thunk_ens ens in
                               [uu____16477; smtpat] in
                             req :: uu____16470 in
                           unit_tm :: uu____16463
                       | req::ens::dec::smtpat::[] when
                           (((is_requires req) && (is_ensures ens)) &&
                              (is_smt_pat smtpat))
                             && (is_decreases dec)
                           ->
                           let uu____16542 =
                             let uu____16549 =
                               let uu____16556 = thunk_ens ens in
                               [uu____16556; dec; smtpat] in
                             req :: uu____16549 in
                           unit_tm :: uu____16542
                       | _other -> fail_lemma () in
                     let head_and_attributes =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) lemma in
                     (head_and_attributes, args1)
                 | FStar_Parser_AST.Name l when
                     FStar_Syntax_DsEnv.is_effect_name env l ->
                     let uu____16618 =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) l in
                     (uu____16618, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____16646 = FStar_Syntax_DsEnv.current_module env in
                      FStar_Ident.lid_equals uu____16646
                        FStar_Parser_Const.prims_lid)
                       &&
                       (let uu____16648 =
                          let uu____16649 = FStar_Ident.ident_of_lid l in
                          FStar_Ident.string_of_id uu____16649 in
                        uu____16648 = "Tot")
                     ->
                     let uu____16650 =
                       let uu____16657 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head.FStar_Parser_AST.range in
                       (uu____16657, []) in
                     (uu____16650, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____16675 = FStar_Syntax_DsEnv.current_module env in
                      FStar_Ident.lid_equals uu____16675
                        FStar_Parser_Const.prims_lid)
                       &&
                       (let uu____16677 =
                          let uu____16678 = FStar_Ident.ident_of_lid l in
                          FStar_Ident.string_of_id uu____16678 in
                        uu____16677 = "GTot")
                     ->
                     let uu____16679 =
                       let uu____16686 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_GTot_lid
                           head.FStar_Parser_AST.range in
                       (uu____16686, []) in
                     (uu____16679, args)
                 | FStar_Parser_AST.Name l when
                     ((let uu____16704 =
                         let uu____16705 = FStar_Ident.ident_of_lid l in
                         FStar_Ident.string_of_id uu____16705 in
                       uu____16704 = "Type") ||
                        (let uu____16707 =
                           let uu____16708 = FStar_Ident.ident_of_lid l in
                           FStar_Ident.string_of_id uu____16708 in
                         uu____16707 = "Type0"))
                       ||
                       (let uu____16710 =
                          let uu____16711 = FStar_Ident.ident_of_lid l in
                          FStar_Ident.string_of_id uu____16711 in
                        uu____16710 = "Effect")
                     ->
                     let uu____16712 =
                       let uu____16719 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head.FStar_Parser_AST.range in
                       (uu____16719, []) in
                     (uu____16712, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____16742 when allow_type_promotion ->
                     let default_effect =
                       let uu____16744 = FStar_Options.ml_ish () in
                       if uu____16744
                       then FStar_Parser_Const.effect_ML_lid
                       else
                         ((let uu____16747 =
                             FStar_Options.warn_default_effects () in
                           if uu____16747
                           then
                             FStar_Errors.log_issue
                               head.FStar_Parser_AST.range
                               (FStar_Errors.Warning_UseDefaultEffect,
                                 "Using default effect Tot")
                           else ());
                          FStar_Parser_Const.effect_Tot_lid) in
                     let uu____16749 =
                       let uu____16756 =
                         FStar_Ident.set_lid_range default_effect
                           head.FStar_Parser_AST.range in
                       (uu____16756, []) in
                     (uu____16749, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____16779 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_EffectNotFound,
                         "Expected an effect constructor")
                       t1.FStar_Parser_AST.range) in
          let uu____16796 = pre_process_comp_typ t in
          match uu____16796 with
          | ((eff, cattributes), args) ->
              (if (FStar_List.length args) = Prims.int_zero
               then
                 (let uu____16845 =
                    let uu____16850 =
                      let uu____16851 = FStar_Syntax_Print.lid_to_string eff in
                      FStar_Util.format1 "Not enough args to effect %s"
                        uu____16851 in
                    (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____16850) in
                  fail uu____16845)
               else ();
               (let is_universe uu____16862 =
                  match uu____16862 with
                  | (uu____16867, imp) -> imp = FStar_Parser_AST.UnivApp in
                let uu____16869 = FStar_Util.take is_universe args in
                match uu____16869 with
                | (universes, args1) ->
                    let universes1 =
                      FStar_List.map
                        (fun uu____16928 ->
                           match uu____16928 with
                           | (u, imp) -> desugar_universe u) universes in
                    let uu____16935 =
                      let uu____16950 = FStar_List.hd args1 in
                      let uu____16959 = FStar_List.tl args1 in
                      (uu____16950, uu____16959) in
                    (match uu____16935 with
                     | (result_arg, rest) ->
                         let result_typ =
                           desugar_typ env
                             (FStar_Pervasives_Native.fst result_arg) in
                         let rest1 = desugar_args env rest in
                         let uu____17014 =
                           let is_decrease uu____17052 =
                             match uu____17052 with
                             | (t1, uu____17062) ->
                                 (match t1.FStar_Syntax_Syntax.n with
                                  | FStar_Syntax_Syntax.Tm_app
                                      ({
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_fvar fv;
                                         FStar_Syntax_Syntax.pos =
                                           uu____17072;
                                         FStar_Syntax_Syntax.vars =
                                           uu____17073;_},
                                       uu____17074::[])
                                      ->
                                      FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Parser_Const.decreases_lid
                                  | uu____17113 -> false) in
                           FStar_All.pipe_right rest1
                             (FStar_List.partition is_decrease) in
                         (match uu____17014 with
                          | (dec, rest2) ->
                              let decreases_clause =
                                FStar_All.pipe_right dec
                                  (FStar_List.map
                                     (fun uu____17229 ->
                                        match uu____17229 with
                                        | (t1, uu____17239) ->
                                            (match t1.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____17248,
                                                  (arg, uu____17250)::[])
                                                 ->
                                                 FStar_Syntax_Syntax.DECREASES
                                                   arg
                                             | uu____17289 ->
                                                 failwith "impos"))) in
                              let no_additional_args =
                                let is_empty l =
                                  match l with
                                  | [] -> true
                                  | uu____17306 -> false in
                                (((is_empty decreases_clause) &&
                                    (is_empty rest2))
                                   && (is_empty cattributes))
                                  && (is_empty universes1) in
                              let uu____17317 =
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_Tot_lid) in
                              if uu____17317
                              then FStar_Syntax_Syntax.mk_Total result_typ
                              else
                                (let uu____17321 =
                                   no_additional_args &&
                                     (FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_GTot_lid) in
                                 if uu____17321
                                 then
                                   FStar_Syntax_Syntax.mk_GTotal result_typ
                                 else
                                   (let flags =
                                      let uu____17328 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid in
                                      if uu____17328
                                      then [FStar_Syntax_Syntax.LEMMA]
                                      else
                                        (let uu____17332 =
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_Tot_lid in
                                         if uu____17332
                                         then [FStar_Syntax_Syntax.TOTAL]
                                         else
                                           (let uu____17336 =
                                              FStar_Ident.lid_equals eff
                                                FStar_Parser_Const.effect_ML_lid in
                                            if uu____17336
                                            then
                                              [FStar_Syntax_Syntax.MLEFFECT]
                                            else
                                              (let uu____17340 =
                                                 FStar_Ident.lid_equals eff
                                                   FStar_Parser_Const.effect_GTot_lid in
                                               if uu____17340
                                               then
                                                 [FStar_Syntax_Syntax.SOMETRIVIAL]
                                               else []))) in
                                    let flags1 =
                                      FStar_List.append flags cattributes in
                                    let rest3 =
                                      let uu____17358 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid in
                                      if uu____17358
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
                                                    let uu____17447 =
                                                      FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos in
                                                    FStar_Syntax_Syntax.fvar
                                                      uu____17447
                                                      FStar_Syntax_Syntax.delta_constant
                                                      FStar_Pervasives_Native.None in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    nil
                                                    [(pattern,
                                                       (FStar_Pervasives_Native.Some
                                                          FStar_Syntax_Syntax.imp_tag))]
                                                    pat.FStar_Syntax_Syntax.pos
                                              | uu____17468 -> pat in
                                            let uu____17469 =
                                              let uu____17480 =
                                                let uu____17491 =
                                                  let uu____17500 =
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (pat1,
                                                           (FStar_Syntax_Syntax.Meta_desugared
                                                              FStar_Syntax_Syntax.Meta_smt_pat)))
                                                      pat1.FStar_Syntax_Syntax.pos in
                                                  (uu____17500, aq) in
                                                [uu____17491] in
                                              ens :: uu____17480 in
                                            req :: uu____17469
                                        | uu____17541 -> rest2
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
        let uu___2393_17575 = t in
        {
          FStar_Syntax_Syntax.n = (uu___2393_17575.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___2393_17575.FStar_Syntax_Syntax.vars)
        } in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___2400_17629 = b in
             {
               FStar_Parser_AST.b = (uu___2400_17629.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___2400_17629.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___2400_17629.FStar_Parser_AST.aqual)
             }) in
        let with_pats env1 uu____17658 body1 =
          match uu____17658 with
          | (names, pats1) ->
              (match (names, pats1) with
               | ([], []) -> body1
               | ([], uu____17704::uu____17705) ->
                   failwith
                     "Impossible: Annotated pattern without binders in scope"
               | uu____17722 ->
                   let names1 =
                     FStar_All.pipe_right names
                       (FStar_List.map
                          (fun i ->
                             let uu___2419_17750 =
                               FStar_Syntax_DsEnv.fail_or2
                                 (FStar_Syntax_DsEnv.try_lookup_id env1) i in
                             let uu____17751 = FStar_Ident.range_of_id i in
                             {
                               FStar_Syntax_Syntax.n =
                                 (uu___2419_17750.FStar_Syntax_Syntax.n);
                               FStar_Syntax_Syntax.pos = uu____17751;
                               FStar_Syntax_Syntax.vars =
                                 (uu___2419_17750.FStar_Syntax_Syntax.vars)
                             })) in
                   let pats2 =
                     FStar_All.pipe_right pats1
                       (FStar_List.map
                          (fun es ->
                             FStar_All.pipe_right es
                               (FStar_List.map
                                  (fun e ->
                                     let uu____17814 = desugar_term env1 e in
                                     FStar_All.pipe_left
                                       (arg_withimp_t
                                          FStar_Parser_AST.Nothing)
                                       uu____17814)))) in
                   mk
                     (FStar_Syntax_Syntax.Tm_meta
                        (body1,
                          (FStar_Syntax_Syntax.Meta_pattern (names1, pats2))))) in
        match tk with
        | (FStar_Pervasives_Native.Some a, k) ->
            let uu____17845 = FStar_Syntax_DsEnv.push_bv env a in
            (match uu____17845 with
             | (env1, a1) ->
                 let a2 =
                   let uu___2432_17855 = a1 in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___2432_17855.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___2432_17855.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   } in
                 let body1 = desugar_formula env1 body in
                 let body2 = with_pats env1 pats body1 in
                 let body3 =
                   let uu____17861 =
                     let uu____17864 =
                       let uu____17865 = FStar_Syntax_Syntax.mk_binder a2 in
                       [uu____17865] in
                     no_annot_abs uu____17864 body2 in
                   FStar_All.pipe_left setpos uu____17861 in
                 let uu____17886 =
                   let uu____17887 =
                     let uu____17904 =
                       let uu____17907 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange in
                       FStar_Syntax_Syntax.fvar uu____17907
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            Prims.int_one) FStar_Pervasives_Native.None in
                     let uu____17908 =
                       let uu____17919 = FStar_Syntax_Syntax.as_arg body3 in
                       [uu____17919] in
                     (uu____17904, uu____17908) in
                   FStar_Syntax_Syntax.Tm_app uu____17887 in
                 FStar_All.pipe_left mk uu____17886)
        | uu____17958 -> failwith "impossible" in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest in
            let body1 =
              let uu____18022 = q (rest, pats, body) in
              let uu____18025 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range in
              FStar_Parser_AST.mk_term uu____18022 uu____18025
                FStar_Parser_AST.Formula in
            let uu____18026 = q ([b], ([], []), body1) in
            FStar_Parser_AST.mk_term uu____18026 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____18037 -> failwith "impossible" in
      let uu____18040 =
        let uu____18041 = unparen f in uu____18041.FStar_Parser_AST.tm in
      match uu____18040 with
      | FStar_Parser_AST.Labeled (f1, l, p) ->
          let f2 = desugar_formula env f1 in
          FStar_All.pipe_left mk
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([], uu____18048, uu____18049) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([], uu____18072, uu____18073) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3, pats, body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____18128 =
            push_quant (fun x -> FStar_Parser_AST.QForall x) binders pats
              body in
          desugar_formula env uu____18128
      | FStar_Parser_AST.QExists (_1::_2::_3, pats, body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____18172 =
            push_quant (fun x -> FStar_Parser_AST.QExists x) binders pats
              body in
          desugar_formula env uu____18172
      | FStar_Parser_AST.QForall (b::[], pats, body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[], pats, body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____18235 -> desugar_term env f
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
          let uu____18246 = desugar_typ env t in
          ((FStar_Pervasives_Native.Some x), uu____18246)
      | FStar_Parser_AST.Annotated (x, t) ->
          let uu____18251 = desugar_typ env t in
          ((FStar_Pervasives_Native.Some x), uu____18251)
      | FStar_Parser_AST.TVariable x ->
          let uu____18255 =
            let uu____18256 = FStar_Ident.range_of_id x in
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              uu____18256 in
          ((FStar_Pervasives_Native.Some x), uu____18255)
      | FStar_Parser_AST.NoName t ->
          let uu____18260 = desugar_typ env t in
          (FStar_Pervasives_Native.None, uu____18260)
      | FStar_Parser_AST.Variable x ->
          let uu____18264 =
            let uu____18265 = FStar_Ident.range_of_id x in tun_r uu____18265 in
          ((FStar_Pervasives_Native.Some x), uu____18264)
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
      fun uu___11_18270 ->
        match uu___11_18270 with
        | (FStar_Pervasives_Native.None, k) ->
            let uu____18292 = FStar_Syntax_Syntax.null_binder k in
            (uu____18292, env)
        | (FStar_Pervasives_Native.Some a, k) ->
            let uu____18309 = FStar_Syntax_DsEnv.push_bv env a in
            (match uu____18309 with
             | (env1, a1) ->
                 let uu____18326 =
                   let uu____18333 = trans_aqual env1 imp in
                   ((let uu___2532_18339 = a1 in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___2532_18339.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___2532_18339.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____18333) in
                 (uu____18326, env1))
and (trans_aqual :
  env_t ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env ->
    fun uu___12_18347 ->
      match uu___12_18347 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta
          (FStar_Parser_AST.Arg_qualifier_meta_tac t)) ->
          let uu____18351 =
            let uu____18352 =
              let uu____18353 = desugar_term env t in
              FStar_Syntax_Syntax.Arg_qualifier_meta_tac uu____18353 in
            FStar_Syntax_Syntax.Meta uu____18352 in
          FStar_Pervasives_Native.Some uu____18351
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
      let uu____18383 =
        FStar_List.fold_left
          (fun uu____18416 ->
             fun b ->
               match uu____18416 with
               | (env1, out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___2557_18460 = b in
                        {
                          FStar_Parser_AST.b =
                            (uu___2557_18460.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___2557_18460.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___2557_18460.FStar_Parser_AST.aqual)
                        }) in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a, k) ->
                        let uu____18475 = FStar_Syntax_DsEnv.push_bv env1 a in
                        (match uu____18475 with
                         | (env2, a1) ->
                             let a2 =
                               let uu___2567_18493 = a1 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2567_18493.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2567_18493.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               } in
                             let uu____18494 =
                               let uu____18501 =
                                 let uu____18506 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual in
                                 (a2, uu____18506) in
                               uu____18501 :: out in
                             (env2, uu____18494))
                    | uu____18517 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs in
      match uu____18383 with
      | (env1, tpars) -> (env1, (FStar_List.rev tpars))
let (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun env ->
    fun cattributes ->
      let desugar_attribute t =
        let uu____18602 =
          let uu____18603 = unparen t in uu____18603.FStar_Parser_AST.tm in
        match uu____18602 with
        | FStar_Parser_AST.Var lid when
            let uu____18605 = FStar_Ident.string_of_lid lid in
            uu____18605 = "cps" -> FStar_Syntax_Syntax.CPS
        | uu____18606 ->
            let uu____18607 =
              let uu____18612 =
                let uu____18613 = FStar_Parser_AST.term_to_string t in
                Prims.op_Hat "Unknown attribute " uu____18613 in
              (FStar_Errors.Fatal_UnknownAttribute, uu____18612) in
            FStar_Errors.raise_error uu____18607 t.FStar_Parser_AST.range in
      FStar_List.map desugar_attribute cattributes
let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x, uu____18626) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x, uu____18628) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu____18631 -> FStar_Pervasives_Native.None
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs ->
    FStar_List.collect
      (fun b ->
         let uu____18648 = binder_ident b in
         FStar_Common.list_of_option uu____18648) bs
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
               (fun uu___13_18684 ->
                  match uu___13_18684 with
                  | FStar_Syntax_Syntax.NoExtract -> true
                  | FStar_Syntax_Syntax.Abstract -> true
                  | FStar_Syntax_Syntax.Private -> true
                  | uu____18685 -> false)) in
        let quals2 q =
          let uu____18698 =
            (let uu____18701 = FStar_Syntax_DsEnv.iface env in
             Prims.op_Negation uu____18701) ||
              (FStar_Syntax_DsEnv.admitted_iface env) in
          if uu____18698
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1 in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d in
                let uu____18715 = FStar_Ident.range_of_lid disc_name in
                let uu____18716 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d] in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____18715;
                  FStar_Syntax_Syntax.sigquals = uu____18716;
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
            let uu____18755 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i ->
                      fun uu____18791 ->
                        match uu____18791 with
                        | (x, uu____18801) ->
                            let field_name =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i in
                            let only_decl =
                              ((let uu____18810 =
                                  FStar_Syntax_DsEnv.current_module env in
                                FStar_Ident.lid_equals
                                  FStar_Parser_Const.prims_lid uu____18810)
                                 || (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                ||
                                (let uu____18812 =
                                   let uu____18813 =
                                     FStar_Syntax_DsEnv.current_module env in
                                   FStar_Ident.string_of_lid uu____18813 in
                                 FStar_Options.dont_gen_projectors
                                   uu____18812) in
                            let no_decl =
                              FStar_Syntax_Syntax.is_type
                                x.FStar_Syntax_Syntax.sort in
                            let quals q =
                              if only_decl
                              then
                                let uu____18829 =
                                  FStar_List.filter
                                    (fun uu___14_18833 ->
                                       match uu___14_18833 with
                                       | FStar_Syntax_Syntax.Abstract ->
                                           false
                                       | uu____18834 -> true) q in
                                FStar_Syntax_Syntax.Assumption :: uu____18829
                              else q in
                            let quals1 =
                              let iquals1 =
                                FStar_All.pipe_right iquals
                                  (FStar_List.filter
                                     (fun uu___15_18847 ->
                                        match uu___15_18847 with
                                        | FStar_Syntax_Syntax.NoExtract ->
                                            true
                                        | FStar_Syntax_Syntax.Abstract ->
                                            true
                                        | FStar_Syntax_Syntax.Private -> true
                                        | uu____18848 -> false)) in
                              quals (FStar_Syntax_Syntax.OnlyName ::
                                (FStar_Syntax_Syntax.Projector
                                   (lid, (x.FStar_Syntax_Syntax.ppname))) ::
                                iquals1) in
                            let decl =
                              let uu____18850 =
                                FStar_Ident.range_of_lid field_name in
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_declare_typ
                                     (field_name, [],
                                       FStar_Syntax_Syntax.tun));
                                FStar_Syntax_Syntax.sigrng = uu____18850;
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
                                 let uu____18855 =
                                   FStar_All.pipe_right quals1
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Abstract) in
                                 if uu____18855
                                 then
                                   FStar_Syntax_Syntax.Delta_abstract
                                     (FStar_Syntax_Syntax.Delta_equational_at_level
                                        Prims.int_one)
                                 else
                                   FStar_Syntax_Syntax.Delta_equational_at_level
                                     Prims.int_one in
                               let lb =
                                 let uu____18860 =
                                   let uu____18865 =
                                     FStar_Syntax_Syntax.lid_as_fv field_name
                                       dd FStar_Pervasives_Native.None in
                                   FStar_Util.Inr uu____18865 in
                                 {
                                   FStar_Syntax_Syntax.lbname = uu____18860;
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
                                 let uu____18869 =
                                   let uu____18870 =
                                     let uu____18877 =
                                       let uu____18880 =
                                         let uu____18881 =
                                           FStar_All.pipe_right
                                             lb.FStar_Syntax_Syntax.lbname
                                             FStar_Util.right in
                                         FStar_All.pipe_right uu____18881
                                           (fun fv ->
                                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                       [uu____18880] in
                                     ((false, [lb]), uu____18877) in
                                   FStar_Syntax_Syntax.Sig_let uu____18870 in
                                 {
                                   FStar_Syntax_Syntax.sigel = uu____18869;
                                   FStar_Syntax_Syntax.sigrng = p;
                                   FStar_Syntax_Syntax.sigquals = quals1;
                                   FStar_Syntax_Syntax.sigmeta =
                                     FStar_Syntax_Syntax.default_sigmeta;
                                   FStar_Syntax_Syntax.sigattrs = [];
                                   FStar_Syntax_Syntax.sigopts =
                                     FStar_Pervasives_Native.None
                                 } in
                               if no_decl then [impl] else [decl; impl]))) in
            FStar_All.pipe_right uu____18755 FStar_List.flatten
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
            (lid, uu____18925, t, uu____18927, n, uu____18929) when
            let uu____18934 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid in
            Prims.op_Negation uu____18934 ->
            let uu____18935 = FStar_Syntax_Util.arrow_formals t in
            (match uu____18935 with
             | (formals, uu____18945) ->
                 (match formals with
                  | [] -> []
                  | uu____18958 ->
                      let filter_records uu___16_18966 =
                        match uu___16_18966 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____18969, fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____18981 -> FStar_Pervasives_Native.None in
                      let fv_qual =
                        let uu____18983 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records in
                        match uu____18983 with
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
                      let uu____18993 = FStar_Util.first_N n formals in
                      (match uu____18993 with
                       | (uu____19022, rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____19056 -> []
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
                        let uu____19149 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env lid in
                        FStar_All.pipe_right uu____19149
                          FStar_Pervasives_Native.snd in
                      let dd =
                        let uu____19173 =
                          FStar_All.pipe_right quals
                            (FStar_List.contains FStar_Syntax_Syntax.Abstract) in
                        if uu____19173
                        then
                          let uu____19176 =
                            FStar_Syntax_Util.incr_delta_qualifier t in
                          FStar_Syntax_Syntax.Delta_abstract uu____19176
                        else FStar_Syntax_Util.incr_delta_qualifier t in
                      let lb =
                        let uu____19179 =
                          let uu____19184 =
                            FStar_Syntax_Syntax.lid_as_fv lid dd
                              FStar_Pervasives_Native.None in
                          FStar_Util.Inr uu____19184 in
                        let uu____19185 =
                          if FStar_Util.is_some kopt
                          then
                            let uu____19190 =
                              let uu____19193 =
                                FStar_All.pipe_right kopt FStar_Util.must in
                              FStar_Syntax_Syntax.mk_Total uu____19193 in
                            FStar_Syntax_Util.arrow typars uu____19190
                          else FStar_Syntax_Syntax.tun in
                        let uu____19197 = no_annot_abs typars t in
                        {
                          FStar_Syntax_Syntax.lbname = uu____19179;
                          FStar_Syntax_Syntax.lbunivs = uvs;
                          FStar_Syntax_Syntax.lbtyp = uu____19185;
                          FStar_Syntax_Syntax.lbeff =
                            FStar_Parser_Const.effect_Tot_lid;
                          FStar_Syntax_Syntax.lbdef = uu____19197;
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
          let tycon_id uu___17_19248 =
            match uu___17_19248 with
            | FStar_Parser_AST.TyconAbstract (id, uu____19250, uu____19251)
                -> id
            | FStar_Parser_AST.TyconAbbrev
                (id, uu____19261, uu____19262, uu____19263) -> id
            | FStar_Parser_AST.TyconRecord
                (id, uu____19273, uu____19274, uu____19275) -> id
            | FStar_Parser_AST.TyconVariant
                (id, uu____19297, uu____19298, uu____19299) -> id in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x, uu____19335) ->
                let uu____19336 =
                  let uu____19337 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____19337 in
                let uu____19338 = FStar_Ident.range_of_id x in
                FStar_Parser_AST.mk_term uu____19336 uu____19338
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____19340 =
                  let uu____19341 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____19341 in
                let uu____19342 = FStar_Ident.range_of_id x in
                FStar_Parser_AST.mk_term uu____19340 uu____19342
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a, uu____19344) ->
                let uu____19345 = FStar_Ident.range_of_id a in
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  uu____19345 FStar_Parser_AST.Type_level
            | FStar_Parser_AST.TVariable a ->
                let uu____19347 = FStar_Ident.range_of_id a in
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  uu____19347 FStar_Parser_AST.Type_level
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
              | uu____19377 -> FStar_Parser_AST.Nothing in
            FStar_List.fold_left
              (fun out ->
                 fun b ->
                   let uu____19385 =
                     let uu____19386 =
                       let uu____19393 = binder_to_term b in
                       (out, uu____19393, (imp_of_aqual b)) in
                     FStar_Parser_AST.App uu____19386 in
                   FStar_Parser_AST.mk_term uu____19385
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders in
          let tycon_record_as_variant uu___18_19405 =
            match uu___18_19405 with
            | FStar_Parser_AST.TyconRecord (id, parms, kopt, fields) ->
                let constrName =
                  let uu____19437 =
                    let uu____19442 =
                      let uu____19443 = FStar_Ident.string_of_id id in
                      Prims.op_Hat "Mk" uu____19443 in
                    let uu____19444 = FStar_Ident.range_of_id id in
                    (uu____19442, uu____19444) in
                  FStar_Ident.mk_ident uu____19437 in
                let mfields =
                  FStar_List.map
                    (fun uu____19456 ->
                       match uu____19456 with
                       | (x, t) ->
                           let uu____19463 = FStar_Ident.range_of_id x in
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated (x, t)) uu____19463
                             FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields in
                let result =
                  let uu____19465 =
                    let uu____19466 =
                      let uu____19467 = FStar_Ident.lid_of_ids [id] in
                      FStar_Parser_AST.Var uu____19467 in
                    let uu____19468 = FStar_Ident.range_of_id id in
                    FStar_Parser_AST.mk_term uu____19466 uu____19468
                      FStar_Parser_AST.Type_level in
                  apply_binders uu____19465 parms in
                let constrTyp =
                  let uu____19470 = FStar_Ident.range_of_id id in
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    uu____19470 FStar_Parser_AST.Type_level in
                let names =
                  let uu____19476 = binder_idents parms in id :: uu____19476 in
                (FStar_List.iter
                   (fun uu____19490 ->
                      match uu____19490 with
                      | (f, uu____19496) ->
                          let uu____19497 =
                            FStar_Util.for_some
                              (fun i -> FStar_Ident.ident_equals f i) names in
                          if uu____19497
                          then
                            let uu____19500 =
                              let uu____19505 =
                                let uu____19506 = FStar_Ident.string_of_id f in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu____19506 in
                              (FStar_Errors.Error_FieldShadow, uu____19505) in
                            let uu____19507 = FStar_Ident.range_of_id f in
                            FStar_Errors.raise_error uu____19500 uu____19507
                          else ()) fields;
                 (let uu____19509 =
                    FStar_All.pipe_right fields
                      (FStar_List.map FStar_Pervasives_Native.fst) in
                  ((FStar_Parser_AST.TyconVariant
                      (id, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp), false)])),
                    uu____19509)))
            | uu____19558 -> failwith "impossible" in
          let desugar_abstract_tc quals1 _env mutuals uu___19_19597 =
            match uu___19_19597 with
            | FStar_Parser_AST.TyconAbstract (id, binders, kopt) ->
                let uu____19621 = typars_of_binders _env binders in
                (match uu____19621 with
                 | (_env', typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k in
                     let tconstr =
                       let uu____19657 =
                         let uu____19658 =
                           let uu____19659 = FStar_Ident.lid_of_ids [id] in
                           FStar_Parser_AST.Var uu____19659 in
                         let uu____19660 = FStar_Ident.range_of_id id in
                         FStar_Parser_AST.mk_term uu____19658 uu____19660
                           FStar_Parser_AST.Type_level in
                       apply_binders uu____19657 binders in
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
                     let uu____19669 =
                       FStar_Syntax_DsEnv.push_top_level_rec_binding _env id
                         FStar_Syntax_Syntax.delta_constant in
                     (match uu____19669 with
                      | (_env1, uu____19685) ->
                          let uu____19690 =
                            FStar_Syntax_DsEnv.push_top_level_rec_binding
                              _env' id FStar_Syntax_Syntax.delta_constant in
                          (match uu____19690 with
                           | (_env2, uu____19706) ->
                               (_env1, _env2, se, tconstr))))
            | uu____19711 -> failwith "Unexpected tycon" in
          let push_tparams env1 bs =
            let uu____19753 =
              FStar_List.fold_left
                (fun uu____19787 ->
                   fun uu____19788 ->
                     match (uu____19787, uu____19788) with
                     | ((env2, tps), (x, imp)) ->
                         let uu____19857 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname in
                         (match uu____19857 with
                          | (env3, y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs in
            match uu____19753 with
            | (env2, bs1) -> (env2, (FStar_List.rev bs1)) in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id, bs, kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None ->
                    let uu____19948 =
                      let uu____19949 = FStar_Ident.range_of_id id in
                      tm_type_z uu____19949 in
                    FStar_Pervasives_Native.Some uu____19948
                | uu____19950 -> kopt in
              let tc = FStar_Parser_AST.TyconAbstract (id, bs, kopt1) in
              let uu____19958 = desugar_abstract_tc quals env [] tc in
              (match uu____19958 with
               | (uu____19971, uu____19972, se, uu____19974) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l, uu____19977, typars, k, [], []) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____19994 =
                                 let uu____19995 = FStar_Options.ml_ish () in
                                 Prims.op_Negation uu____19995 in
                               if uu____19994
                               then
                                 let uu____19996 =
                                   let uu____20001 =
                                     let uu____20002 =
                                       FStar_Syntax_Print.lid_to_string l in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____20002 in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____20001) in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____19996
                               else ());
                              FStar_Syntax_Syntax.Assumption
                              ::
                              FStar_Syntax_Syntax.New
                              ::
                              quals1) in
                         let t =
                           match typars with
                           | [] -> k
                           | uu____20011 ->
                               let uu____20012 =
                                 let uu____20013 =
                                   let uu____20028 =
                                     FStar_Syntax_Syntax.mk_Total k in
                                   (typars, uu____20028) in
                                 FStar_Syntax_Syntax.Tm_arrow uu____20013 in
                               FStar_Syntax_Syntax.mk uu____20012
                                 se.FStar_Syntax_Syntax.sigrng in
                         let uu___2844_20041 = se in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___2844_20041.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___2844_20041.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___2844_20041.FStar_Syntax_Syntax.sigattrs);
                           FStar_Syntax_Syntax.sigopts =
                             (uu___2844_20041.FStar_Syntax_Syntax.sigopts)
                         }
                     | uu____20042 -> failwith "Impossible" in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1 in
                   (env1, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t))::[] ->
              let uu____20056 = typars_of_binders env binders in
              (match uu____20056 with
               | (env', typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None ->
                         let uu____20090 =
                           FStar_Util.for_some
                             (fun uu___20_20092 ->
                                match uu___20_20092 with
                                | FStar_Syntax_Syntax.Effect -> true
                                | uu____20093 -> false) quals in
                         if uu____20090
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____20098 = desugar_term env' k in
                         FStar_Pervasives_Native.Some uu____20098 in
                   let t0 = t in
                   let quals1 =
                     let uu____20103 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___21_20107 ->
                               match uu___21_20107 with
                               | FStar_Syntax_Syntax.Logic -> true
                               | uu____20108 -> false)) in
                     if uu____20103
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals in
                   let qlid = FStar_Syntax_DsEnv.qualify env id in
                   let se =
                     let uu____20117 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect) in
                     if uu____20117
                     then
                       let uu____20120 =
                         let uu____20127 =
                           let uu____20128 = unparen t in
                           uu____20128.FStar_Parser_AST.tm in
                         match uu____20127 with
                         | FStar_Parser_AST.Construct (head, args) ->
                             let uu____20149 =
                               match FStar_List.rev args with
                               | (last_arg, uu____20179)::args_rev ->
                                   let uu____20191 =
                                     let uu____20192 = unparen last_arg in
                                     uu____20192.FStar_Parser_AST.tm in
                                   (match uu____20191 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____20220 -> ([], args))
                               | uu____20229 -> ([], args) in
                             (match uu____20149 with
                              | (cattributes, args1) ->
                                  let uu____20268 =
                                    desugar_attributes env cattributes in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____20268))
                         | uu____20279 -> (t, []) in
                       match uu____20120 with
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
                                  (fun uu___22_20301 ->
                                     match uu___22_20301 with
                                     | FStar_Syntax_Syntax.Effect -> false
                                     | uu____20302 -> true)) in
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
          | (FStar_Parser_AST.TyconRecord uu____20308)::[] ->
              let trec = FStar_List.hd tcs in
              let uu____20328 = tycon_record_as_variant trec in
              (match uu____20328 with
               | (t, fs) ->
                   let uu____20345 =
                     let uu____20348 =
                       let uu____20349 =
                         let uu____20358 =
                           let uu____20361 =
                             FStar_Syntax_DsEnv.current_module env in
                           FStar_Ident.ids_of_lid uu____20361 in
                         (uu____20358, fs) in
                       FStar_Syntax_Syntax.RecordType uu____20349 in
                     uu____20348 :: quals in
                   desugar_tycon env d uu____20345 [t])
          | uu____20366::uu____20367 ->
              let env0 = env in
              let mutuals =
                FStar_List.map
                  (fun x ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs in
              let rec collect_tcs quals1 et tc =
                let uu____20522 = et in
                match uu____20522 with
                | (env1, tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____20727 ->
                         let trec = tc in
                         let uu____20747 = tycon_record_as_variant trec in
                         (match uu____20747 with
                          | (t, fs) ->
                              let uu____20802 =
                                let uu____20805 =
                                  let uu____20806 =
                                    let uu____20815 =
                                      let uu____20818 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1 in
                                      FStar_Ident.ids_of_lid uu____20818 in
                                    (uu____20815, fs) in
                                  FStar_Syntax_Syntax.RecordType uu____20806 in
                                uu____20805 :: quals1 in
                              collect_tcs uu____20802 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id, binders, kopt, constructors) ->
                         let uu____20893 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt)) in
                         (match uu____20893 with
                          | (env2, uu____20949, se, tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t) ->
                         let uu____21082 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt)) in
                         (match uu____21082 with
                          | (env2, uu____21138, se, tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____21251 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng) in
              let uu____21294 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs in
              (match uu____21294 with
               | (env1, tcs1) ->
                   let tcs2 = FStar_List.rev tcs1 in
                   let tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___24_21736 ->
                             match uu___24_21736 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id, uvs, tpars, k, uu____21789,
                                       uu____21790);
                                    FStar_Syntax_Syntax.sigrng = uu____21791;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____21792;
                                    FStar_Syntax_Syntax.sigmeta = uu____21793;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____21794;
                                    FStar_Syntax_Syntax.sigopts = uu____21795;_},
                                  binders, t, quals1)
                                 ->
                                 let t1 =
                                   let uu____21856 =
                                     typars_of_binders env1 binders in
                                   match uu____21856 with
                                   | (env2, tpars1) ->
                                       let uu____21883 =
                                         push_tparams env2 tpars1 in
                                       (match uu____21883 with
                                        | (env_tps, tpars2) ->
                                            let t1 = desugar_typ env_tps t in
                                            let tpars3 =
                                              FStar_Syntax_Subst.close_binders
                                                tpars2 in
                                            FStar_Syntax_Subst.close tpars3
                                              t1) in
                                 let uu____21912 =
                                   let uu____21923 =
                                     mk_typ_abbrev env1 d id uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id] quals1 rng in
                                   ([], uu____21923) in
                                 [uu____21912]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname, univs, tpars, k, mutuals1,
                                       uu____21959);
                                    FStar_Syntax_Syntax.sigrng = uu____21960;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____21962;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____21963;
                                    FStar_Syntax_Syntax.sigopts = uu____21964;_},
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
                                 let uu____22052 = push_tparams env1 tpars in
                                 (match uu____22052 with
                                  | (env_tps, tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____22111 ->
                                             match uu____22111 with
                                             | (x, uu____22123) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps in
                                      let tot_tconstr = mk_tot tconstr in
                                      let attrs =
                                        FStar_List.map (desugar_term env1)
                                          d.FStar_Parser_AST.attrs in
                                      let val_attrs =
                                        let uu____22133 =
                                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                                            env1 tname in
                                        FStar_All.pipe_right uu____22133
                                          FStar_Pervasives_Native.snd in
                                      let uu____22156 =
                                        let uu____22175 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____22250 ->
                                                  match uu____22250 with
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
                                                        let uu____22287 =
                                                          close env_tps t in
                                                        desugar_term env_tps
                                                          uu____22287 in
                                                      let name =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env1 id in
                                                      let quals2 =
                                                        FStar_All.pipe_right
                                                          tname_quals
                                                          (FStar_List.collect
                                                             (fun
                                                                uu___23_22298
                                                                ->
                                                                match uu___23_22298
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____22310
                                                                    -> [])) in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars in
                                                      let uu____22318 =
                                                        let uu____22329 =
                                                          let uu____22330 =
                                                            let uu____22331 =
                                                              let uu____22346
                                                                =
                                                                let uu____22347
                                                                  =
                                                                  let uu____22350
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____22350 in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____22347 in
                                                              (name, univs,
                                                                uu____22346,
                                                                tname, ntps,
                                                                mutuals1) in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____22331 in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____22330;
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
                                                        (tps, uu____22329) in
                                                      (name, uu____22318))) in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____22175 in
                                      (match uu____22156 with
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
                             | uu____22481 -> failwith "impossible")) in
                   let sigelts =
                     FStar_All.pipe_right tps_sigelts
                       (FStar_List.map
                          (fun uu____22560 ->
                             match uu____22560 with | (uu____22571, se) -> se)) in
                   let uu____22585 =
                     let uu____22592 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____22592 rng in
                   (match uu____22585 with
                    | (bundle, abbrevs) ->
                        let env2 = FStar_Syntax_DsEnv.push_sigelt env0 bundle in
                        let env3 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env2 abbrevs in
                        let data_ops =
                          FStar_All.pipe_right tps_sigelts
                            (FStar_List.collect
                               (fun uu____22637 ->
                                  match uu____22637 with
                                  | (tps, se) ->
                                      mk_data_projector_names quals env3 se)) in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname, uu____22685, tps, k,
                                       uu____22688, constrs)
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
                                      let uu____22707 =
                                        FStar_All.pipe_right constrs
                                          (FStar_List.filter
                                             (fun data_lid ->
                                                let data_quals =
                                                  let data_se =
                                                    let uu____22722 =
                                                      FStar_All.pipe_right
                                                        sigelts
                                                        (FStar_List.find
                                                           (fun se1 ->
                                                              match se1.FStar_Syntax_Syntax.sigel
                                                              with
                                                              | FStar_Syntax_Syntax.Sig_datacon
                                                                  (name,
                                                                   uu____22738,
                                                                   uu____22739,
                                                                   uu____22740,
                                                                   uu____22741,
                                                                   uu____22742)
                                                                  ->
                                                                  FStar_Ident.lid_equals
                                                                    name
                                                                    data_lid
                                                              | uu____22747
                                                                  -> false)) in
                                                    FStar_All.pipe_right
                                                      uu____22722
                                                      FStar_Util.must in
                                                  data_se.FStar_Syntax_Syntax.sigquals in
                                                let uu____22750 =
                                                  FStar_All.pipe_right
                                                    data_quals
                                                    (FStar_List.existsb
                                                       (fun uu___25_22755 ->
                                                          match uu___25_22755
                                                          with
                                                          | FStar_Syntax_Syntax.RecordConstructor
                                                              uu____22756 ->
                                                              true
                                                          | uu____22765 ->
                                                              false)) in
                                                Prims.op_Negation uu____22750)) in
                                      mk_data_discriminators quals2 env3
                                        uu____22707
                                  | uu____22766 -> [])) in
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
      let uu____22801 =
        FStar_List.fold_left
          (fun uu____22836 ->
             fun b ->
               match uu____22836 with
               | (env1, binders1) ->
                   let uu____22880 = desugar_binder env1 b in
                   (match uu____22880 with
                    | (FStar_Pervasives_Native.Some a, k) ->
                        let uu____22903 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k) in
                        (match uu____22903 with
                         | (binder, env2) -> (env2, (binder :: binders1)))
                    | uu____22956 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders in
      match uu____22801 with
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
          let uu____23057 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___26_23062 ->
                    match uu___26_23062 with
                    | FStar_Syntax_Syntax.Reflectable uu____23063 -> true
                    | uu____23064 -> false)) in
          if uu____23057
          then
            let monad_env =
              let uu____23066 = FStar_Ident.ident_of_lid effect_name in
              FStar_Syntax_DsEnv.enter_monad_scope env uu____23066 in
            let reflect_lid =
              let uu____23068 = FStar_Ident.id_of_text "reflect" in
              FStar_All.pipe_right uu____23068
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
        let warn1 uu____23110 =
          if warn
          then
            let uu____23111 =
              let uu____23116 =
                let uu____23117 = FStar_Ident.string_of_lid head in
                FStar_Util.format1
                  "Found ill-applied '%s', argument should be a non-empty list of integer literals"
                  uu____23117 in
              (FStar_Errors.Warning_UnappliedFail, uu____23116) in
            FStar_Errors.log_issue at.FStar_Syntax_Syntax.pos uu____23111
          else () in
        let uu____23119 = FStar_Syntax_Util.head_and_args at in
        match uu____23119 with
        | (hd, args) ->
            let uu____23170 =
              let uu____23171 = FStar_Syntax_Subst.compress hd in
              uu____23171.FStar_Syntax_Syntax.n in
            (match uu____23170 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 FStar_Syntax_Syntax.fv_eq_lid fv head ->
                 (match args with
                  | [] -> ((FStar_Pervasives_Native.Some []), true)
                  | (a1, uu____23206)::[] ->
                      let uu____23231 =
                        let uu____23236 =
                          let uu____23245 =
                            FStar_Syntax_Embeddings.e_list
                              FStar_Syntax_Embeddings.e_int in
                          FStar_Syntax_Embeddings.unembed uu____23245 a1 in
                        uu____23236 true FStar_Syntax_Embeddings.id_norm_cb in
                      (match uu____23231 with
                       | FStar_Pervasives_Native.Some es ->
                           let uu____23265 =
                             let uu____23270 =
                               FStar_List.map FStar_BigInt.to_int_fs es in
                             FStar_Pervasives_Native.Some uu____23270 in
                           (uu____23265, true)
                       | uu____23279 ->
                           (warn1 (); (FStar_Pervasives_Native.None, true)))
                  | uu____23291 ->
                      (warn1 (); (FStar_Pervasives_Native.None, true)))
             | uu____23309 -> (FStar_Pervasives_Native.None, false))
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
      let uu____23398 =
        parse_attr_with_list warn at FStar_Parser_Const.fail_attr in
      match uu____23398 with
      | (res, matched) ->
          if matched
          then rebind res false
          else
            (let uu____23434 =
               parse_attr_with_list warn at FStar_Parser_Const.fail_lax_attr in
             match uu____23434 with | (res1, uu____23452) -> rebind res1 true)
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
        | uu____23698 -> FStar_Pervasives_Native.None in
      FStar_List.fold_right
        (fun at ->
           fun acc ->
             let uu____23746 = get_fail_attr1 warn at in comb uu____23746 acc)
        ats FStar_Pervasives_Native.None
let (lookup_effect_lid :
  FStar_Syntax_DsEnv.env ->
    FStar_Ident.lident -> FStar_Range.range -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env ->
    fun l ->
      fun r ->
        let uu____23776 = FStar_Syntax_DsEnv.try_lookup_effect_defn env l in
        match uu____23776 with
        | FStar_Pervasives_Native.None ->
            let uu____23779 =
              let uu____23784 =
                let uu____23785 =
                  let uu____23786 = FStar_Syntax_Print.lid_to_string l in
                  Prims.op_Hat uu____23786 " not found" in
                Prims.op_Hat "Effect name " uu____23785 in
              (FStar_Errors.Fatal_EffectNotFound, uu____23784) in
            FStar_Errors.raise_error uu____23779 r
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
                    let uu____23935 = desugar_binders monad_env eff_binders in
                    match uu____23935 with
                    | (env1, binders) ->
                        let eff_t = desugar_term env1 eff_typ in
                        let num_indices =
                          let uu____23974 =
                            let uu____23983 =
                              FStar_Syntax_Util.arrow_formals eff_t in
                            FStar_Pervasives_Native.fst uu____23983 in
                          FStar_List.length uu____23974 in
                        (if is_layered && (num_indices <= Prims.int_one)
                         then
                           (let uu____23999 =
                              let uu____24004 =
                                let uu____24005 =
                                  let uu____24006 =
                                    FStar_Ident.string_of_id eff_name in
                                  Prims.op_Hat uu____24006
                                    "is defined as a layered effect but has no indices" in
                                Prims.op_Hat "Effect " uu____24005 in
                              (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                uu____24004) in
                            FStar_Errors.raise_error uu____23999
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
                                (uu____24027, uu____24028,
                                 (FStar_Parser_AST.TyconAbbrev
                                 (name, uu____24030, uu____24031,
                                  uu____24032))::[])
                                -> FStar_Ident.string_of_id name
                            | uu____24043 ->
                                failwith
                                  "Malformed effect member declaration." in
                          let uu____24044 =
                            FStar_List.partition
                              (fun decl ->
                                 let uu____24056 = name_of_eff_decl decl in
                                 FStar_List.mem uu____24056 mandatory_members)
                              eff_decls in
                          match uu____24044 with
                          | (mandatory_members_decls, actions) ->
                              let uu____24073 =
                                FStar_All.pipe_right mandatory_members_decls
                                  (FStar_List.fold_left
                                     (fun uu____24102 ->
                                        fun decl ->
                                          match uu____24102 with
                                          | (env2, out) ->
                                              let uu____24122 =
                                                desugar_decl env2 decl in
                                              (match uu____24122 with
                                               | (env3, ses) ->
                                                   let uu____24135 =
                                                     let uu____24138 =
                                                       FStar_List.hd ses in
                                                     uu____24138 :: out in
                                                   (env3, uu____24135)))
                                     (env1, [])) in
                              (match uu____24073 with
                               | (env2, decls) ->
                                   let binders1 =
                                     FStar_Syntax_Subst.close_binders binders in
                                   let actions1 =
                                     FStar_All.pipe_right actions
                                       (FStar_List.map
                                          (fun d1 ->
                                             match d1.FStar_Parser_AST.d with
                                             | FStar_Parser_AST.Tycon
                                                 (uu____24184, uu____24185,
                                                  (FStar_Parser_AST.TyconAbbrev
                                                  (name, action_params,
                                                   uu____24188,
                                                   {
                                                     FStar_Parser_AST.tm =
                                                       FStar_Parser_AST.Construct
                                                       (uu____24189,
                                                        (def, uu____24191)::
                                                        (cps_type,
                                                         uu____24193)::[]);
                                                     FStar_Parser_AST.range =
                                                       uu____24194;
                                                     FStar_Parser_AST.level =
                                                       uu____24195;_}))::[])
                                                 when
                                                 Prims.op_Negation for_free
                                                 ->
                                                 let uu____24224 =
                                                   desugar_binders env2
                                                     action_params in
                                                 (match uu____24224 with
                                                  | (env3, action_params1) ->
                                                      let action_params2 =
                                                        FStar_Syntax_Subst.close_binders
                                                          action_params1 in
                                                      let uu____24256 =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env3 name in
                                                      let uu____24257 =
                                                        let uu____24258 =
                                                          desugar_term env3
                                                            def in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____24258 in
                                                      let uu____24265 =
                                                        let uu____24266 =
                                                          desugar_typ env3
                                                            cps_type in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____24266 in
                                                      {
                                                        FStar_Syntax_Syntax.action_name
                                                          = uu____24256;
                                                        FStar_Syntax_Syntax.action_unqualified_name
                                                          = name;
                                                        FStar_Syntax_Syntax.action_univs
                                                          = [];
                                                        FStar_Syntax_Syntax.action_params
                                                          = action_params2;
                                                        FStar_Syntax_Syntax.action_defn
                                                          = uu____24257;
                                                        FStar_Syntax_Syntax.action_typ
                                                          = uu____24265
                                                      })
                                             | FStar_Parser_AST.Tycon
                                                 (uu____24273, uu____24274,
                                                  (FStar_Parser_AST.TyconAbbrev
                                                  (name, action_params,
                                                   uu____24277, defn))::[])
                                                 when for_free || is_layered
                                                 ->
                                                 let uu____24289 =
                                                   desugar_binders env2
                                                     action_params in
                                                 (match uu____24289 with
                                                  | (env3, action_params1) ->
                                                      let action_params2 =
                                                        FStar_Syntax_Subst.close_binders
                                                          action_params1 in
                                                      let uu____24321 =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env3 name in
                                                      let uu____24322 =
                                                        let uu____24323 =
                                                          desugar_term env3
                                                            defn in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____24323 in
                                                      {
                                                        FStar_Syntax_Syntax.action_name
                                                          = uu____24321;
                                                        FStar_Syntax_Syntax.action_unqualified_name
                                                          = name;
                                                        FStar_Syntax_Syntax.action_univs
                                                          = [];
                                                        FStar_Syntax_Syntax.action_params
                                                          = action_params2;
                                                        FStar_Syntax_Syntax.action_defn
                                                          = uu____24322;
                                                        FStar_Syntax_Syntax.action_typ
                                                          =
                                                          FStar_Syntax_Syntax.tun
                                                      })
                                             | uu____24330 ->
                                                 FStar_Errors.raise_error
                                                   (FStar_Errors.Fatal_MalformedActionDeclaration,
                                                     "Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples).")
                                                   d1.FStar_Parser_AST.drange)) in
                                   let eff_t1 =
                                     FStar_Syntax_Subst.close binders1 eff_t in
                                   let lookup s =
                                     let l =
                                       let uu____24345 =
                                         FStar_Ident.mk_ident
                                           (s, (d.FStar_Parser_AST.drange)) in
                                       FStar_Syntax_DsEnv.qualify env2
                                         uu____24345 in
                                     let uu____24346 =
                                       let uu____24347 =
                                         FStar_Syntax_DsEnv.fail_or env2
                                           (FStar_Syntax_DsEnv.try_lookup_definition
                                              env2) l in
                                       FStar_All.pipe_left
                                         (FStar_Syntax_Subst.close binders1)
                                         uu____24347 in
                                     ([], uu____24346) in
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
                                       let uu____24368 =
                                         let uu____24369 =
                                           let uu____24372 = lookup "repr" in
                                           FStar_Pervasives_Native.Some
                                             uu____24372 in
                                         let uu____24373 =
                                           let uu____24376 = lookup "return" in
                                           FStar_Pervasives_Native.Some
                                             uu____24376 in
                                         let uu____24377 =
                                           let uu____24380 = lookup "bind" in
                                           FStar_Pervasives_Native.Some
                                             uu____24380 in
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
                                             uu____24369;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____24373;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____24377
                                         } in
                                       FStar_Syntax_Syntax.DM4F_eff
                                         uu____24368
                                     else
                                       if is_layered
                                       then
                                         (let has_subcomp =
                                            FStar_List.existsb
                                              (fun decl ->
                                                 let uu____24386 =
                                                   name_of_eff_decl decl in
                                                 uu____24386 = "subcomp")
                                              eff_decls in
                                          let has_if_then_else =
                                            FStar_List.existsb
                                              (fun decl ->
                                                 let uu____24391 =
                                                   name_of_eff_decl decl in
                                                 uu____24391 = "if_then_else")
                                              eff_decls in
                                          let to_comb uu____24421 =
                                            match uu____24421 with
                                            | (us, t) ->
                                                ((us, t), dummy_tscheme) in
                                          let uu____24468 =
                                            let uu____24469 =
                                              let uu____24474 = lookup "repr" in
                                              FStar_All.pipe_right
                                                uu____24474 to_comb in
                                            let uu____24491 =
                                              let uu____24496 =
                                                lookup "return" in
                                              FStar_All.pipe_right
                                                uu____24496 to_comb in
                                            let uu____24513 =
                                              let uu____24518 = lookup "bind" in
                                              FStar_All.pipe_right
                                                uu____24518 to_comb in
                                            let uu____24535 =
                                              if has_subcomp
                                              then
                                                let uu____24544 =
                                                  lookup "subcomp" in
                                                FStar_All.pipe_right
                                                  uu____24544 to_comb
                                              else
                                                (dummy_tscheme,
                                                  dummy_tscheme) in
                                            let uu____24562 =
                                              if has_if_then_else
                                              then
                                                let uu____24571 =
                                                  lookup "if_then_else" in
                                                FStar_All.pipe_right
                                                  uu____24571 to_comb
                                              else
                                                (dummy_tscheme,
                                                  dummy_tscheme) in
                                            {
                                              FStar_Syntax_Syntax.l_repr =
                                                uu____24469;
                                              FStar_Syntax_Syntax.l_return =
                                                uu____24491;
                                              FStar_Syntax_Syntax.l_bind =
                                                uu____24513;
                                              FStar_Syntax_Syntax.l_subcomp =
                                                uu____24535;
                                              FStar_Syntax_Syntax.l_if_then_else
                                                = uu____24562
                                            } in
                                          FStar_Syntax_Syntax.Layered_eff
                                            uu____24468)
                                       else
                                         (let rr =
                                            FStar_Util.for_some
                                              (fun uu___27_24592 ->
                                                 match uu___27_24592 with
                                                 | FStar_Syntax_Syntax.Reifiable
                                                     -> true
                                                 | FStar_Syntax_Syntax.Reflectable
                                                     uu____24593 -> true
                                                 | uu____24594 -> false)
                                              qualifiers in
                                          let uu____24595 =
                                            let uu____24596 =
                                              lookup "return_wp" in
                                            let uu____24597 =
                                              lookup "bind_wp" in
                                            let uu____24598 =
                                              lookup "stronger" in
                                            let uu____24599 =
                                              lookup "if_then_else" in
                                            let uu____24600 = lookup "ite_wp" in
                                            let uu____24601 =
                                              lookup "close_wp" in
                                            let uu____24602 =
                                              lookup "trivial" in
                                            let uu____24603 =
                                              if rr
                                              then
                                                let uu____24608 =
                                                  lookup "repr" in
                                                FStar_Pervasives_Native.Some
                                                  uu____24608
                                              else
                                                FStar_Pervasives_Native.None in
                                            let uu____24610 =
                                              if rr
                                              then
                                                let uu____24615 =
                                                  lookup "return" in
                                                FStar_Pervasives_Native.Some
                                                  uu____24615
                                              else
                                                FStar_Pervasives_Native.None in
                                            let uu____24617 =
                                              if rr
                                              then
                                                let uu____24622 =
                                                  lookup "bind" in
                                                FStar_Pervasives_Native.Some
                                                  uu____24622
                                              else
                                                FStar_Pervasives_Native.None in
                                            {
                                              FStar_Syntax_Syntax.ret_wp =
                                                uu____24596;
                                              FStar_Syntax_Syntax.bind_wp =
                                                uu____24597;
                                              FStar_Syntax_Syntax.stronger =
                                                uu____24598;
                                              FStar_Syntax_Syntax.if_then_else
                                                = uu____24599;
                                              FStar_Syntax_Syntax.ite_wp =
                                                uu____24600;
                                              FStar_Syntax_Syntax.close_wp =
                                                uu____24601;
                                              FStar_Syntax_Syntax.trivial =
                                                uu____24602;
                                              FStar_Syntax_Syntax.repr =
                                                uu____24603;
                                              FStar_Syntax_Syntax.return_repr
                                                = uu____24610;
                                              FStar_Syntax_Syntax.bind_repr =
                                                uu____24617
                                            } in
                                          FStar_Syntax_Syntax.Primitive_eff
                                            uu____24595) in
                                   let sigel =
                                     let uu____24625 =
                                       let uu____24626 =
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
                                           uu____24626
                                       } in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____24625 in
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
                                               let uu____24643 =
                                                 FStar_Syntax_Util.action_as_lb
                                                   mname a
                                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                                               FStar_Syntax_DsEnv.push_sigelt
                                                 env4 uu____24643) env3) in
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
                let uu____24666 = desugar_binders env1 eff_binders in
                match uu____24666 with
                | (env2, binders) ->
                    let uu____24703 =
                      let uu____24714 = head_and_args defn in
                      match uu____24714 with
                      | (head, args) ->
                          let lid =
                            match head.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____24751 ->
                                let uu____24752 =
                                  let uu____24757 =
                                    let uu____24758 =
                                      let uu____24759 =
                                        FStar_Parser_AST.term_to_string head in
                                      Prims.op_Hat uu____24759 " not found" in
                                    Prims.op_Hat "Effect " uu____24758 in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____24757) in
                                FStar_Errors.raise_error uu____24752
                                  d.FStar_Parser_AST.drange in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid in
                          let uu____24761 =
                            match FStar_List.rev args with
                            | (last_arg, uu____24791)::args_rev ->
                                let uu____24803 =
                                  let uu____24804 = unparen last_arg in
                                  uu____24804.FStar_Parser_AST.tm in
                                (match uu____24803 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____24832 -> ([], args))
                            | uu____24841 -> ([], args) in
                          (match uu____24761 with
                           | (cattributes, args1) ->
                               let uu____24884 = desugar_args env2 args1 in
                               let uu____24885 =
                                 desugar_attributes env2 cattributes in
                               (lid, ed, uu____24884, uu____24885)) in
                    (match uu____24703 with
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
                          (let uu____24921 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit in
                           match uu____24921 with
                           | (ed_binders, uu____24935, ed_binders_opening) ->
                               let sub' shift_n uu____24953 =
                                 match uu____24953 with
                                 | (us, x) ->
                                     let x1 =
                                       let uu____24967 =
                                         FStar_Syntax_Subst.shift_subst
                                           (shift_n + (FStar_List.length us))
                                           ed_binders_opening in
                                       FStar_Syntax_Subst.subst uu____24967 x in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args in
                                     let uu____24971 =
                                       let uu____24972 =
                                         FStar_Syntax_Subst.subst s x1 in
                                       (us, uu____24972) in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____24971 in
                               let sub = sub' Prims.int_zero in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name in
                               let ed1 =
                                 let uu____24992 =
                                   sub ed.FStar_Syntax_Syntax.signature in
                                 let uu____24993 =
                                   FStar_Syntax_Util.apply_eff_combinators
                                     sub ed.FStar_Syntax_Syntax.combinators in
                                 let uu____24994 =
                                   FStar_List.map
                                     (fun action ->
                                        let nparam =
                                          FStar_List.length
                                            action.FStar_Syntax_Syntax.action_params in
                                        let uu____25010 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name in
                                        let uu____25011 =
                                          let uu____25012 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn)) in
                                          FStar_Pervasives_Native.snd
                                            uu____25012 in
                                        let uu____25027 =
                                          let uu____25028 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ)) in
                                          FStar_Pervasives_Native.snd
                                            uu____25028 in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____25010;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____25011;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____25027
                                        }) ed.FStar_Syntax_Syntax.actions in
                                 {
                                   FStar_Syntax_Syntax.mname = mname;
                                   FStar_Syntax_Syntax.cattributes =
                                     cattributes;
                                   FStar_Syntax_Syntax.univs =
                                     (ed.FStar_Syntax_Syntax.univs);
                                   FStar_Syntax_Syntax.binders = binders1;
                                   FStar_Syntax_Syntax.signature =
                                     uu____24992;
                                   FStar_Syntax_Syntax.combinators =
                                     uu____24993;
                                   FStar_Syntax_Syntax.actions = uu____24994;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 } in
                               let se =
                                 let uu____25044 =
                                   let uu____25047 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname) in
                                   FStar_List.map uu____25047 quals in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (FStar_Syntax_Syntax.Sig_new_effect ed1);
                                   FStar_Syntax_Syntax.sigrng =
                                     (d.FStar_Parser_AST.drange);
                                   FStar_Syntax_Syntax.sigquals = uu____25044;
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
                                           let uu____25062 =
                                             FStar_Syntax_Util.action_as_lb
                                               mname a
                                               (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                                           FStar_Syntax_DsEnv.push_sigelt
                                             env4 uu____25062) env3) in
                               let env5 =
                                 let uu____25064 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable) in
                                 if uu____25064
                                 then
                                   let reflect_lid =
                                     let uu____25068 =
                                       FStar_Ident.id_of_text "reflect" in
                                     FStar_All.pipe_right uu____25068
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
             let uu____25099 = get_fail_attr1 false at in
             FStar_Option.isNone uu____25099) ats in
      let env0 =
        let uu____25115 = FStar_Syntax_DsEnv.snapshot env in
        FStar_All.pipe_right uu____25115 FStar_Pervasives_Native.snd in
      let attrs = FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs in
      let uu____25127 =
        let uu____25134 = get_fail_attr false attrs in
        match uu____25134 with
        | FStar_Pervasives_Native.Some (expected_errs, lax) ->
            let d1 =
              let uu___3405_25162 = d in
              {
                FStar_Parser_AST.d = (uu___3405_25162.FStar_Parser_AST.d);
                FStar_Parser_AST.drange =
                  (uu___3405_25162.FStar_Parser_AST.drange);
                FStar_Parser_AST.quals =
                  (uu___3405_25162.FStar_Parser_AST.quals);
                FStar_Parser_AST.attrs = []
              } in
            let uu____25163 =
              FStar_Errors.catch_errors
                (fun uu____25181 ->
                   FStar_Options.with_saved_options
                     (fun uu____25187 -> desugar_decl_noattrs env d1)) in
            (match uu____25163 with
             | (errs, r) ->
                 (match (errs, r) with
                  | ([], FStar_Pervasives_Native.Some (env1, ses)) ->
                      let ses1 =
                        FStar_List.map
                          (fun se ->
                             let uu___3420_25247 = se in
                             let uu____25248 = no_fail_attrs attrs in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (uu___3420_25247.FStar_Syntax_Syntax.sigel);
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___3420_25247.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___3420_25247.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___3420_25247.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs = uu____25248;
                               FStar_Syntax_Syntax.sigopts =
                                 (uu___3420_25247.FStar_Syntax_Syntax.sigopts)
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
                        (let uu____25292 =
                           FStar_Errors.find_multiset_discrepancy
                             expected_errs errnos in
                         match uu____25292 with
                         | FStar_Pervasives_Native.None -> (env0, [])
                         | FStar_Pervasives_Native.Some (e, n1, n2) ->
                             (FStar_List.iter FStar_Errors.print_issue errs1;
                              (let uu____25326 =
                                 let uu____25331 =
                                   let uu____25332 =
                                     FStar_Common.string_of_list
                                       FStar_Util.string_of_int expected_errs in
                                   let uu____25333 =
                                     FStar_Common.string_of_list
                                       FStar_Util.string_of_int errnos in
                                   let uu____25334 =
                                     FStar_Util.string_of_int e in
                                   let uu____25335 =
                                     FStar_Util.string_of_int n2 in
                                   let uu____25336 =
                                     FStar_Util.string_of_int n1 in
                                   FStar_Util.format5
                                     "This top-level definition was expected to raise error codes %s, but it raised %s (at desugaring time). Error #%s was raised %s times, instead of %s."
                                     uu____25332 uu____25333 uu____25334
                                     uu____25335 uu____25336 in
                                 (FStar_Errors.Error_DidNotFail, uu____25331) in
                               FStar_Errors.log_issue
                                 d1.FStar_Parser_AST.drange uu____25326);
                              (env0, [])))))
        | FStar_Pervasives_Native.None -> desugar_decl_noattrs env d in
      match uu____25127 with
      | (env1, sigelts) ->
          let rec val_attrs ses =
            match ses with
            | {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                  uu____25369;
                FStar_Syntax_Syntax.sigrng = uu____25370;
                FStar_Syntax_Syntax.sigquals = uu____25371;
                FStar_Syntax_Syntax.sigmeta = uu____25372;
                FStar_Syntax_Syntax.sigattrs = uu____25373;
                FStar_Syntax_Syntax.sigopts = uu____25374;_}::[] ->
                let uu____25387 =
                  let uu____25390 = FStar_List.hd sigelts in
                  FStar_Syntax_Util.lids_of_sigelt uu____25390 in
                FStar_All.pipe_right uu____25387
                  (FStar_List.collect
                     (fun nm ->
                        let uu____25398 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env0 nm in
                        FStar_Pervasives_Native.snd uu____25398))
            | {
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_inductive_typ uu____25411;
                FStar_Syntax_Syntax.sigrng = uu____25412;
                FStar_Syntax_Syntax.sigquals = uu____25413;
                FStar_Syntax_Syntax.sigmeta = uu____25414;
                FStar_Syntax_Syntax.sigattrs = uu____25415;
                FStar_Syntax_Syntax.sigopts = uu____25416;_}::uu____25417 ->
                let uu____25442 =
                  let uu____25445 = FStar_List.hd sigelts in
                  FStar_Syntax_Util.lids_of_sigelt uu____25445 in
                FStar_All.pipe_right uu____25442
                  (FStar_List.collect
                     (fun nm ->
                        let uu____25453 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env0 nm in
                        FStar_Pervasives_Native.snd uu____25453))
            | {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_fail
                  (_errs, _lax, ses1);
                FStar_Syntax_Syntax.sigrng = uu____25469;
                FStar_Syntax_Syntax.sigquals = uu____25470;
                FStar_Syntax_Syntax.sigmeta = uu____25471;
                FStar_Syntax_Syntax.sigattrs = uu____25472;
                FStar_Syntax_Syntax.sigopts = uu____25473;_}::[] ->
                FStar_List.collect (fun se -> val_attrs [se]) ses1
            | uu____25490 -> [] in
          let attrs1 =
            let uu____25496 = val_attrs sigelts in
            FStar_List.append attrs uu____25496 in
          let uu____25499 =
            FStar_List.map
              (fun sigelt ->
                 let uu___3480_25503 = sigelt in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___3480_25503.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___3480_25503.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___3480_25503.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___3480_25503.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs = attrs1;
                   FStar_Syntax_Syntax.sigopts =
                     (uu___3480_25503.FStar_Syntax_Syntax.sigopts)
                 }) sigelts in
          (env1, uu____25499)
and (desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env ->
    fun d ->
      let uu____25510 = desugar_decl_aux env d in
      match uu____25510 with
      | (env1, ses) ->
          let uu____25521 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs) in
          (env1, uu____25521)
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
          let uu____25553 = FStar_Syntax_DsEnv.iface env in
          if uu____25553
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____25563 =
               let uu____25564 =
                 let uu____25565 = FStar_Syntax_DsEnv.dep_graph env in
                 let uu____25566 = FStar_Syntax_DsEnv.current_module env in
                 FStar_Parser_Dep.module_has_interface uu____25565
                   uu____25566 in
               Prims.op_Negation uu____25564 in
             if uu____25563
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____25576 =
                  let uu____25577 =
                    let uu____25578 = FStar_Syntax_DsEnv.dep_graph env in
                    FStar_Parser_Dep.module_has_interface uu____25578 lid in
                  Prims.op_Negation uu____25577 in
                if uu____25576
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____25588 =
                     let uu____25589 =
                       let uu____25590 = FStar_Syntax_DsEnv.dep_graph env in
                       FStar_Parser_Dep.deps_has_implementation uu____25590
                         lid in
                     Prims.op_Negation uu____25589 in
                   if uu____25588
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x, l) ->
          let uu____25604 = FStar_Syntax_DsEnv.push_module_abbrev env x l in
          (uu____25604, [])
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
              | (FStar_Parser_AST.TyconRecord uu____25626)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu____25645 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1 in
          let uu____25651 =
            let uu____25656 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2 in
            desugar_tycon env d uu____25656 tcs in
          (match uu____25651 with
           | (env1, ses) ->
               let mkclass lid =
                 let r = FStar_Ident.range_of_lid lid in
                 let uu____25674 =
                   let uu____25675 =
                     let uu____25682 =
                       let uu____25683 = tun_r r in
                       FStar_Syntax_Syntax.new_bv
                         (FStar_Pervasives_Native.Some r) uu____25683 in
                     FStar_Syntax_Syntax.mk_binder uu____25682 in
                   [uu____25675] in
                 let uu____25696 =
                   let uu____25699 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid in
                   let uu____25702 =
                     let uu____25713 =
                       let uu____25722 =
                         let uu____25723 = FStar_Ident.string_of_lid lid in
                         FStar_Syntax_Util.exp_string uu____25723 in
                       FStar_Syntax_Syntax.as_arg uu____25722 in
                     [uu____25713] in
                   FStar_Syntax_Util.mk_app uu____25699 uu____25702 in
                 FStar_Syntax_Util.abs uu____25674 uu____25696
                   FStar_Pervasives_Native.None in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____25762, id))::uu____25764 ->
                       FStar_Pervasives_Native.Some id
                   | uu____25767::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None in
                 let uu____25771 = get_fname se.FStar_Syntax_Syntax.sigquals in
                 match uu____25771 with
                 | FStar_Pervasives_Native.None -> []
                 | FStar_Pervasives_Native.Some id ->
                     let uu____25777 = FStar_Syntax_DsEnv.qualify env1 id in
                     [uu____25777] in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1, uu____25798) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid, uu____25808, uu____25809, uu____25810,
                      uu____25811, uu____25812)
                     ->
                     let uu____25821 =
                       let uu____25822 =
                         let uu____25823 =
                           let uu____25830 = mkclass lid in
                           (meths, uu____25830) in
                         FStar_Syntax_Syntax.Sig_splice uu____25823 in
                       {
                         FStar_Syntax_Syntax.sigel = uu____25822;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = [];
                         FStar_Syntax_Syntax.sigopts =
                           FStar_Pervasives_Native.None
                       } in
                     [uu____25821]
                 | uu____25833 -> [] in
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
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____25863;
                    FStar_Parser_AST.prange = uu____25864;_},
                  uu____25865)::[] -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____25874;
                    FStar_Parser_AST.prange = uu____25875;_},
                  uu____25876)::[] -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____25891;
                         FStar_Parser_AST.prange = uu____25892;_},
                       uu____25893);
                    FStar_Parser_AST.prange = uu____25894;_},
                  uu____25895)::[] -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____25916;
                         FStar_Parser_AST.prange = uu____25917;_},
                       uu____25918);
                    FStar_Parser_AST.prange = uu____25919;_},
                  uu____25920)::[] -> false
               | (p, uu____25948)::[] ->
                   let uu____25957 = is_app_pattern p in
                   Prims.op_Negation uu____25957
               | uu____25958 -> false) in
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
            let uu____26031 = desugar_term_maybe_top true env as_inner_let in
            (match uu____26031 with
             | (ds_lets, aq) ->
                 (check_no_aq aq;
                  (let uu____26043 =
                     let uu____26044 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets in
                     uu____26044.FStar_Syntax_Syntax.n in
                   match uu____26043 with
                   | FStar_Syntax_Syntax.Tm_let (lbs, uu____26054) ->
                       let fvs =
                         FStar_All.pipe_right
                           (FStar_Pervasives_Native.snd lbs)
                           (FStar_List.map
                              (fun lb ->
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname)) in
                       let uu____26082 =
                         FStar_List.fold_right
                           (fun fv ->
                              fun uu____26107 ->
                                match uu____26107 with
                                | (qs, ats) ->
                                    let uu____26134 =
                                      FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                                        env
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    (match uu____26134 with
                                     | (qs', ats') ->
                                         ((FStar_List.append qs' qs),
                                           (FStar_List.append ats' ats))))
                           fvs ([], []) in
                       (match uu____26082 with
                        | (val_quals, val_attrs) ->
                            let quals1 =
                              match quals with
                              | uu____26188::uu____26189 ->
                                  FStar_List.map
                                    (trans_qual1 FStar_Pervasives_Native.None)
                                    quals
                              | uu____26192 -> val_quals in
                            let quals2 =
                              let uu____26196 =
                                FStar_All.pipe_right lets1
                                  (FStar_Util.for_some
                                     (fun uu____26227 ->
                                        match uu____26227 with
                                        | (uu____26240, (uu____26241, t)) ->
                                            t.FStar_Parser_AST.level =
                                              FStar_Parser_AST.Formula)) in
                              if uu____26196
                              then FStar_Syntax_Syntax.Logic :: quals1
                              else quals1 in
                            let lbs1 =
                              let uu____26259 =
                                FStar_All.pipe_right quals2
                                  (FStar_List.contains
                                     FStar_Syntax_Syntax.Abstract) in
                              if uu____26259
                              then
                                let uu____26262 =
                                  FStar_All.pipe_right
                                    (FStar_Pervasives_Native.snd lbs)
                                    (FStar_List.map
                                       (fun lb ->
                                          let fv =
                                            FStar_Util.right
                                              lb.FStar_Syntax_Syntax.lbname in
                                          let uu___3658_26276 = lb in
                                          {
                                            FStar_Syntax_Syntax.lbname =
                                              (FStar_Util.Inr
                                                 (let uu___3660_26278 = fv in
                                                  {
                                                    FStar_Syntax_Syntax.fv_name
                                                      =
                                                      (uu___3660_26278.FStar_Syntax_Syntax.fv_name);
                                                    FStar_Syntax_Syntax.fv_delta
                                                      =
                                                      (FStar_Syntax_Syntax.Delta_abstract
                                                         (fv.FStar_Syntax_Syntax.fv_delta));
                                                    FStar_Syntax_Syntax.fv_qual
                                                      =
                                                      (uu___3660_26278.FStar_Syntax_Syntax.fv_qual)
                                                  }));
                                            FStar_Syntax_Syntax.lbunivs =
                                              (uu___3658_26276.FStar_Syntax_Syntax.lbunivs);
                                            FStar_Syntax_Syntax.lbtyp =
                                              (uu___3658_26276.FStar_Syntax_Syntax.lbtyp);
                                            FStar_Syntax_Syntax.lbeff =
                                              (uu___3658_26276.FStar_Syntax_Syntax.lbeff);
                                            FStar_Syntax_Syntax.lbdef =
                                              (uu___3658_26276.FStar_Syntax_Syntax.lbdef);
                                            FStar_Syntax_Syntax.lbattrs =
                                              (uu___3658_26276.FStar_Syntax_Syntax.lbattrs);
                                            FStar_Syntax_Syntax.lbpos =
                                              (uu___3658_26276.FStar_Syntax_Syntax.lbpos)
                                          })) in
                                ((FStar_Pervasives_Native.fst lbs),
                                  uu____26262)
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
                   | uu____26300 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____26306 =
               match lets with
               | (pat, body)::[] -> (pat, body)
               | uu____26325 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets" in
             match uu____26306 with
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
                       let uu___3683_26361 = pat1 in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___3683_26361.FStar_Parser_AST.prange)
                       }
                   | uu____26368 -> var_pat in
                 let main_let =
                   let quals1 =
                     if
                       FStar_List.mem FStar_Parser_AST.Private
                         d.FStar_Parser_AST.quals
                     then d.FStar_Parser_AST.quals
                     else FStar_Parser_AST.Private ::
                       (d.FStar_Parser_AST.quals) in
                   desugar_decl env
                     (let uu___3689_26377 = d in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___3689_26377.FStar_Parser_AST.drange);
                        FStar_Parser_AST.quals = quals1;
                        FStar_Parser_AST.attrs =
                          (uu___3689_26377.FStar_Parser_AST.attrs)
                      }) in
                 let main =
                   let uu____26393 =
                     let uu____26394 =
                       FStar_Ident.lid_of_ids [fresh_toplevel_name] in
                     FStar_Parser_AST.Var uu____26394 in
                   FStar_Parser_AST.mk_term uu____26393
                     pat.FStar_Parser_AST.prange FStar_Parser_AST.Expr in
                 let build_generic_projection uu____26418 id_opt =
                   match uu____26418 with
                   | (env1, ses) ->
                       let uu____26440 =
                         match id_opt with
                         | FStar_Pervasives_Native.Some id ->
                             let lid = FStar_Ident.lid_of_ids [id] in
                             let branch =
                               let uu____26452 = FStar_Ident.range_of_lid lid in
                               FStar_Parser_AST.mk_term
                                 (FStar_Parser_AST.Var lid) uu____26452
                                 FStar_Parser_AST.Expr in
                             let bv_pat =
                               let uu____26454 = FStar_Ident.range_of_id id in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatVar
                                    (id, FStar_Pervasives_Native.None))
                                 uu____26454 in
                             (bv_pat, branch)
                         | FStar_Pervasives_Native.None ->
                             let id = FStar_Ident.gen FStar_Range.dummyRange in
                             let branch =
                               FStar_Parser_AST.mk_term
                                 (FStar_Parser_AST.Const
                                    FStar_Const.Const_unit)
                                 FStar_Range.dummyRange FStar_Parser_AST.Expr in
                             let bv_pat =
                               let uu____26460 = FStar_Ident.range_of_id id in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatVar
                                    (id, FStar_Pervasives_Native.None))
                                 uu____26460 in
                             let bv_pat1 =
                               let uu____26464 =
                                 let uu____26465 =
                                   let uu____26476 =
                                     let uu____26483 =
                                       let uu____26484 =
                                         FStar_Ident.range_of_id id in
                                       unit_ty uu____26484 in
                                     (uu____26483,
                                       FStar_Pervasives_Native.None) in
                                   (bv_pat, uu____26476) in
                                 FStar_Parser_AST.PatAscribed uu____26465 in
                               let uu____26493 = FStar_Ident.range_of_id id in
                               FStar_Parser_AST.mk_pattern uu____26464
                                 uu____26493 in
                             (bv_pat1, branch) in
                       (match uu____26440 with
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
                              let uu___3713_26547 = id_decl in
                              {
                                FStar_Parser_AST.d =
                                  (uu___3713_26547.FStar_Parser_AST.d);
                                FStar_Parser_AST.drange =
                                  (uu___3713_26547.FStar_Parser_AST.drange);
                                FStar_Parser_AST.quals =
                                  (d.FStar_Parser_AST.quals);
                                FStar_Parser_AST.attrs =
                                  (uu___3713_26547.FStar_Parser_AST.attrs)
                              } in
                            let uu____26548 = desugar_decl env1 id_decl1 in
                            (match uu____26548 with
                             | (env2, ses') ->
                                 (env2, (FStar_List.append ses ses')))) in
                 let build_projection uu____26584 id =
                   match uu____26584 with
                   | (env1, ses) ->
                       build_generic_projection (env1, ses)
                         (FStar_Pervasives_Native.Some id) in
                 let build_coverage_check uu____26623 =
                   match uu____26623 with
                   | (env1, ses) ->
                       build_generic_projection (env1, ses)
                         FStar_Pervasives_Native.None in
                 let bvs =
                   let uu____26647 = gather_pattern_bound_vars pat in
                   FStar_All.pipe_right uu____26647 FStar_Util.set_elements in
                 let uu____26654 =
                   (FStar_List.isEmpty bvs) &&
                     (let uu____26656 = is_var_pattern pat in
                      Prims.op_Negation uu____26656) in
                 if uu____26654
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
            let uu____26676 = close_fun env t in desugar_term env uu____26676 in
          let quals1 =
            let uu____26680 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env) in
            if uu____26680
            then FStar_Parser_AST.Assumption :: quals
            else quals in
          let lid = FStar_Syntax_DsEnv.qualify env id in
          let attrs =
            FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs in
          let se =
            let uu____26689 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1 in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____26689;
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
                let uu____26702 =
                  let uu____26711 = FStar_Syntax_Syntax.null_binder t in
                  [uu____26711] in
                let uu____26730 =
                  let uu____26733 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total
                    uu____26733 in
                FStar_Syntax_Util.arrow uu____26702 uu____26730 in
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
          uu____26792) ->
          failwith
            "Impossible: LayeredEffect (RedefineEffect _) (should not be parseable)"
      | FStar_Parser_AST.SubEffect l ->
          let src_ed =
            lookup_effect_lid env l.FStar_Parser_AST.msource
              d.FStar_Parser_AST.drange in
          let dst_ed =
            lookup_effect_lid env l.FStar_Parser_AST.mdest
              d.FStar_Parser_AST.drange in
          let uu____26808 =
            let uu____26809 =
              (FStar_Syntax_Util.is_layered src_ed) ||
                (FStar_Syntax_Util.is_layered dst_ed) in
            Prims.op_Negation uu____26809 in
          if uu____26808
          then
            let uu____26814 =
              match l.FStar_Parser_AST.lift_op with
              | FStar_Parser_AST.NonReifiableLift t ->
                  let uu____26832 =
                    let uu____26835 =
                      let uu____26836 = desugar_term env t in
                      ([], uu____26836) in
                    FStar_Pervasives_Native.Some uu____26835 in
                  (uu____26832, FStar_Pervasives_Native.None)
              | FStar_Parser_AST.ReifiableLift (wp, t) ->
                  let uu____26849 =
                    let uu____26852 =
                      let uu____26853 = desugar_term env wp in
                      ([], uu____26853) in
                    FStar_Pervasives_Native.Some uu____26852 in
                  let uu____26860 =
                    let uu____26863 =
                      let uu____26864 = desugar_term env t in
                      ([], uu____26864) in
                    FStar_Pervasives_Native.Some uu____26863 in
                  (uu____26849, uu____26860)
              | FStar_Parser_AST.LiftForFree t ->
                  let uu____26876 =
                    let uu____26879 =
                      let uu____26880 = desugar_term env t in
                      ([], uu____26880) in
                    FStar_Pervasives_Native.Some uu____26879 in
                  (FStar_Pervasives_Native.None, uu____26876) in
            (match uu____26814 with
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
                   let uu____26913 =
                     let uu____26916 =
                       let uu____26917 = desugar_term env t in
                       ([], uu____26917) in
                     FStar_Pervasives_Native.Some uu____26916 in
                   {
                     FStar_Syntax_Syntax.source =
                       (src_ed.FStar_Syntax_Syntax.mname);
                     FStar_Syntax_Syntax.target =
                       (dst_ed.FStar_Syntax_Syntax.mname);
                     FStar_Syntax_Syntax.lift_wp =
                       FStar_Pervasives_Native.None;
                     FStar_Syntax_Syntax.lift = uu____26913
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
             | uu____26924 ->
                 failwith
                   "Impossible! unexpected lift_op for lift to a layered effect")
      | FStar_Parser_AST.Polymonadic_bind (m_eff, n_eff, p_eff, bind) ->
          let m = lookup_effect_lid env m_eff d.FStar_Parser_AST.drange in
          let n = lookup_effect_lid env n_eff d.FStar_Parser_AST.drange in
          let p = lookup_effect_lid env p_eff d.FStar_Parser_AST.drange in
          let uu____26936 =
            let uu____26937 =
              let uu____26938 =
                let uu____26939 =
                  let uu____26950 =
                    let uu____26951 = desugar_term env bind in
                    ([], uu____26951) in
                  ((m.FStar_Syntax_Syntax.mname),
                    (n.FStar_Syntax_Syntax.mname),
                    (p.FStar_Syntax_Syntax.mname), uu____26950,
                    ([], FStar_Syntax_Syntax.tun)) in
                FStar_Syntax_Syntax.Sig_polymonadic_bind uu____26939 in
              {
                FStar_Syntax_Syntax.sigel = uu____26938;
                FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta;
                FStar_Syntax_Syntax.sigattrs = [];
                FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
              } in
            [uu____26937] in
          (env, uu____26936)
      | FStar_Parser_AST.Polymonadic_subcomp (m_eff, n_eff, subcomp) ->
          let m = lookup_effect_lid env m_eff d.FStar_Parser_AST.drange in
          let n = lookup_effect_lid env n_eff d.FStar_Parser_AST.drange in
          let uu____26967 =
            let uu____26968 =
              let uu____26969 =
                let uu____26970 =
                  let uu____26979 =
                    let uu____26980 = desugar_term env subcomp in
                    ([], uu____26980) in
                  ((m.FStar_Syntax_Syntax.mname),
                    (n.FStar_Syntax_Syntax.mname), uu____26979,
                    ([], FStar_Syntax_Syntax.tun)) in
                FStar_Syntax_Syntax.Sig_polymonadic_subcomp uu____26970 in
              {
                FStar_Syntax_Syntax.sigel = uu____26969;
                FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta;
                FStar_Syntax_Syntax.sigattrs = [];
                FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
              } in
            [uu____26968] in
          (env, uu____26967)
      | FStar_Parser_AST.Splice (ids, t) ->
          let t1 = desugar_term env t in
          let se =
            let uu____26999 =
              let uu____27000 =
                let uu____27007 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids in
                (uu____27007, t1) in
              FStar_Syntax_Syntax.Sig_splice uu____27000 in
            {
              FStar_Syntax_Syntax.sigel = uu____26999;
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
      let uu____27033 =
        FStar_List.fold_left
          (fun uu____27053 ->
             fun d ->
               match uu____27053 with
               | (env1, sigelts) ->
                   let uu____27073 = desugar_decl env1 d in
                   (match uu____27073 with
                    | (env2, se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls in
      match uu____27033 with | (env1, sigelts) -> (env1, sigelts)
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
          | (FStar_Pervasives_Native.None, uu____27160) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____27164;
               FStar_Syntax_Syntax.exports = uu____27165;
               FStar_Syntax_Syntax.is_interface = uu____27166;_},
             FStar_Parser_AST.Module (current_lid, uu____27168)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod, uu____27176) ->
              let uu____27179 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod in
              FStar_Pervasives_Native.fst uu____27179 in
        let uu____27184 =
          match m with
          | FStar_Parser_AST.Interface (mname, decls, admitted) ->
              let uu____27220 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii in
              (uu____27220, mname, decls, true)
          | FStar_Parser_AST.Module (mname, decls) ->
              let uu____27237 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii in
              (uu____27237, mname, decls, false) in
        match uu____27184 with
        | ((env2, pop_when_done), mname, decls, intf) ->
            let uu____27267 = desugar_decls env2 decls in
            (match uu____27267 with
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
          let uu____27329 =
            (FStar_Options.interactive ()) &&
              (let uu____27331 =
                 let uu____27332 =
                   let uu____27333 = FStar_Options.file_list () in
                   FStar_List.hd uu____27333 in
                 FStar_Util.get_file_extension uu____27332 in
               FStar_List.mem uu____27331 ["fsti"; "fsi"]) in
          if uu____27329 then as_interface m else m in
        let uu____27337 = desugar_modul_common curmod env m1 in
        match uu____27337 with
        | (env1, modul, pop_when_done) ->
            if pop_when_done
            then
              let uu____27355 = FStar_Syntax_DsEnv.pop () in
              (uu____27355, modul)
            else (env1, modul)
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun env ->
    fun m ->
      let uu____27375 =
        desugar_modul_common FStar_Pervasives_Native.None env m in
      match uu____27375 with
      | (env1, modul, pop_when_done) ->
          let uu____27389 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul in
          (match uu____27389 with
           | (env2, modul1) ->
               ((let uu____27401 =
                   let uu____27402 =
                     FStar_Ident.string_of_lid
                       modul1.FStar_Syntax_Syntax.name in
                   FStar_Options.dump_module uu____27402 in
                 if uu____27401
                 then
                   let uu____27403 =
                     FStar_Syntax_Print.modul_to_string modul1 in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____27403
                 else ());
                (let uu____27405 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2 in
                 (uu____27405, modul1))))
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
        (fun uu____27448 ->
           let uu____27449 = desugar_modul env modul in
           match uu____27449 with | (e, m) -> (m, e))
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls ->
    fun env ->
      with_options
        (fun uu____27486 ->
           let uu____27487 = desugar_decls env decls in
           match uu____27487 with | (env1, sigelts) -> (sigelts, env1))
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul ->
    fun a_modul ->
      fun env ->
        with_options
          (fun uu____27537 ->
             let uu____27538 = desugar_partial_modul modul env a_modul in
             match uu____27538 with | (env1, modul1) -> (modul1, env1))
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
              | uu____27632 ->
                  let t =
                    let uu____27642 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Range.dummyRange in
                    erase_univs uu____27642 in
                  let uu____27655 =
                    let uu____27656 = FStar_Syntax_Subst.compress t in
                    uu____27656.FStar_Syntax_Syntax.n in
                  (match uu____27655 with
                   | FStar_Syntax_Syntax.Tm_abs
                       (bs1, uu____27668, uu____27669) -> bs1
                   | uu____27694 -> failwith "Impossible") in
            let uu____27703 =
              let uu____27710 = erase_binders ed.FStar_Syntax_Syntax.binders in
              FStar_Syntax_Subst.open_term' uu____27710
                FStar_Syntax_Syntax.t_unit in
            match uu____27703 with
            | (binders, uu____27712, binders_opening) ->
                let erase_term t =
                  let uu____27720 =
                    let uu____27721 =
                      FStar_Syntax_Subst.subst binders_opening t in
                    erase_univs uu____27721 in
                  FStar_Syntax_Subst.close binders uu____27720 in
                let erase_tscheme uu____27739 =
                  match uu____27739 with
                  | (us, t) ->
                      let t1 =
                        let uu____27759 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening in
                        FStar_Syntax_Subst.subst uu____27759 t in
                      let uu____27762 =
                        let uu____27763 = erase_univs t1 in
                        FStar_Syntax_Subst.close binders uu____27763 in
                      ([], uu____27762) in
                let erase_action action =
                  let opening =
                    FStar_Syntax_Subst.shift_subst
                      (FStar_List.length
                         action.FStar_Syntax_Syntax.action_univs)
                      binders_opening in
                  let erased_action_params =
                    match action.FStar_Syntax_Syntax.action_params with
                    | [] -> []
                    | uu____27786 ->
                        let bs =
                          let uu____27796 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params in
                          FStar_All.pipe_left erase_binders uu____27796 in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Range.dummyRange in
                        let uu____27836 =
                          let uu____27837 =
                            let uu____27840 =
                              FStar_Syntax_Subst.close binders t in
                            FStar_Syntax_Subst.compress uu____27840 in
                          uu____27837.FStar_Syntax_Syntax.n in
                        (match uu____27836 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1, uu____27842, uu____27843) -> bs1
                         | uu____27868 -> failwith "Impossible") in
                  let erase_term1 t =
                    let uu____27875 =
                      let uu____27876 = FStar_Syntax_Subst.subst opening t in
                      erase_univs uu____27876 in
                    FStar_Syntax_Subst.close binders uu____27875 in
                  let uu___3991_27877 = action in
                  let uu____27878 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn in
                  let uu____27879 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___3991_27877.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___3991_27877.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____27878;
                    FStar_Syntax_Syntax.action_typ = uu____27879
                  } in
                let uu___3993_27880 = ed in
                let uu____27881 = FStar_Syntax_Subst.close_binders binders in
                let uu____27882 =
                  erase_tscheme ed.FStar_Syntax_Syntax.signature in
                let uu____27883 =
                  FStar_Syntax_Util.apply_eff_combinators erase_tscheme
                    ed.FStar_Syntax_Syntax.combinators in
                let uu____27884 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions in
                {
                  FStar_Syntax_Syntax.mname =
                    (uu___3993_27880.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.cattributes =
                    (uu___3993_27880.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____27881;
                  FStar_Syntax_Syntax.signature = uu____27882;
                  FStar_Syntax_Syntax.combinators = uu____27883;
                  FStar_Syntax_Syntax.actions = uu____27884;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___3993_27880.FStar_Syntax_Syntax.eff_attrs)
                } in
          let push_sigelt env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___4000_27900 = se in
                  let uu____27901 =
                    let uu____27902 = erase_univs_ed ed in
                    FStar_Syntax_Syntax.Sig_new_effect uu____27902 in
                  {
                    FStar_Syntax_Syntax.sigel = uu____27901;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___4000_27900.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___4000_27900.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___4000_27900.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___4000_27900.FStar_Syntax_Syntax.sigattrs);
                    FStar_Syntax_Syntax.sigopts =
                      (uu___4000_27900.FStar_Syntax_Syntax.sigopts)
                  } in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se' in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____27904 -> FStar_Syntax_DsEnv.push_sigelt env se in
          let uu____27905 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii in
          match uu____27905 with
          | (en1, pop_when_done) ->
              let en2 =
                let uu____27917 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name in
                FStar_List.fold_left push_sigelt uu____27917
                  m.FStar_Syntax_Syntax.exports in
              let env = FStar_Syntax_DsEnv.finish en2 m in
              let uu____27919 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env in
              ((), uu____27919)