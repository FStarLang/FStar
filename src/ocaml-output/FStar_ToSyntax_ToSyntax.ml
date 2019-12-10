open Prims
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
      fun branch1 ->
        FStar_All.pipe_right annotated_pats
          (FStar_List.map
             (fun uu____103 ->
                match uu____103 with
                | (pat, annots) ->
                    let branch2 =
                      FStar_List.fold_left
                        (fun br ->
                           fun uu____158 ->
                             match uu____158 with
                             | (bv, ty) ->
                                 let lb =
                                   let uu____176 =
                                     FStar_Syntax_Syntax.bv_to_name bv in
                                   FStar_Syntax_Util.mk_letbinding
                                     (FStar_Util.Inl bv) [] ty
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____176 [] br.FStar_Syntax_Syntax.pos in
                                 let branch2 =
                                   let uu____182 =
                                     let uu____183 =
                                       FStar_Syntax_Syntax.mk_binder bv in
                                     [uu____183] in
                                   FStar_Syntax_Subst.close uu____182 branch1 in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((false, [lb]), branch2))
                                   FStar_Pervasives_Native.None
                                   br.FStar_Syntax_Syntax.pos) branch1 annots in
                    FStar_Syntax_Util.branch (pat, when_opt, branch2)))
let (trans_qual :
  FStar_Range.range ->
    FStar_Ident.lident FStar_Pervasives_Native.option ->
      FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier)
  =
  fun r ->
    fun maybe_effect_id ->
      fun uu___0_240 ->
        match uu___0_240 with
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
  fun uu___1_260 ->
    match uu___1_260 with
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
  fun uu___2_278 ->
    match uu___2_278 with
    | FStar_Parser_AST.Hash ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | uu____281 -> FStar_Pervasives_Native.None
let arg_withimp_e :
  'Auu____289 .
    FStar_Parser_AST.imp ->
      'Auu____289 ->
        ('Auu____289 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  = fun imp -> fun t -> (t, (as_imp imp))
let arg_withimp_t :
  'Auu____315 .
    FStar_Parser_AST.imp ->
      'Auu____315 ->
        ('Auu____315 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  =
  fun imp ->
    fun t ->
      match imp with
      | FStar_Parser_AST.Hash ->
          (t, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag))
      | uu____334 -> (t, FStar_Pervasives_Native.None)
let (contains_binder : FStar_Parser_AST.binder Prims.list -> Prims.bool) =
  fun binders ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____355 -> true
            | uu____361 -> false))
let rec (unparen : FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun t ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____370 -> t
let (tm_type_z : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r ->
    let uu____377 =
      let uu____378 = FStar_Ident.lid_of_path ["Type0"] r in
      FStar_Parser_AST.Name uu____378 in
    FStar_Parser_AST.mk_term uu____377 r FStar_Parser_AST.Kind
let (tm_type : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r ->
    let uu____388 =
      let uu____389 = FStar_Ident.lid_of_path ["Type"] r in
      FStar_Parser_AST.Name uu____389 in
    FStar_Parser_AST.mk_term uu____388 r FStar_Parser_AST.Kind
let rec (is_comp_type :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun env ->
    fun t ->
      let uu____405 =
        let uu____406 = unparen t in uu____406.FStar_Parser_AST.tm in
      match uu____405 with
      | FStar_Parser_AST.Name l ->
          let uu____409 = FStar_Syntax_DsEnv.try_lookup_effect_name env l in
          FStar_All.pipe_right uu____409 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l, uu____416) ->
          let uu____429 = FStar_Syntax_DsEnv.try_lookup_effect_name env l in
          FStar_All.pipe_right uu____429 FStar_Option.isSome
      | FStar_Parser_AST.App (head1, uu____436, uu____437) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1, uu____442, uu____443) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____448, t1) -> is_comp_type env t1
      | uu____450 -> false
let (unit_ty : FStar_Parser_AST.term) =
  FStar_Parser_AST.mk_term
    (FStar_Parser_AST.Name FStar_Parser_Const.unit_lid)
    FStar_Range.dummyRange FStar_Parser_AST.Type_level
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
              let warn_if_deprecated attrs1 =
                FStar_List.iter
                  (fun a ->
                     match a.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_fvar fv;
                            FStar_Syntax_Syntax.pos = uu____551;
                            FStar_Syntax_Syntax.vars = uu____552;_},
                          args)
                         when
                         FStar_Ident.lid_equals
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           FStar_Parser_Const.deprecated_attr
                         ->
                         let msg =
                           let uu____580 =
                             FStar_Syntax_Print.term_to_string tm in
                           Prims.op_Hat uu____580 " is deprecated" in
                         let msg1 =
                           if (FStar_List.length args) > Prims.int_zero
                           then
                             let uu____596 =
                               let uu____597 =
                                 let uu____600 = FStar_List.hd args in
                                 FStar_Pervasives_Native.fst uu____600 in
                               uu____597.FStar_Syntax_Syntax.n in
                             match uu____596 with
                             | FStar_Syntax_Syntax.Tm_constant
                                 (FStar_Const.Const_string (s, uu____623))
                                 when
                                 Prims.op_Negation
                                   ((FStar_Util.trim_string s) = "")
                                 ->
                                 Prims.op_Hat msg
                                   (Prims.op_Hat ", use "
                                      (Prims.op_Hat s " instead"))
                             | uu____630 -> msg
                           else msg in
                         let uu____633 = FStar_Ident.range_of_lid l in
                         FStar_Errors.log_issue uu____633
                           (FStar_Errors.Warning_DeprecatedDefinition, msg1)
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Ident.lid_equals
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           FStar_Parser_Const.deprecated_attr
                         ->
                         let msg =
                           let uu____638 =
                             FStar_Syntax_Print.term_to_string tm in
                           Prims.op_Hat uu____638 " is deprecated" in
                         let uu____641 = FStar_Ident.range_of_lid l in
                         FStar_Errors.log_issue uu____641
                           (FStar_Errors.Warning_DeprecatedDefinition, msg)
                     | uu____643 -> ()) attrs1 in
              (warn_if_deprecated attrs;
               (let tm1 = setpos tm in FStar_Pervasives_Native.Some tm1))
let desugar_name :
  'Auu____659 .
    'Auu____659 ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        env_t -> Prims.bool -> FStar_Ident.lident -> FStar_Syntax_Syntax.term
  =
  fun mk1 ->
    fun setpos ->
      fun env ->
        fun resolve ->
          fun l ->
            FStar_Syntax_DsEnv.fail_or env (desugar_name' setpos env resolve)
              l
let (compile_op_lid :
  Prims.int -> Prims.string -> FStar_Range.range -> FStar_Ident.lident) =
  fun n1 ->
    fun s ->
      fun r ->
        let uu____712 =
          let uu____715 =
            let uu____716 =
              let uu____722 = FStar_Parser_AST.compile_op n1 s r in
              (uu____722, r) in
            FStar_Ident.mk_ident uu____716 in
          [uu____715] in
        FStar_All.pipe_right uu____712 FStar_Ident.lid_of_ids
let op_as_term :
  'Auu____738 .
    env_t ->
      Prims.int ->
        'Auu____738 ->
          FStar_Ident.ident ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env ->
    fun arity ->
      fun rng ->
        fun op ->
          let r l dd =
            let uu____776 =
              let uu____777 =
                let uu____778 =
                  FStar_Ident.set_lid_range l op.FStar_Ident.idRange in
                FStar_Syntax_Syntax.lid_as_fv uu____778 dd
                  FStar_Pervasives_Native.None in
              FStar_All.pipe_right uu____777 FStar_Syntax_Syntax.fv_to_tm in
            FStar_Pervasives_Native.Some uu____776 in
          let fallback uu____786 =
            let uu____787 = FStar_Ident.text_of_id op in
            match uu____787 with
            | "=" ->
                r FStar_Parser_Const.op_Eq
                  FStar_Syntax_Syntax.delta_equational
            | ":=" ->
                r FStar_Parser_Const.write_lid
                  FStar_Syntax_Syntax.delta_equational
            | "<" ->
                r FStar_Parser_Const.op_LT
                  FStar_Syntax_Syntax.delta_equational
            | "<=" ->
                r FStar_Parser_Const.op_LTE
                  FStar_Syntax_Syntax.delta_equational
            | ">" ->
                r FStar_Parser_Const.op_GT
                  FStar_Syntax_Syntax.delta_equational
            | ">=" ->
                r FStar_Parser_Const.op_GTE
                  FStar_Syntax_Syntax.delta_equational
            | "&&" ->
                r FStar_Parser_Const.op_And
                  FStar_Syntax_Syntax.delta_equational
            | "||" ->
                r FStar_Parser_Const.op_Or
                  FStar_Syntax_Syntax.delta_equational
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
                let uu____808 = FStar_Options.ml_ish () in
                if uu____808
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
            | uu____833 -> FStar_Pervasives_Native.None in
          let uu____835 =
            let uu____838 =
              compile_op_lid arity op.FStar_Ident.idText
                op.FStar_Ident.idRange in
            desugar_name'
              (fun t ->
                 let uu___203_844 = t in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___203_844.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = (op.FStar_Ident.idRange);
                   FStar_Syntax_Syntax.vars =
                     (uu___203_844.FStar_Syntax_Syntax.vars)
                 }) env true uu____838 in
          match uu____835 with
          | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
          | uu____849 -> fallback ()
let (sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list)
  =
  fun ftv ->
    let uu____864 =
      FStar_Util.remove_dups
        (fun x -> fun y -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x ->
            fun y ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____864
let rec (free_type_vars_b :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Syntax_DsEnv.env * FStar_Ident.ident Prims.list))
  =
  fun env ->
    fun binder ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____913 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____917 = FStar_Syntax_DsEnv.push_bv env x in
          (match uu____917 with | (env1, uu____929) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____932, term) ->
          let uu____934 = free_type_vars env term in (env, uu____934)
      | FStar_Parser_AST.TAnnotated (id1, uu____940) ->
          let uu____941 = FStar_Syntax_DsEnv.push_bv env id1 in
          (match uu____941 with | (env1, uu____953) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____957 = free_type_vars env t in (env, uu____957)
and (free_type_vars :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list)
  =
  fun env ->
    fun t ->
      let uu____964 =
        let uu____965 = unparen t in uu____965.FStar_Parser_AST.tm in
      match uu____964 with
      | FStar_Parser_AST.Labeled uu____968 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____981 = FStar_Syntax_DsEnv.try_lookup_id env a in
          (match uu____981 with
           | FStar_Pervasives_Native.None -> [a]
           | uu____986 -> [])
      | FStar_Parser_AST.Wild -> []
      | FStar_Parser_AST.Const uu____989 -> []
      | FStar_Parser_AST.Uvar uu____990 -> []
      | FStar_Parser_AST.Var uu____991 -> []
      | FStar_Parser_AST.Projector uu____992 -> []
      | FStar_Parser_AST.Discrim uu____997 -> []
      | FStar_Parser_AST.Name uu____998 -> []
      | FStar_Parser_AST.Requires (t1, uu____1000) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1, uu____1008) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____1015, t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1, t', tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None -> []
             | FStar_Pervasives_Native.Some t2 -> [t2]) in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____1034, ts) ->
          FStar_List.collect
            (fun uu____1055 ->
               match uu____1055 with
               | (t1, uu____1063) -> free_type_vars env t1) ts
      | FStar_Parser_AST.Op (uu____1064, ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1, t2, uu____1072) ->
          let uu____1073 = free_type_vars env t1 in
          let uu____1076 = free_type_vars env t2 in
          FStar_List.append uu____1073 uu____1076
      | FStar_Parser_AST.Refine (b, t1) ->
          let uu____1081 = free_type_vars_b env b in
          (match uu____1081 with
           | (env1, f) ->
               let uu____1096 = free_type_vars env1 t1 in
               FStar_List.append f uu____1096)
      | FStar_Parser_AST.Sum (binders, body) ->
          let uu____1113 =
            FStar_List.fold_left
              (fun uu____1137 ->
                 fun bt ->
                   match uu____1137 with
                   | (env1, free) ->
                       let uu____1161 =
                         match bt with
                         | FStar_Util.Inl binder ->
                             free_type_vars_b env1 binder
                         | FStar_Util.Inr t1 ->
                             let uu____1176 = free_type_vars env1 body in
                             (env1, uu____1176) in
                       (match uu____1161 with
                        | (env2, f) -> (env2, (FStar_List.append f free))))
              (env, []) binders in
          (match uu____1113 with
           | (env1, free) ->
               let uu____1205 = free_type_vars env1 body in
               FStar_List.append free uu____1205)
      | FStar_Parser_AST.Product (binders, body) ->
          let uu____1214 =
            FStar_List.fold_left
              (fun uu____1234 ->
                 fun binder ->
                   match uu____1234 with
                   | (env1, free) ->
                       let uu____1254 = free_type_vars_b env1 binder in
                       (match uu____1254 with
                        | (env2, f) -> (env2, (FStar_List.append f free))))
              (env, []) binders in
          (match uu____1214 with
           | (env1, free) ->
               let uu____1285 = free_type_vars env1 body in
               FStar_List.append free uu____1285)
      | FStar_Parser_AST.Project (t1, uu____1289) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.CalcProof (rel, init1, steps) ->
          let uu____1300 = free_type_vars env rel in
          let uu____1303 =
            let uu____1306 = free_type_vars env init1 in
            let uu____1309 =
              FStar_List.collect
                (fun uu____1318 ->
                   match uu____1318 with
                   | FStar_Parser_AST.CalcStep (rel1, just, next) ->
                       let uu____1324 = free_type_vars env rel1 in
                       let uu____1327 =
                         let uu____1330 = free_type_vars env just in
                         let uu____1333 = free_type_vars env next in
                         FStar_List.append uu____1330 uu____1333 in
                       FStar_List.append uu____1324 uu____1327) steps in
            FStar_List.append uu____1306 uu____1309 in
          FStar_List.append uu____1300 uu____1303
      | FStar_Parser_AST.Abs uu____1336 -> []
      | FStar_Parser_AST.Let uu____1343 -> []
      | FStar_Parser_AST.LetOpen uu____1364 -> []
      | FStar_Parser_AST.If uu____1369 -> []
      | FStar_Parser_AST.QForall uu____1376 -> []
      | FStar_Parser_AST.QExists uu____1395 -> []
      | FStar_Parser_AST.Record uu____1414 -> []
      | FStar_Parser_AST.Match uu____1427 -> []
      | FStar_Parser_AST.TryWith uu____1442 -> []
      | FStar_Parser_AST.Bind uu____1457 -> []
      | FStar_Parser_AST.Quote uu____1464 -> []
      | FStar_Parser_AST.VQuote uu____1469 -> []
      | FStar_Parser_AST.Antiquote uu____1470 -> []
      | FStar_Parser_AST.Seq uu____1471 -> []
let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun t ->
    let rec aux args t1 =
      let uu____1525 =
        let uu____1526 = unparen t1 in uu____1526.FStar_Parser_AST.tm in
      match uu____1525 with
      | FStar_Parser_AST.App (t2, arg, imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l, args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____1568 -> (t1, args) in
    aux [] t
let (close :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env ->
    fun t ->
      let ftv =
        let uu____1593 = free_type_vars env t in
        FStar_All.pipe_left sort_ftv uu____1593 in
      if (FStar_List.length ftv) = Prims.int_zero
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x ->
                   let uu____1615 =
                     let uu____1616 =
                       let uu____1621 = tm_type x.FStar_Ident.idRange in
                       (x, uu____1621) in
                     FStar_Parser_AST.TAnnotated uu____1616 in
                   FStar_Parser_AST.mk_binder uu____1615
                     x.FStar_Ident.idRange FStar_Parser_AST.Type_level
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
        let uu____1639 = free_type_vars env t in
        FStar_All.pipe_left sort_ftv uu____1639 in
      if (FStar_List.length ftv) = Prims.int_zero
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x ->
                   let uu____1661 =
                     let uu____1662 =
                       let uu____1667 = tm_type x.FStar_Ident.idRange in
                       (x, uu____1667) in
                     FStar_Parser_AST.TAnnotated uu____1662 in
                   FStar_Parser_AST.mk_binder uu____1661
                     x.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit))) in
         let t1 =
           let uu____1669 =
             let uu____1670 = unparen t in uu____1670.FStar_Parser_AST.tm in
           match uu____1669 with
           | FStar_Parser_AST.Product uu____1671 -> t
           | uu____1678 ->
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
      | uu____1715 -> (bs, t)
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild uu____1726 -> true
    | FStar_Parser_AST.PatTvar (uu____1730, uu____1731) -> true
    | FStar_Parser_AST.PatVar (uu____1737, uu____1738) -> true
    | FStar_Parser_AST.PatAscribed (p1, uu____1745) -> is_var_pattern p1
    | uu____1758 -> false
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1, uu____1769) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____1782;
           FStar_Parser_AST.prange = uu____1783;_},
         uu____1784)
        -> true
    | uu____1796 -> false
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
               (unit_ty, FStar_Pervasives_Native.None)))
          p.FStar_Parser_AST.prange
    | uu____1812 -> p
let rec (destruct_app_pattern :
  FStar_Syntax_DsEnv.env ->
    Prims.bool ->
      FStar_Parser_AST.pattern ->
        ((FStar_Ident.ident, FStar_Ident.lident) FStar_Util.either *
          FStar_Parser_AST.pattern Prims.list * (FStar_Parser_AST.term *
          FStar_Parser_AST.term FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.option))
  =
  fun env ->
    fun is_top_level1 ->
      fun p ->
        match p.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatAscribed (p1, t) ->
            let uu____1885 = destruct_app_pattern env is_top_level1 p1 in
            (match uu____1885 with
             | (name, args, uu____1928) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1, uu____1978);
               FStar_Parser_AST.prange = uu____1979;_},
             args)
            when is_top_level1 ->
            let uu____1989 =
              let uu____1994 = FStar_Syntax_DsEnv.qualify env id1 in
              FStar_Util.Inr uu____1994 in
            (uu____1989, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1, uu____2016);
               FStar_Parser_AST.prange = uu____2017;_},
             args)
            -> ((FStar_Util.Inl id1), args, FStar_Pervasives_Native.None)
        | uu____2047 -> failwith "Not an app pattern"
let rec (gather_pattern_bound_vars_maybe_top :
  Prims.bool ->
    FStar_Ident.ident FStar_Util.set ->
      FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set)
  =
  fun fail_on_patconst ->
    fun acc ->
      fun p ->
        let gather_pattern_bound_vars_from_list =
          FStar_List.fold_left
            (gather_pattern_bound_vars_maybe_top fail_on_patconst) acc in
        match p.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatWild uu____2106 -> acc
        | FStar_Parser_AST.PatName uu____2109 -> acc
        | FStar_Parser_AST.PatOp uu____2110 -> acc
        | FStar_Parser_AST.PatConst uu____2111 ->
            if fail_on_patconst
            then
              FStar_Errors.raise_error
                (FStar_Errors.Error_CannotRedefineConst,
                  "Constants cannot be redefined") p.FStar_Parser_AST.prange
            else acc
        | FStar_Parser_AST.PatApp (phead, pats) ->
            gather_pattern_bound_vars_from_list (phead :: pats)
        | FStar_Parser_AST.PatTvar (x, uu____2128) ->
            FStar_Util.set_add x acc
        | FStar_Parser_AST.PatVar (x, uu____2134) -> FStar_Util.set_add x acc
        | FStar_Parser_AST.PatList pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatTuple (pats, uu____2143) ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatOr pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatRecord guarded_pats ->
            let uu____2160 =
              FStar_List.map FStar_Pervasives_Native.snd guarded_pats in
            gather_pattern_bound_vars_from_list uu____2160
        | FStar_Parser_AST.PatAscribed (pat, uu____2168) ->
            gather_pattern_bound_vars_maybe_top fail_on_patconst acc pat
let (gather_pattern_bound_vars :
  Prims.bool -> FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set)
  =
  fun fail_on_patconst ->
    fun p ->
      let acc =
        FStar_Util.new_set
          (fun id1 ->
             fun id2 ->
               if id1.FStar_Ident.idText = id2.FStar_Ident.idText
               then Prims.int_zero
               else Prims.int_one) in
      gather_pattern_bound_vars_maybe_top fail_on_patconst acc p
type bnd =
  | LocalBinder of (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) 
  | LetBinder of (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)) 
let (uu___is_LocalBinder : bnd -> Prims.bool) =
  fun projectee ->
    match projectee with | LocalBinder _0 -> true | uu____2250 -> false
let (__proj__LocalBinder__item___0 :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun projectee -> match projectee with | LocalBinder _0 -> _0
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee ->
    match projectee with | LetBinder _0 -> true | uu____2291 -> false
let (__proj__LetBinder__item___0 :
  bnd ->
    (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)))
  = fun projectee -> match projectee with | LetBinder _0 -> _0
let (binder_of_bnd :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun uu___3_2339 ->
    match uu___3_2339 with
    | LocalBinder (a, aq) -> (a, aq)
    | uu____2346 -> failwith "Impossible"
let (mk_lb :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list *
    (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Range.range)
    -> FStar_Syntax_Syntax.letbinding)
  =
  fun uu____2379 ->
    match uu____2379 with
    | (attrs, n1, t, e, pos) ->
        {
          FStar_Syntax_Syntax.lbname = n1;
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
      let uu____2461 =
        let uu____2478 =
          let uu____2481 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
          FStar_Syntax_Syntax.fv_to_tm uu____2481 in
        let uu____2482 =
          let uu____2493 =
            let uu____2502 = FStar_Syntax_Syntax.as_implicit false in
            (tm, uu____2502) in
          [uu____2493] in
        (uu____2478, uu____2482) in
      FStar_Syntax_Syntax.Tm_app uu____2461 in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm ->
    let tm' =
      let uu____2551 =
        let uu____2568 =
          let uu____2571 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
          FStar_Syntax_Syntax.fv_to_tm uu____2571 in
        let uu____2572 =
          let uu____2583 =
            let uu____2592 = FStar_Syntax_Syntax.as_implicit false in
            (tm, uu____2592) in
          [uu____2583] in
        (uu____2568, uu____2572) in
      FStar_Syntax_Syntax.Tm_app uu____2551 in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
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
          let uu____2655 =
            let uu____2672 =
              let uu____2675 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Syntax_Syntax.fv_to_tm uu____2675 in
            let uu____2676 =
              let uu____2687 =
                let uu____2696 = FStar_Syntax_Syntax.as_implicit false in
                (t1, uu____2696) in
              let uu____2704 =
                let uu____2715 =
                  let uu____2724 = FStar_Syntax_Syntax.as_implicit false in
                  (t2, uu____2724) in
                [uu____2715] in
              uu____2687 :: uu____2704 in
            (uu____2672, uu____2676) in
          FStar_Syntax_Syntax.Tm_app uu____2655 in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
let (generalize_annotated_univs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun s ->
    let bs_univnames bs =
      let uu____2784 =
        let uu____2799 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name in
        FStar_List.fold_left
          (fun uvs ->
             fun uu____2818 ->
               match uu____2818 with
               | ({ FStar_Syntax_Syntax.ppname = uu____2829;
                    FStar_Syntax_Syntax.index = uu____2830;
                    FStar_Syntax_Syntax.sort = t;_},
                  uu____2832) ->
                   let uu____2840 = FStar_Syntax_Free.univnames t in
                   FStar_Util.set_union uvs uu____2840) uu____2799 in
      FStar_All.pipe_right bs uu____2784 in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____2856 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____2874 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs, lids) ->
        let uvs =
          let uu____2902 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs ->
                    fun se ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____2923, uu____2924, bs, t, uu____2927,
                             uu____2928)
                            ->
                            let uu____2937 = bs_univnames bs in
                            let uu____2940 = FStar_Syntax_Free.univnames t in
                            FStar_Util.set_union uu____2937 uu____2940
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____2943, uu____2944, t, uu____2946,
                             uu____2947, uu____2948)
                            -> FStar_Syntax_Free.univnames t
                        | uu____2955 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt" in
                      FStar_Util.set_union uvs se_univs) empty_set) in
          FStar_All.pipe_right uu____2902 FStar_Util.set_elements in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs in
        let uu___585_2964 = s in
        let uu____2965 =
          let uu____2966 =
            let uu____2975 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid, uu____2993, bs, t, lids1, lids2) ->
                          let uu___596_3006 = se in
                          let uu____3007 =
                            let uu____3008 =
                              let uu____3025 =
                                FStar_Syntax_Subst.subst_binders usubst bs in
                              let uu____3026 =
                                let uu____3027 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst in
                                FStar_Syntax_Subst.subst uu____3027 t in
                              (lid, uvs, uu____3025, uu____3026, lids1,
                                lids2) in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____3008 in
                          {
                            FStar_Syntax_Syntax.sigel = uu____3007;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___596_3006.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___596_3006.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___596_3006.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___596_3006.FStar_Syntax_Syntax.sigattrs);
                            FStar_Syntax_Syntax.sigopts =
                              (uu___596_3006.FStar_Syntax_Syntax.sigopts)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid, uu____3041, t, tlid, n1, lids1) ->
                          let uu___606_3052 = se in
                          let uu____3053 =
                            let uu____3054 =
                              let uu____3070 =
                                FStar_Syntax_Subst.subst usubst t in
                              (lid, uvs, uu____3070, tlid, n1, lids1) in
                            FStar_Syntax_Syntax.Sig_datacon uu____3054 in
                          {
                            FStar_Syntax_Syntax.sigel = uu____3053;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___606_3052.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___606_3052.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___606_3052.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___606_3052.FStar_Syntax_Syntax.sigattrs);
                            FStar_Syntax_Syntax.sigopts =
                              (uu___606_3052.FStar_Syntax_Syntax.sigopts)
                          }
                      | uu____3074 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt")) in
            (uu____2975, lids) in
          FStar_Syntax_Syntax.Sig_bundle uu____2966 in
        {
          FStar_Syntax_Syntax.sigel = uu____2965;
          FStar_Syntax_Syntax.sigrng =
            (uu___585_2964.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___585_2964.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___585_2964.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___585_2964.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___585_2964.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____3081, t) ->
        let uvs =
          let uu____3084 = FStar_Syntax_Free.univnames t in
          FStar_All.pipe_right uu____3084 FStar_Util.set_elements in
        let uu___615_3089 = s in
        let uu____3090 =
          let uu____3091 =
            let uu____3098 = FStar_Syntax_Subst.close_univ_vars uvs t in
            (lid, uvs, uu____3098) in
          FStar_Syntax_Syntax.Sig_declare_typ uu____3091 in
        {
          FStar_Syntax_Syntax.sigel = uu____3090;
          FStar_Syntax_Syntax.sigrng =
            (uu___615_3089.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___615_3089.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___615_3089.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___615_3089.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___615_3089.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_let ((b, lbs), lids) ->
        let lb_univnames lb =
          let uu____3122 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp in
          let uu____3125 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs, e, uu____3132) ->
                let uvs1 = bs_univnames bs in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____3165, (FStar_Util.Inl t, uu____3167),
                       uu____3168)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____3215, (FStar_Util.Inr c, uu____3217),
                       uu____3218)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____3265 -> empty_set in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____3266, (FStar_Util.Inl t, uu____3268), uu____3269) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____3316, (FStar_Util.Inr c, uu____3318), uu____3319) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____3366 -> empty_set in
          FStar_Util.set_union uu____3122 uu____3125 in
        let all_lb_univs =
          let uu____3370 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs ->
                    fun lb ->
                      let uu____3386 = lb_univnames lb in
                      FStar_Util.set_union uvs uu____3386) empty_set) in
          FStar_All.pipe_right uu____3370 FStar_Util.set_elements in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs in
        let uu___670_3396 = s in
        let uu____3397 =
          let uu____3398 =
            let uu____3405 =
              let uu____3406 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb ->
                        let uu___673_3418 = lb in
                        let uu____3419 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp in
                        let uu____3422 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___673_3418.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____3419;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___673_3418.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____3422;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___673_3418.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___673_3418.FStar_Syntax_Syntax.lbpos)
                        })) in
              (b, uu____3406) in
            (uu____3405, lids) in
          FStar_Syntax_Syntax.Sig_let uu____3398 in
        {
          FStar_Syntax_Syntax.sigel = uu____3397;
          FStar_Syntax_Syntax.sigrng =
            (uu___670_3396.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___670_3396.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___670_3396.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___670_3396.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___670_3396.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid, uu____3431, fml) ->
        let uvs =
          let uu____3434 = FStar_Syntax_Free.univnames fml in
          FStar_All.pipe_right uu____3434 FStar_Util.set_elements in
        let uu___681_3439 = s in
        let uu____3440 =
          let uu____3441 =
            let uu____3448 = FStar_Syntax_Subst.close_univ_vars uvs fml in
            (lid, uvs, uu____3448) in
          FStar_Syntax_Syntax.Sig_assume uu____3441 in
        {
          FStar_Syntax_Syntax.sigel = uu____3440;
          FStar_Syntax_Syntax.sigrng =
            (uu___681_3439.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___681_3439.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___681_3439.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___681_3439.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___681_3439.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uu____3450, bs, c, flags)
        ->
        let uvs =
          let uu____3459 =
            let uu____3462 = bs_univnames bs in
            let uu____3465 = FStar_Syntax_Free.univnames_comp c in
            FStar_Util.set_union uu____3462 uu____3465 in
          FStar_All.pipe_right uu____3459 FStar_Util.set_elements in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs in
        let uu___692_3473 = s in
        let uu____3474 =
          let uu____3475 =
            let uu____3488 = FStar_Syntax_Subst.subst_binders usubst bs in
            let uu____3489 = FStar_Syntax_Subst.subst_comp usubst c in
            (lid, uvs, uu____3488, uu____3489, flags) in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____3475 in
        {
          FStar_Syntax_Syntax.sigel = uu____3474;
          FStar_Syntax_Syntax.sigrng =
            (uu___692_3473.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___692_3473.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___692_3473.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___692_3473.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___692_3473.FStar_Syntax_Syntax.sigopts)
        }
    | uu____3492 -> s
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___4_3500 ->
    match uu___4_3500 with
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
    | uu____3549 -> false
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u ->
    fun n1 ->
      if n1 = Prims.int_zero
      then u
      else
        (let uu____3570 = sum_to_universe u (n1 - Prims.int_one) in
         FStar_Syntax_Syntax.U_succ uu____3570)
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1 -> sum_to_universe FStar_Syntax_Syntax.U_zero n1
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int, FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t ->
    let uu____3596 =
      let uu____3597 = unparen t in uu____3597.FStar_Parser_AST.tm in
    match uu____3596 with
    | FStar_Parser_AST.Wild ->
        let uu____3603 =
          let uu____3604 = FStar_Syntax_Unionfind.univ_fresh () in
          FStar_Syntax_Syntax.U_unif uu____3604 in
        FStar_Util.Inr uu____3603
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr, uu____3617)) ->
        let n1 = FStar_Util.int_of_string repr in
        (if n1 < Prims.int_zero
         then
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_NegativeUniverseConstFatal_NotSupported,
               (Prims.op_Hat
                  "Negative universe constant  are not supported : " repr))
             t.FStar_Parser_AST.range
         else ();
         FStar_Util.Inl n1)
    | FStar_Parser_AST.Op (op_plus, t1::t2::[]) ->
        let u1 = desugar_maybe_non_constant_universe t1 in
        let u2 = desugar_maybe_non_constant_universe t2 in
        (match (u1, u2) with
         | (FStar_Util.Inl n1, FStar_Util.Inl n2) -> FStar_Util.Inl (n1 + n2)
         | (FStar_Util.Inl n1, FStar_Util.Inr u) ->
             let uu____3708 = sum_to_universe u n1 in
             FStar_Util.Inr uu____3708
         | (FStar_Util.Inr u, FStar_Util.Inl n1) ->
             let uu____3725 = sum_to_universe u n1 in
             FStar_Util.Inr uu____3725
         | (FStar_Util.Inr u11, FStar_Util.Inr u21) ->
             let uu____3741 =
               let uu____3747 =
                 let uu____3749 = FStar_Parser_AST.term_to_string t in
                 Prims.op_Hat
                   "This universe might contain a sum of two universe variables "
                   uu____3749 in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____3747) in
             FStar_Errors.raise_error uu____3741 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____3758 ->
        let rec aux t1 univargs =
          let uu____3795 =
            let uu____3796 = unparen t1 in uu____3796.FStar_Parser_AST.tm in
          match uu____3795 with
          | FStar_Parser_AST.App (t2, targ, uu____3804) ->
              let uarg = desugar_maybe_non_constant_universe targ in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___5_3831 ->
                     match uu___5_3831 with
                     | FStar_Util.Inr uu____3838 -> true
                     | uu____3841 -> false) univargs
              then
                let uu____3849 =
                  let uu____3850 =
                    FStar_List.map
                      (fun uu___6_3860 ->
                         match uu___6_3860 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs in
                  FStar_Syntax_Syntax.U_max uu____3850 in
                FStar_Util.Inr uu____3849
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___7_3886 ->
                        match uu___7_3886 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____3896 -> failwith "impossible")
                     univargs in
                 let uu____3900 =
                   FStar_List.fold_left
                     (fun m -> fun n1 -> if m > n1 then m else n1)
                     Prims.int_zero nargs in
                 FStar_Util.Inl uu____3900)
          | uu____3916 ->
              let uu____3917 =
                let uu____3923 =
                  let uu____3925 =
                    let uu____3927 = FStar_Parser_AST.term_to_string t1 in
                    Prims.op_Hat uu____3927 " in universe context" in
                  Prims.op_Hat "Unexpected term " uu____3925 in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3923) in
              FStar_Errors.raise_error uu____3917 t1.FStar_Parser_AST.range in
        aux t []
    | uu____3942 ->
        let uu____3943 =
          let uu____3949 =
            let uu____3951 =
              let uu____3953 = FStar_Parser_AST.term_to_string t in
              Prims.op_Hat uu____3953 " in universe context" in
            Prims.op_Hat "Unexpected term " uu____3951 in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3949) in
        FStar_Errors.raise_error uu____3943 t.FStar_Parser_AST.range
let (desugar_universe :
  FStar_Parser_AST.term -> FStar_Syntax_Syntax.universe) =
  fun t ->
    let u = desugar_maybe_non_constant_universe t in
    match u with
    | FStar_Util.Inl n1 -> int_to_universe n1
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
              FStar_Syntax_Syntax.antiquotes = uu____3994;_});
         FStar_Syntax_Syntax.pos = uu____3995;
         FStar_Syntax_Syntax.vars = uu____3996;_})::uu____3997
        ->
        let uu____4028 =
          let uu____4034 =
            let uu____4036 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____4036 in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4034) in
        FStar_Errors.raise_error uu____4028 e.FStar_Syntax_Syntax.pos
    | (bv, e)::uu____4042 ->
        let uu____4061 =
          let uu____4067 =
            let uu____4069 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____4069 in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4067) in
        FStar_Errors.raise_error uu____4061 e.FStar_Syntax_Syntax.pos
let check_fields :
  'Auu____4082 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident * 'Auu____4082) Prims.list ->
        FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env ->
    fun fields ->
      fun rg ->
        let uu____4110 = FStar_List.hd fields in
        match uu____4110 with
        | (f, uu____4120) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f in
              let check_field uu____4132 =
                match uu____4132 with
                | (f', uu____4138) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____4140 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record in
                      if uu____4140
                      then ()
                      else
                        (let msg =
                           FStar_Util.format3
                             "Field %s belongs to record type %s, whereas field %s does not"
                             f.FStar_Ident.str
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                             f'.FStar_Ident.str in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_FieldsNotBelongToSameRecordType,
                             msg) rg))) in
              (let uu____4150 = FStar_List.tl fields in
               FStar_List.iter check_field uu____4150);
              (match () with | () -> record)))
let rec (desugar_data_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern -> (env_t * bnd * annotated_pat Prims.list))
  =
  fun env ->
    fun p ->
      let check_linear_pattern_variables pats r =
        let rec pat_vars p1 =
          match p1.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_dot_term uu____4476 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_wild uu____4483 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_constant uu____4484 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_var x ->
              FStar_Util.set_add x FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_cons (uu____4486, pats1) ->
              let aux out uu____4527 =
                match uu____4527 with
                | (p2, uu____4540) ->
                    let intersection =
                      let uu____4550 = pat_vars p2 in
                      FStar_Util.set_intersect uu____4550 out in
                    let uu____4553 = FStar_Util.set_is_empty intersection in
                    if uu____4553
                    then
                      let uu____4558 = pat_vars p2 in
                      FStar_Util.set_union out uu____4558
                    else
                      (let duplicate_bv =
                         let uu____4564 =
                           FStar_Util.set_elements intersection in
                         FStar_List.hd uu____4564 in
                       let uu____4567 =
                         let uu____4573 =
                           FStar_Util.format1
                             "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                             (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
                         (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                           uu____4573) in
                       FStar_Errors.raise_error uu____4567 r) in
              FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1 in
        match pats with
        | [] -> ()
        | p1::[] ->
            let uu____4597 = pat_vars p1 in
            FStar_All.pipe_right uu____4597 (fun a1 -> ())
        | p1::ps ->
            let pvars = pat_vars p1 in
            let aux p2 =
              let uu____4625 =
                let uu____4627 = pat_vars p2 in
                FStar_Util.set_eq pvars uu____4627 in
              if uu____4625
              then ()
              else
                (let nonlinear_vars =
                   let uu____4636 = pat_vars p2 in
                   FStar_Util.set_symmetric_difference pvars uu____4636 in
                 let first_nonlinear_var =
                   let uu____4640 = FStar_Util.set_elements nonlinear_vars in
                   FStar_List.hd uu____4640 in
                 let uu____4643 =
                   let uu____4649 =
                     FStar_Util.format1
                       "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                       (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
                   (FStar_Errors.Fatal_IncoherentPatterns, uu____4649) in
                 FStar_Errors.raise_error uu____4643 r) in
            FStar_List.iter aux ps in
      let resolvex l e x =
        let uu____4677 =
          FStar_All.pipe_right l
            (FStar_Util.find_opt
               (fun y ->
                  (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                    x.FStar_Ident.idText)) in
        match uu____4677 with
        | FStar_Pervasives_Native.Some y -> (l, e, y)
        | uu____4694 ->
            let uu____4697 = FStar_Syntax_DsEnv.push_bv e x in
            (match uu____4697 with | (e1, x1) -> ((x1 :: l), e1, x1)) in
      let rec aux' top loc env1 p1 =
        let pos q = FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange in
        let pos_r r q = FStar_Syntax_Syntax.withinfo q r in
        let orig = p1 in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr uu____4848 -> failwith "impossible"
        | FStar_Parser_AST.PatOp op ->
            let uu____4872 =
              let uu____4873 =
                let uu____4874 =
                  let uu____4881 =
                    let uu____4882 =
                      let uu____4888 =
                        FStar_Parser_AST.compile_op Prims.int_zero
                          op.FStar_Ident.idText op.FStar_Ident.idRange in
                      (uu____4888, (op.FStar_Ident.idRange)) in
                    FStar_Ident.mk_ident uu____4882 in
                  (uu____4881, FStar_Pervasives_Native.None) in
                FStar_Parser_AST.PatVar uu____4874 in
              {
                FStar_Parser_AST.pat = uu____4873;
                FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
              } in
            aux loc env1 uu____4872
        | FStar_Parser_AST.PatAscribed (p2, (t, tacopt)) ->
            ((match tacopt with
              | FStar_Pervasives_Native.None -> ()
              | FStar_Pervasives_Native.Some uu____4908 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                      "Type ascriptions within patterns cannot be associated with a tactic")
                    orig.FStar_Parser_AST.prange);
             (let uu____4911 = aux loc env1 p2 in
              match uu____4911 with
              | (loc1, env', binder, p3, annots, imp) ->
                  let annot_pat_var p4 t1 =
                    match p4.FStar_Syntax_Syntax.v with
                    | FStar_Syntax_Syntax.Pat_var x ->
                        let uu___929_5000 = p4 in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_var
                               (let uu___931_5005 = x in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___931_5005.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___931_5005.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___929_5000.FStar_Syntax_Syntax.p)
                        }
                    | FStar_Syntax_Syntax.Pat_wild x ->
                        let uu___935_5007 = p4 in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_wild
                               (let uu___937_5012 = x in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___937_5012.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___937_5012.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___935_5007.FStar_Syntax_Syntax.p)
                        }
                    | uu____5013 when top -> p4
                    | uu____5014 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                            "Type ascriptions within patterns are only allowed on variables")
                          orig.FStar_Parser_AST.prange in
                  let uu____5019 =
                    match binder with
                    | LetBinder uu____5040 -> failwith "impossible"
                    | LocalBinder (x, aq) ->
                        let t1 =
                          let uu____5065 = close_fun env1 t in
                          desugar_term env1 uu____5065 in
                        let x1 =
                          let uu___948_5067 = x in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___948_5067.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___948_5067.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t1
                          } in
                        ([(x1, t1)], (LocalBinder (x1, aq))) in
                  (match uu____5019 with
                   | (annots', binder1) ->
                       (loc1, env', binder1, p3,
                         (FStar_List.append annots' annots), imp))))
        | FStar_Parser_AST.PatWild aq ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit) in
            let aq1 = trans_aqual env1 aq in
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                FStar_Syntax_Syntax.tun in
            let uu____5135 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x) in
            (loc, env1, (LocalBinder (x, aq1)), uu____5135, [], imp)
        | FStar_Parser_AST.PatConst c ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                FStar_Syntax_Syntax.tun in
            let uu____5149 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c) in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____5149, [], false)
        | FStar_Parser_AST.PatTvar (x, aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit) in
            let aq1 = trans_aqual env1 aq in
            let uu____5173 = resolvex loc env1 x in
            (match uu____5173 with
             | (loc1, env2, xbv) ->
                 let uu____5202 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv) in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____5202, [], imp))
        | FStar_Parser_AST.PatVar (x, aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit) in
            let aq1 = trans_aqual env1 aq in
            let uu____5225 = resolvex loc env1 x in
            (match uu____5225 with
             | (loc1, env2, xbv) ->
                 let uu____5254 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv) in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____5254, [], imp))
        | FStar_Parser_AST.PatName l ->
            let l1 =
              FStar_Syntax_DsEnv.fail_or env1
                (FStar_Syntax_DsEnv.try_lookup_datacon env1) l in
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                FStar_Syntax_Syntax.tun in
            let uu____5269 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (l1, [])) in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____5269, [], false)
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
               FStar_Parser_AST.prange = uu____5299;_},
             args)
            ->
            let uu____5305 =
              FStar_List.fold_right
                (fun arg ->
                   fun uu____5366 ->
                     match uu____5366 with
                     | (loc1, env2, annots, args1) ->
                         let uu____5447 = aux loc1 env2 arg in
                         (match uu____5447 with
                          | (loc2, env3, uu____5494, arg1, ans, imp) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((arg1, imp) :: args1)))) args
                (loc, env1, [], []) in
            (match uu____5305 with
             | (loc1, env2, annots, args1) ->
                 let l1 =
                   FStar_Syntax_DsEnv.fail_or env2
                     (FStar_Syntax_DsEnv.try_lookup_datacon env2) l in
                 let x =
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some
                        (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun in
                 let uu____5626 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args1)) in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____5626, annots, false))
        | FStar_Parser_AST.PatApp uu____5644 ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
              p1.FStar_Parser_AST.prange
        | FStar_Parser_AST.PatList pats ->
            let uu____5675 =
              FStar_List.fold_right
                (fun pat ->
                   fun uu____5726 ->
                     match uu____5726 with
                     | (loc1, env2, annots, pats1) ->
                         let uu____5787 = aux loc1 env2 pat in
                         (match uu____5787 with
                          | (loc2, env3, uu____5829, pat1, ans, uu____5832)
                              ->
                              (loc2, env3, (FStar_List.append ans annots),
                                (pat1 :: pats1)))) pats (loc, env1, [], []) in
            (match uu____5675 with
             | (loc1, env2, annots, pats1) ->
                 let pat =
                   let uu____5929 =
                     let uu____5932 =
                       let uu____5939 =
                         FStar_Range.end_range p1.FStar_Parser_AST.prange in
                       pos_r uu____5939 in
                     let uu____5940 =
                       let uu____5941 =
                         let uu____5955 =
                           FStar_Syntax_Syntax.lid_as_fv
                             FStar_Parser_Const.nil_lid
                             FStar_Syntax_Syntax.delta_constant
                             (FStar_Pervasives_Native.Some
                                FStar_Syntax_Syntax.Data_ctor) in
                         (uu____5955, []) in
                       FStar_Syntax_Syntax.Pat_cons uu____5941 in
                     FStar_All.pipe_left uu____5932 uu____5940 in
                   FStar_List.fold_right
                     (fun hd1 ->
                        fun tl1 ->
                          let r =
                            FStar_Range.union_ranges
                              hd1.FStar_Syntax_Syntax.p
                              tl1.FStar_Syntax_Syntax.p in
                          let uu____5989 =
                            let uu____5990 =
                              let uu____6004 =
                                FStar_Syntax_Syntax.lid_as_fv
                                  FStar_Parser_Const.cons_lid
                                  FStar_Syntax_Syntax.delta_constant
                                  (FStar_Pervasives_Native.Some
                                     FStar_Syntax_Syntax.Data_ctor) in
                              (uu____6004, [(hd1, false); (tl1, false)]) in
                            FStar_Syntax_Syntax.Pat_cons uu____5990 in
                          FStar_All.pipe_left (pos_r r) uu____5989) pats1
                     uu____5929 in
                 let x =
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some
                        (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)), pat,
                   annots, false))
        | FStar_Parser_AST.PatTuple (args, dep1) ->
            let uu____6062 =
              FStar_List.fold_left
                (fun uu____6122 ->
                   fun p2 ->
                     match uu____6122 with
                     | (loc1, env2, annots, pats) ->
                         let uu____6204 = aux loc1 env2 p2 in
                         (match uu____6204 with
                          | (loc2, env3, uu____6251, pat, ans, uu____6254) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((pat, false) :: pats)))) (loc, env1, [], [])
                args in
            (match uu____6062 with
             | (loc1, env2, annots, args1) ->
                 let args2 = FStar_List.rev args1 in
                 let l =
                   if dep1
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
                   | uu____6420 -> failwith "impossible" in
                 let x =
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some
                        (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun in
                 let uu____6423 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args2)) in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____6423, annots, false))
        | FStar_Parser_AST.PatRecord [] ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
              p1.FStar_Parser_AST.prange
        | FStar_Parser_AST.PatRecord fields ->
            let record = check_fields env1 fields p1.FStar_Parser_AST.prange in
            let fields1 =
              FStar_All.pipe_right fields
                (FStar_List.map
                   (fun uu____6504 ->
                      match uu____6504 with
                      | (f, p2) -> ((f.FStar_Ident.ident), p2))) in
            let args =
              FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                (FStar_List.map
                   (fun uu____6534 ->
                      match uu____6534 with
                      | (f, uu____6540) ->
                          let uu____6541 =
                            FStar_All.pipe_right fields1
                              (FStar_List.tryFind
                                 (fun uu____6567 ->
                                    match uu____6567 with
                                    | (g, uu____6574) ->
                                        f.FStar_Ident.idText =
                                          g.FStar_Ident.idText)) in
                          (match uu____6541 with
                           | FStar_Pervasives_Native.None ->
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatWild
                                    FStar_Pervasives_Native.None)
                                 p1.FStar_Parser_AST.prange
                           | FStar_Pervasives_Native.Some (uu____6580, p2) ->
                               p2))) in
            let app =
              let uu____6587 =
                let uu____6588 =
                  let uu____6595 =
                    let uu____6596 =
                      let uu____6597 =
                        FStar_Ident.lid_of_ids
                          (FStar_List.append
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                             [record.FStar_Syntax_DsEnv.constrname]) in
                      FStar_Parser_AST.PatName uu____6597 in
                    FStar_Parser_AST.mk_pattern uu____6596
                      p1.FStar_Parser_AST.prange in
                  (uu____6595, args) in
                FStar_Parser_AST.PatApp uu____6588 in
              FStar_Parser_AST.mk_pattern uu____6587
                p1.FStar_Parser_AST.prange in
            let uu____6600 = aux loc env1 app in
            (match uu____6600 with
             | (env2, e, b, p2, annots, uu____6646) ->
                 let p3 =
                   match p2.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_cons (fv, args1) ->
                       let uu____6686 =
                         let uu____6687 =
                           let uu____6701 =
                             let uu___1096_6702 = fv in
                             let uu____6703 =
                               let uu____6706 =
                                 let uu____6707 =
                                   let uu____6714 =
                                     FStar_All.pipe_right
                                       record.FStar_Syntax_DsEnv.fields
                                       (FStar_List.map
                                          FStar_Pervasives_Native.fst) in
                                   ((record.FStar_Syntax_DsEnv.typename),
                                     uu____6714) in
                                 FStar_Syntax_Syntax.Record_ctor uu____6707 in
                               FStar_Pervasives_Native.Some uu____6706 in
                             {
                               FStar_Syntax_Syntax.fv_name =
                                 (uu___1096_6702.FStar_Syntax_Syntax.fv_name);
                               FStar_Syntax_Syntax.fv_delta =
                                 (uu___1096_6702.FStar_Syntax_Syntax.fv_delta);
                               FStar_Syntax_Syntax.fv_qual = uu____6703
                             } in
                           (uu____6701, args1) in
                         FStar_Syntax_Syntax.Pat_cons uu____6687 in
                       FStar_All.pipe_left pos uu____6686
                   | uu____6740 -> p2 in
                 (env2, e, b, p3, annots, false))
      and aux loc env1 p1 = aux' false loc env1 p1 in
      let aux_maybe_or env1 p1 =
        let loc = [] in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr [] -> failwith "impossible"
        | FStar_Parser_AST.PatOr (p2::ps) ->
            let uu____6826 = aux' true loc env1 p2 in
            (match uu____6826 with
             | (loc1, env2, var, p3, ans, uu____6870) ->
                 let uu____6885 =
                   FStar_List.fold_left
                     (fun uu____6934 ->
                        fun p4 ->
                          match uu____6934 with
                          | (loc2, env3, ps1) ->
                              let uu____6999 = aux' true loc2 env3 p4 in
                              (match uu____6999 with
                               | (loc3, env4, uu____7040, p5, ans1,
                                  uu____7043) ->
                                   (loc3, env4, ((p5, ans1) :: ps1))))
                     (loc1, env2, []) ps in
                 (match uu____6885 with
                  | (loc2, env3, ps1) ->
                      let pats = (p3, ans) :: (FStar_List.rev ps1) in
                      (env3, var, pats)))
        | uu____7204 ->
            let uu____7205 = aux' true loc env1 p1 in
            (match uu____7205 with
             | (loc1, env2, vars, pat, ans, b) -> (env2, vars, [(pat, ans)])) in
      let uu____7302 = aux_maybe_or env p in
      match uu____7302 with
      | (env1, b, pats) ->
          ((let uu____7357 = FStar_List.map FStar_Pervasives_Native.fst pats in
            check_linear_pattern_variables uu____7357
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
        let mklet x ty tacopt =
          let uu____7430 =
            let uu____7431 =
              let uu____7442 = FStar_Syntax_DsEnv.qualify env x in
              (uu____7442, (ty, tacopt)) in
            LetBinder uu____7431 in
          (env, uu____7430, []) in
        let op_to_ident x =
          let uu____7459 =
            let uu____7465 =
              FStar_Parser_AST.compile_op Prims.int_zero x.FStar_Ident.idText
                x.FStar_Ident.idRange in
            (uu____7465, (x.FStar_Ident.idRange)) in
          FStar_Ident.mk_ident uu____7459 in
        if top
        then
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu____7487 = op_to_ident x in
              mklet uu____7487 FStar_Syntax_Syntax.tun
                FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x, uu____7489) ->
              mklet x FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu____7495;_},
               (t, tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env) in
              let uu____7511 = op_to_ident x in
              let uu____7512 = desugar_term env t in
              mklet uu____7511 uu____7512 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x, uu____7514);
                 FStar_Parser_AST.prange = uu____7515;_},
               (t, tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env) in
              let uu____7535 = desugar_term env t in
              mklet x uu____7535 tacopt1
          | uu____7536 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu____7549 = desugar_data_pat env p in
           match uu____7549 with
           | (env1, binder, p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu____7578;
                      FStar_Syntax_Syntax.p = uu____7579;_},
                    uu____7580)::[] -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu____7593;
                      FStar_Syntax_Syntax.p = uu____7594;_},
                    uu____7595)::[] -> []
                 | uu____7608 -> p1 in
               (env1, binder, p2))
and (desugar_binding_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern -> (env_t * bnd * annotated_pat Prims.list))
  = fun env -> fun p -> desugar_binding_pat_maybe_top false env p
and (desugar_match_pat_maybe_top :
  Prims.bool ->
    FStar_Syntax_DsEnv.env ->
      FStar_Parser_AST.pattern -> (env_t * annotated_pat Prims.list))
  =
  fun uu____7616 ->
    fun env ->
      fun pat ->
        let uu____7620 = desugar_data_pat env pat in
        match uu____7620 with | (env1, uu____7636, pat1) -> (env1, pat1)
and (desugar_match_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern -> (env_t * annotated_pat Prims.list))
  = fun env -> fun p -> desugar_match_pat_maybe_top false env p
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
      let uu____7658 = desugar_term_aq env e in
      match uu____7658 with | (t, aq) -> (check_no_aq aq; t)
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
      let uu____7677 = desugar_typ_aq env e in
      match uu____7677 with | (t, aq) -> (check_no_aq aq; t)
and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness * FStar_Const.width) ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun repr ->
      fun uu____7687 ->
        fun range ->
          match uu____7687 with
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
              ((let uu____7709 =
                  let uu____7711 =
                    FStar_Const.within_bounds repr signedness width in
                  Prims.op_Negation uu____7711 in
                if uu____7709
                then
                  let uu____7714 =
                    let uu____7720 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm in
                    (FStar_Errors.Error_OutOfRange, uu____7720) in
                  FStar_Errors.log_issue range uu____7714
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
                  let uu____7741 = FStar_Ident.path_of_text intro_nm in
                  FStar_Ident.lid_of_path uu____7741 range in
                let lid1 =
                  let uu____7745 = FStar_Syntax_DsEnv.try_lookup_lid env lid in
                  match uu____7745 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____7755 =
                               FStar_Ident.path_of_text private_intro_nm in
                             FStar_Ident.lid_of_path uu____7755 range in
                           let private_fv =
                             let uu____7757 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____7757 fv.FStar_Syntax_Syntax.fv_qual in
                           let uu___1266_7758 = intro_term in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___1266_7758.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1266_7758.FStar_Syntax_Syntax.vars)
                           }
                       | uu____7759 ->
                           failwith
                             (Prims.op_Hat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None ->
                      let uu____7763 =
                        let uu____7769 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____7769) in
                      FStar_Errors.raise_error uu____7763 range in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range in
                let uu____7789 =
                  let uu____7796 =
                    let uu____7797 =
                      let uu____7814 =
                        let uu____7825 =
                          let uu____7834 =
                            FStar_Syntax_Syntax.as_implicit false in
                          (repr1, uu____7834) in
                        [uu____7825] in
                      (lid1, uu____7814) in
                    FStar_Syntax_Syntax.Tm_app uu____7797 in
                  FStar_Syntax_Syntax.mk uu____7796 in
                uu____7789 FStar_Pervasives_Native.None range))
and (desugar_term_maybe_top :
  Prims.bool ->
    env_t ->
      FStar_Parser_AST.term ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.antiquotations))
  =
  fun top_level ->
    fun env ->
      fun top ->
        let mk1 e =
          FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
            top.FStar_Parser_AST.range in
        let noaqs = [] in
        let join_aqs aqs = FStar_List.flatten aqs in
        let setpos e =
          let uu___1282_7953 = e in
          {
            FStar_Syntax_Syntax.n = (uu___1282_7953.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___1282_7953.FStar_Syntax_Syntax.vars)
          } in
        let uu____7956 =
          let uu____7957 = unparen top in uu____7957.FStar_Parser_AST.tm in
        match uu____7956 with
        | FStar_Parser_AST.Wild -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____7962 ->
            let uu____7971 = desugar_formula env top in (uu____7971, noaqs)
        | FStar_Parser_AST.Requires (t, lopt) ->
            let uu____7980 = desugar_formula env t in (uu____7980, noaqs)
        | FStar_Parser_AST.Ensures (t, lopt) ->
            let uu____7989 = desugar_formula env t in (uu____7989, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i, FStar_Pervasives_Native.Some size)) ->
            let uu____8016 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range in
            (uu____8016, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____8018 = mk1 (FStar_Syntax_Syntax.Tm_constant c) in
            (uu____8018, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_}, args)
            ->
            let e =
              let uu____8027 =
                let uu____8028 =
                  let uu____8035 = FStar_Ident.mk_ident ("==", r) in
                  (uu____8035, args) in
                FStar_Parser_AST.Op uu____8028 in
              FStar_Parser_AST.mk_term uu____8027 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level in
            let uu____8040 =
              let uu____8041 =
                let uu____8042 =
                  let uu____8049 = FStar_Ident.mk_ident ("~", r) in
                  (uu____8049, [e]) in
                FStar_Parser_AST.Op uu____8042 in
              FStar_Parser_AST.mk_term uu____8041 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level in
            desugar_term_aq env uu____8040
        | FStar_Parser_AST.Op (op_star, lhs::rhs::[]) when
            (let uu____8061 = FStar_Ident.text_of_id op_star in
             uu____8061 = "*") &&
              (let uu____8066 =
                 op_as_term env (Prims.of_int (2)) top.FStar_Parser_AST.range
                   op_star in
               FStar_All.pipe_right uu____8066 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____8083;_},
                   t1::t2::[])
                  when
                  let uu____8089 =
                    op_as_term env (Prims.of_int (2))
                      top.FStar_Parser_AST.range op_star in
                  FStar_All.pipe_right uu____8089 FStar_Option.isNone ->
                  let uu____8096 = flatten1 t1 in
                  FStar_List.append uu____8096 [t2]
              | uu____8099 -> [t] in
            let terms = flatten1 lhs in
            let t =
              let uu___1330_8104 = top in
              let uu____8105 =
                let uu____8106 =
                  let uu____8117 =
                    FStar_List.map (fun _8128 -> FStar_Util.Inr _8128) terms in
                  (uu____8117, rhs) in
                FStar_Parser_AST.Sum uu____8106 in
              {
                FStar_Parser_AST.tm = uu____8105;
                FStar_Parser_AST.range =
                  (uu___1330_8104.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1330_8104.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env t
        | FStar_Parser_AST.Tvar a ->
            let uu____8136 =
              let uu____8137 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a in
              FStar_All.pipe_left setpos uu____8137 in
            (uu____8136, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____8143 =
              let uu____8149 =
                let uu____8151 =
                  let uu____8153 = FStar_Ident.text_of_id u in
                  Prims.op_Hat uu____8153 " in non-universe context" in
                Prims.op_Hat "Unexpected universe variable " uu____8151 in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____8149) in
            FStar_Errors.raise_error uu____8143 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s, args) ->
            let uu____8168 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s in
            (match uu____8168 with
             | FStar_Pervasives_Native.None ->
                 let uu____8175 =
                   let uu____8181 =
                     let uu____8183 = FStar_Ident.text_of_id s in
                     Prims.op_Hat "Unexpected or unbound operator: "
                       uu____8183 in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____8181) in
                 FStar_Errors.raise_error uu____8175
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > Prims.int_zero
                 then
                   let uu____8198 =
                     let uu____8223 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t ->
                               let uu____8285 = desugar_term_aq env t in
                               match uu____8285 with
                               | (t', s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1))) in
                     FStar_All.pipe_right uu____8223 FStar_List.unzip in
                   (match uu____8198 with
                    | (args1, aqs) ->
                        let uu____8418 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1)) in
                        (uu____8418, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1, (a, uu____8435)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____8452 =
              let uu___1359_8453 = top in
              let uu____8454 =
                let uu____8455 =
                  let uu____8462 =
                    let uu___1361_8463 = top in
                    let uu____8464 =
                      let uu____8465 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____8465 in
                    {
                      FStar_Parser_AST.tm = uu____8464;
                      FStar_Parser_AST.range =
                        (uu___1361_8463.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1361_8463.FStar_Parser_AST.level)
                    } in
                  (uu____8462, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____8455 in
              {
                FStar_Parser_AST.tm = uu____8454;
                FStar_Parser_AST.range =
                  (uu___1359_8453.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1359_8453.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____8452
        | FStar_Parser_AST.Construct (n1, (a, uu____8473)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____8493 =
                let uu___1371_8494 = top in
                let uu____8495 =
                  let uu____8496 =
                    let uu____8503 =
                      let uu___1373_8504 = top in
                      let uu____8505 =
                        let uu____8506 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range in
                        FStar_Parser_AST.Var uu____8506 in
                      {
                        FStar_Parser_AST.tm = uu____8505;
                        FStar_Parser_AST.range =
                          (uu___1373_8504.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___1373_8504.FStar_Parser_AST.level)
                      } in
                    (uu____8503, a, FStar_Parser_AST.Nothing) in
                  FStar_Parser_AST.App uu____8496 in
                {
                  FStar_Parser_AST.tm = uu____8495;
                  FStar_Parser_AST.range =
                    (uu___1371_8494.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___1371_8494.FStar_Parser_AST.level)
                } in
              desugar_term_maybe_top top_level env uu____8493))
        | FStar_Parser_AST.Construct (n1, (a, uu____8514)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____8531 =
              let uu___1382_8532 = top in
              let uu____8533 =
                let uu____8534 =
                  let uu____8541 =
                    let uu___1384_8542 = top in
                    let uu____8543 =
                      let uu____8544 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____8544 in
                    {
                      FStar_Parser_AST.tm = uu____8543;
                      FStar_Parser_AST.range =
                        (uu___1384_8542.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1384_8542.FStar_Parser_AST.level)
                    } in
                  (uu____8541, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____8534 in
              {
                FStar_Parser_AST.tm = uu____8533;
                FStar_Parser_AST.range =
                  (uu___1382_8532.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1382_8532.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____8531
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8550; FStar_Ident.ident = uu____8551;
              FStar_Ident.nsstr = uu____8552; FStar_Ident.str = "Type0";_}
            ->
            let uu____8557 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero) in
            (uu____8557, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8558; FStar_Ident.ident = uu____8559;
              FStar_Ident.nsstr = uu____8560; FStar_Ident.str = "Type";_}
            ->
            let uu____8565 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown) in
            (uu____8565, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____8566; FStar_Ident.ident = uu____8567;
               FStar_Ident.nsstr = uu____8568; FStar_Ident.str = "Type";_},
             (t, FStar_Parser_AST.UnivApp)::[])
            ->
            let uu____8588 =
              let uu____8589 =
                let uu____8590 = desugar_universe t in
                FStar_Syntax_Syntax.Tm_type uu____8590 in
              mk1 uu____8589 in
            (uu____8588, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8591; FStar_Ident.ident = uu____8592;
              FStar_Ident.nsstr = uu____8593; FStar_Ident.str = "Effect";_}
            ->
            let uu____8598 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect) in
            (uu____8598, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8599; FStar_Ident.ident = uu____8600;
              FStar_Ident.nsstr = uu____8601; FStar_Ident.str = "True";_}
            ->
            let uu____8606 =
              let uu____8607 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range in
              FStar_Syntax_Syntax.fvar uu____8607
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None in
            (uu____8606, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8608; FStar_Ident.ident = uu____8609;
              FStar_Ident.nsstr = uu____8610; FStar_Ident.str = "False";_}
            ->
            let uu____8615 =
              let uu____8616 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range in
              FStar_Syntax_Syntax.fvar uu____8616
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None in
            (uu____8615, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,
             { FStar_Ident.idText = txt; FStar_Ident.idRange = uu____8619;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____8622 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name in
              match uu____8622 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt in
                  let uu____8631 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_constant_at_level
                         Prims.int_one) FStar_Pervasives_Native.None in
                  (uu____8631, noaqs)
              | FStar_Pervasives_Native.None ->
                  let uu____8633 =
                    let uu____8635 = FStar_Ident.text_of_lid eff_name in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____8635 txt in
                  failwith uu____8633))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8644 = desugar_name mk1 setpos env true l in
              (uu____8644, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8653 = desugar_name mk1 setpos env true l in
              (uu____8653, noaqs)))
        | FStar_Parser_AST.Projector (l, i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____8671 = FStar_Syntax_DsEnv.try_lookup_datacon env l in
                match uu____8671 with
                | FStar_Pervasives_Native.Some uu____8681 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None ->
                    let uu____8689 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l in
                    (match uu____8689 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____8707 -> FStar_Pervasives_Native.None) in
              match name with
              | FStar_Pervasives_Native.Some (resolve, new_name) ->
                  let uu____8728 =
                    let uu____8729 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i in
                    desugar_name mk1 setpos env resolve uu____8729 in
                  (uu____8728, noaqs)
              | uu____8735 ->
                  let uu____8743 =
                    let uu____8749 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str in
                    (FStar_Errors.Fatal_EffectNotFound, uu____8749) in
                  FStar_Errors.raise_error uu____8743
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____8759 = FStar_Syntax_DsEnv.try_lookup_datacon env lid in
              match uu____8759 with
              | FStar_Pervasives_Native.None ->
                  let uu____8766 =
                    let uu____8772 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____8772) in
                  FStar_Errors.raise_error uu____8766
                    top.FStar_Parser_AST.range
              | uu____8780 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid in
                  let uu____8784 = desugar_name mk1 setpos env true lid' in
                  (uu____8784, noaqs)))
        | FStar_Parser_AST.Construct (l, args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8806 = FStar_Syntax_DsEnv.try_lookup_datacon env l in
              match uu____8806 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1) in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____8825 ->
                       let uu____8832 =
                         FStar_Util.take
                           (fun uu____8856 ->
                              match uu____8856 with
                              | (uu____8862, imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args in
                       (match uu____8832 with
                        | (universes, args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes in
                            let uu____8907 =
                              let uu____8932 =
                                FStar_List.map
                                  (fun uu____8975 ->
                                     match uu____8975 with
                                     | (t, imp) ->
                                         let uu____8992 =
                                           desugar_term_aq env t in
                                         (match uu____8992 with
                                          | (te, aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1 in
                              FStar_All.pipe_right uu____8932
                                FStar_List.unzip in
                            (match uu____8907 with
                             | (args2, aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1)) in
                                 let uu____9135 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2)) in
                                 (uu____9135, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None ->
                  let err =
                    let uu____9154 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l in
                    match uu____9154 with
                    | FStar_Pervasives_Native.None ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.op_Hat "Constructor "
                             (Prims.op_Hat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____9165 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.op_Hat "Effect "
                             (Prims.op_Hat l.FStar_Ident.str
                                " used at an unexpected position"))) in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders, t) when
            FStar_Util.for_all
              (fun uu___8_9193 ->
                 match uu___8_9193 with
                 | FStar_Util.Inr uu____9199 -> true
                 | uu____9201 -> false) binders
            ->
            let terms =
              let uu____9210 =
                FStar_All.pipe_right binders
                  (FStar_List.map
                     (fun uu___9_9227 ->
                        match uu___9_9227 with
                        | FStar_Util.Inr x -> x
                        | FStar_Util.Inl uu____9233 -> failwith "Impossible")) in
              FStar_List.append uu____9210 [t] in
            let uu____9235 =
              let uu____9260 =
                FStar_All.pipe_right terms
                  (FStar_List.map
                     (fun t1 ->
                        let uu____9317 = desugar_typ_aq env t1 in
                        match uu____9317 with
                        | (t', aq) ->
                            let uu____9328 = FStar_Syntax_Syntax.as_arg t' in
                            (uu____9328, aq))) in
              FStar_All.pipe_right uu____9260 FStar_List.unzip in
            (match uu____9235 with
             | (targs, aqs) ->
                 let tup =
                   let uu____9438 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____9438 in
                 let uu____9447 =
                   mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs)) in
                 (uu____9447, (join_aqs aqs)))
        | FStar_Parser_AST.Sum (binders, t) ->
            let uu____9474 =
              let uu____9491 =
                let uu____9498 =
                  let uu____9505 =
                    FStar_All.pipe_left (fun _9514 -> FStar_Util.Inl _9514)
                      (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                         FStar_Pervasives_Native.None) in
                  [uu____9505] in
                FStar_List.append binders uu____9498 in
              FStar_List.fold_left
                (fun uu____9559 ->
                   fun b ->
                     match uu____9559 with
                     | (env1, tparams, typs) ->
                         let uu____9620 =
                           match b with
                           | FStar_Util.Inl b1 -> desugar_binder env1 b1
                           | FStar_Util.Inr t1 ->
                               let uu____9635 = desugar_typ env1 t1 in
                               (FStar_Pervasives_Native.None, uu____9635) in
                         (match uu____9620 with
                          | (xopt, t1) ->
                              let uu____9660 =
                                match xopt with
                                | FStar_Pervasives_Native.None ->
                                    let uu____9669 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun in
                                    (env1, uu____9669)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x in
                              (match uu____9660 with
                               | (env2, x) ->
                                   let uu____9689 =
                                     let uu____9692 =
                                       let uu____9695 =
                                         let uu____9696 =
                                           no_annot_abs tparams t1 in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____9696 in
                                       [uu____9695] in
                                     FStar_List.append typs uu____9692 in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___1543_9722 = x in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___1543_9722.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___1543_9722.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____9689)))) (env, [], []) uu____9491 in
            (match uu____9474 with
             | (env1, uu____9750, targs) ->
                 let tup =
                   let uu____9773 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____9773 in
                 let uu____9774 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_app (tup, targs)) in
                 (uu____9774, noaqs))
        | FStar_Parser_AST.Product (binders, t) ->
            let uu____9793 = uncurry binders t in
            (match uu____9793 with
             | (bs, t1) ->
                 let rec aux env1 bs1 uu___10_9837 =
                   match uu___10_9837 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range true env1 t1 in
                       let uu____9854 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod in
                       FStar_All.pipe_left setpos uu____9854
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1 in
                       let uu____9878 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb in
                       (match uu____9878 with
                        | (b, env2) -> aux env2 (b :: bs1) tl1) in
                 let uu____9911 = aux env [] bs in (uu____9911, noaqs))
        | FStar_Parser_AST.Refine (b, f) ->
            let uu____9920 = desugar_binder env b in
            (match uu____9920 with
             | (FStar_Pervasives_Native.None, uu____9931) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____9946 =
                   as_binder env FStar_Pervasives_Native.None b1 in
                 (match uu____9946 with
                  | ((x, uu____9962), env1) ->
                      let f1 = desugar_formula env1 f in
                      let uu____9975 =
                        let uu____9976 = FStar_Syntax_Util.refine x f1 in
                        FStar_All.pipe_left setpos uu____9976 in
                      (uu____9975, noaqs)))
        | FStar_Parser_AST.Abs (binders, body) ->
            let bvss =
              FStar_List.map (gather_pattern_bound_vars false) binders in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set1::sets2 ->
                    let i = FStar_Util.set_intersect acc set1 in
                    let uu____10055 = FStar_Util.set_is_empty i in
                    if uu____10055
                    then
                      let uu____10060 = FStar_Util.set_union acc set1 in
                      aux uu____10060 sets2
                    else
                      (let uu____10065 =
                         let uu____10066 = FStar_Util.set_elements i in
                         FStar_List.hd uu____10066 in
                       FStar_Pervasives_Native.Some uu____10065) in
              let uu____10069 = FStar_Syntax_Syntax.new_id_set () in
              aux uu____10069 sets in
            ((let uu____10073 = check_disjoint bvss in
              match uu____10073 with
              | FStar_Pervasives_Native.None -> ()
              | FStar_Pervasives_Native.Some id1 ->
                  let uu____10077 =
                    let uu____10083 =
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        id1.FStar_Ident.idText in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____10083) in
                  let uu____10087 = FStar_Ident.range_of_id id1 in
                  FStar_Errors.raise_error uu____10077 uu____10087);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern) in
              let uu____10095 =
                FStar_List.fold_left
                  (fun uu____10115 ->
                     fun pat ->
                       match uu____10115 with
                       | (env1, ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____10141,
                                 (t, FStar_Pervasives_Native.None))
                                ->
                                let uu____10151 =
                                  let uu____10154 = free_type_vars env1 t in
                                  FStar_List.append uu____10154 ftvs in
                                (env1, uu____10151)
                            | FStar_Parser_AST.PatAscribed
                                (uu____10159,
                                 (t, FStar_Pervasives_Native.Some tac))
                                ->
                                let uu____10170 =
                                  let uu____10173 = free_type_vars env1 t in
                                  let uu____10176 =
                                    let uu____10179 = free_type_vars env1 tac in
                                    FStar_List.append uu____10179 ftvs in
                                  FStar_List.append uu____10173 uu____10176 in
                                (env1, uu____10170)
                            | uu____10184 -> (env1, ftvs))) (env, [])
                  binders1 in
              match uu____10095 with
              | (uu____10193, ftv) ->
                  let ftv1 = sort_ftv ftv in
                  let binders2 =
                    let uu____10205 =
                      FStar_All.pipe_right ftv1
                        (FStar_List.map
                           (fun a ->
                              FStar_Parser_AST.mk_pattern
                                (FStar_Parser_AST.PatTvar
                                   (a,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Parser_AST.Implicit)))
                                top.FStar_Parser_AST.range)) in
                    FStar_List.append uu____10205 binders1 in
                  let rec aux env1 bs sc_pat_opt uu___11_10262 =
                    match uu___11_10262 with
                    | [] ->
                        let uu____10289 = desugar_term_aq env1 body in
                        (match uu____10289 with
                         | (body1, aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc, pat) ->
                                   let body2 =
                                     let uu____10326 =
                                       let uu____10327 =
                                         FStar_Syntax_Syntax.pat_bvs pat in
                                       FStar_All.pipe_right uu____10327
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder) in
                                     FStar_Syntax_Subst.close uu____10326
                                       body1 in
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_match
                                        (sc,
                                          [(pat,
                                             FStar_Pervasives_Native.None,
                                             body2)]))
                                     FStar_Pervasives_Native.None
                                     body2.FStar_Syntax_Syntax.pos
                               | FStar_Pervasives_Native.None -> body1 in
                             let uu____10396 =
                               let uu____10399 =
                                 no_annot_abs (FStar_List.rev bs) body2 in
                               setpos uu____10399 in
                             (uu____10396, aq))
                    | p::rest ->
                        let uu____10414 = desugar_binding_pat env1 p in
                        (match uu____10414 with
                         | (env2, b, pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1, uu____10448)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____10463 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange in
                             let uu____10472 =
                               match b with
                               | LetBinder uu____10513 ->
                                   failwith "Impossible"
                               | LocalBinder (x, aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None,
                                        uu____10582) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some p1,
                                        FStar_Pervasives_Native.None) ->
                                         let uu____10636 =
                                           let uu____10645 =
                                             FStar_Syntax_Syntax.bv_to_name x in
                                           (uu____10645, p1) in
                                         FStar_Pervasives_Native.Some
                                           uu____10636
                                     | (FStar_Pervasives_Native.Some p1,
                                        FStar_Pervasives_Native.Some
                                        (sc, p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____10707, uu____10708) ->
                                              let tup2 =
                                                let uu____10710 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.of_int (2))
                                                    top.FStar_Parser_AST.range in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10710
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor) in
                                              let sc1 =
                                                let uu____10715 =
                                                  let uu____10722 =
                                                    let uu____10723 =
                                                      let uu____10740 =
                                                        mk1
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2) in
                                                      let uu____10743 =
                                                        let uu____10754 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc in
                                                        let uu____10763 =
                                                          let uu____10774 =
                                                            let uu____10783 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____10783 in
                                                          [uu____10774] in
                                                        uu____10754 ::
                                                          uu____10763 in
                                                      (uu____10740,
                                                        uu____10743) in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____10723 in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____10722 in
                                                uu____10715
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range in
                                              let p2 =
                                                let uu____10831 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____10831 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____10882, args),
                                             FStar_Syntax_Syntax.Pat_cons
                                             (uu____10884, pats)) ->
                                              let tupn =
                                                let uu____10929 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.int_one +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10929
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor) in
                                              let sc1 =
                                                let uu____10942 =
                                                  let uu____10943 =
                                                    let uu____10960 =
                                                      mk1
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn) in
                                                    let uu____10963 =
                                                      let uu____10974 =
                                                        let uu____10985 =
                                                          let uu____10994 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____10994 in
                                                        [uu____10985] in
                                                      FStar_List.append args
                                                        uu____10974 in
                                                    (uu____10960,
                                                      uu____10963) in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____10943 in
                                                mk1 uu____10942 in
                                              let p2 =
                                                let uu____11042 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats [(p1, false)])))
                                                  uu____11042 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____11089 ->
                                              failwith "Impossible") in
                                   ((x, aq), sc_pat_opt1) in
                             (match uu____10472 with
                              | (b1, sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest)) in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____11183, uu____11184, FStar_Parser_AST.UnivApp) ->
            let rec aux universes e =
              let uu____11206 =
                let uu____11207 = unparen e in
                uu____11207.FStar_Parser_AST.tm in
              match uu____11206 with
              | FStar_Parser_AST.App (e1, t, FStar_Parser_AST.UnivApp) ->
                  let univ_arg = desugar_universe t in
                  aux (univ_arg :: universes) e1
              | uu____11217 ->
                  let uu____11218 = desugar_term_aq env e in
                  (match uu____11218 with
                   | (head1, aq) ->
                       let uu____11231 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes)) in
                       (uu____11231, aq)) in
            aux [] top
        | FStar_Parser_AST.App uu____11238 ->
            let rec aux args aqs e =
              let uu____11315 =
                let uu____11316 = unparen e in
                uu____11316.FStar_Parser_AST.tm in
              match uu____11315 with
              | FStar_Parser_AST.App (e1, t, imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____11334 = desugar_term_aq env t in
                  (match uu____11334 with
                   | (t1, aq) ->
                       let arg = arg_withimp_e imp t1 in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____11382 ->
                  let uu____11383 = desugar_term_aq env e in
                  (match uu____11383 with
                   | (head1, aq) ->
                       let uu____11404 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args)) in
                       (uu____11404, (join_aqs (aq :: aqs)))) in
            aux [] [] top
        | FStar_Parser_AST.Bind (x, t1, t2) ->
            let xpat =
              FStar_Parser_AST.mk_pattern
                (FStar_Parser_AST.PatVar (x, FStar_Pervasives_Native.None))
                x.FStar_Ident.idRange in
            let k =
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Abs ([xpat], t2))
                t2.FStar_Parser_AST.range t2.FStar_Parser_AST.level in
            let bind_lid =
              FStar_Ident.lid_of_path ["bind"] x.FStar_Ident.idRange in
            let bind1 =
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Var bind_lid)
                x.FStar_Ident.idRange FStar_Parser_AST.Expr in
            let uu____11467 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range in
            desugar_term_aq env uu____11467
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
            let uu____11519 = desugar_term_aq env t in
            (match uu____11519 with
             | (tm, s) ->
                 let uu____11530 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence))) in
                 (uu____11530, s))
        | FStar_Parser_AST.LetOpen (lid, e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid in
            let uu____11536 =
              let uu____11549 = FStar_Syntax_DsEnv.expect_typ env1 in
              if uu____11549 then desugar_typ_aq else desugar_term_aq in
            uu____11536 env1 e
        | FStar_Parser_AST.Let (qual, lbs, body) ->
            let is_rec = qual = FStar_Parser_AST.Rec in
            let ds_let_rec_or_app uu____11616 =
              let bindings = lbs in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____11759 ->
                        match uu____11759 with
                        | (attr_opt, (p, def)) ->
                            let uu____11817 = is_app_pattern p in
                            if uu____11817
                            then
                              let uu____11850 =
                                destruct_app_pattern env top_level p in
                              (attr_opt, uu____11850, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1, def1) ->
                                   let uu____11933 =
                                     destruct_app_pattern env top_level p1 in
                                   (attr_opt, uu____11933, def1)
                               | uu____11978 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1, uu____12016);
                                           FStar_Parser_AST.prange =
                                             uu____12017;_},
                                         t)
                                        ->
                                        if top_level
                                        then
                                          let uu____12066 =
                                            let uu____12087 =
                                              let uu____12092 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1 in
                                              FStar_Util.Inr uu____12092 in
                                            (uu____12087, [],
                                              (FStar_Pervasives_Native.Some t)) in
                                          (attr_opt, uu____12066, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1, uu____12184) ->
                                        if top_level
                                        then
                                          let uu____12220 =
                                            let uu____12241 =
                                              let uu____12246 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1 in
                                              FStar_Util.Inr uu____12246 in
                                            (uu____12241, [],
                                              FStar_Pervasives_Native.None) in
                                          (attr_opt, uu____12220, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____12337 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange)))) in
              let uu____12370 =
                FStar_List.fold_left
                  (fun uu____12459 ->
                     fun uu____12460 ->
                       match (uu____12459, uu____12460) with
                       | ((env1, fnames, rec_bindings, used_markers),
                          (_attr_opt, (f, uu____12590, uu____12591),
                           uu____12592)) ->
                           let uu____12726 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____12766 =
                                   FStar_Syntax_DsEnv.push_bv' env1 x in
                                 (match uu____12766 with
                                  | (env2, xx, used_marker) ->
                                      let dummy_ref = FStar_Util.mk_ref true in
                                      let uu____12801 =
                                        let uu____12804 =
                                          FStar_Syntax_Syntax.mk_binder xx in
                                        uu____12804 :: rec_bindings in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____12801, (used_marker ::
                                        used_markers)))
                             | FStar_Util.Inr l ->
                                 let uu____12820 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.delta_equational in
                                 (match uu____12820 with
                                  | (env2, used_marker) ->
                                      (env2, (FStar_Util.Inr l),
                                        rec_bindings, (used_marker ::
                                        used_markers))) in
                           (match uu____12726 with
                            | (env2, lbname, rec_bindings1, used_markers1) ->
                                (env2, (lbname :: fnames), rec_bindings1,
                                  used_markers1))) (env, [], [], []) funs in
              match uu____12370 with
              | (env', fnames, rec_bindings, used_markers) ->
                  let fnames1 = FStar_List.rev fnames in
                  let rec_bindings1 = FStar_List.rev rec_bindings in
                  let used_markers1 = FStar_List.rev used_markers in
                  let desugar_one_def env1 lbname uu____13073 =
                    match uu____13073 with
                    | (attrs_opt, (uu____13113, args, result_t), def) ->
                        let args1 =
                          FStar_All.pipe_right args
                            (FStar_List.map replace_unit_pattern) in
                        let pos = def.FStar_Parser_AST.range in
                        let def1 =
                          match result_t with
                          | FStar_Pervasives_Native.None -> def
                          | FStar_Pervasives_Native.Some (t, tacopt) ->
                              let t1 =
                                let uu____13205 = is_comp_type env1 t in
                                if uu____13205
                                then
                                  ((let uu____13209 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x ->
                                              let uu____13219 =
                                                is_var_pattern x in
                                              Prims.op_Negation uu____13219)) in
                                    match uu____13209 with
                                    | FStar_Pervasives_Native.None -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____13226 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____13229 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid in
                                         FStar_Option.isSome uu____13229))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             Prims.int_zero)) in
                                   if uu____13226
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t) in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed (def, t1, tacopt))
                                def.FStar_Parser_AST.range
                                FStar_Parser_AST.Expr in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____13240 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level in
                        let uu____13243 = desugar_term_aq env1 def2 in
                        (match uu____13243 with
                         | (body1, aq) ->
                             let lbname1 =
                               match lbname with
                               | FStar_Util.Inl x -> FStar_Util.Inl x
                               | FStar_Util.Inr l ->
                                   let uu____13265 =
                                     let uu____13266 =
                                       FStar_Syntax_Util.incr_delta_qualifier
                                         body1 in
                                     FStar_Syntax_Syntax.lid_as_fv l
                                       uu____13266
                                       FStar_Pervasives_Native.None in
                                   FStar_Util.Inr uu____13265 in
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
                                 (attrs, lbname1, FStar_Syntax_Syntax.tun,
                                   body2, pos)), aq)) in
                  let uu____13307 =
                    let uu____13324 =
                      FStar_List.map2
                        (desugar_one_def (if is_rec then env' else env))
                        fnames1 funs in
                    FStar_All.pipe_right uu____13324 FStar_List.unzip in
                  (match uu____13307 with
                   | (lbs1, aqss) ->
                       let uu____13466 = desugar_term_aq env' body in
                       (match uu____13466 with
                        | (body1, aq) ->
                            (if is_rec
                             then
                               FStar_List.iter2
                                 (fun uu____13572 ->
                                    fun used_marker ->
                                      match uu____13572 with
                                      | (_attr_opt,
                                         (f, uu____13646, uu____13647),
                                         uu____13648) ->
                                          let uu____13705 =
                                            let uu____13707 =
                                              FStar_ST.op_Bang used_marker in
                                            Prims.op_Negation uu____13707 in
                                          if uu____13705
                                          then
                                            let uu____13731 =
                                              match f with
                                              | FStar_Util.Inl x ->
                                                  let uu____13749 =
                                                    FStar_Ident.string_of_ident
                                                      x in
                                                  let uu____13751 =
                                                    FStar_Ident.range_of_id x in
                                                  (uu____13749, "Local",
                                                    uu____13751)
                                              | FStar_Util.Inr l ->
                                                  let uu____13756 =
                                                    FStar_Ident.string_of_lid
                                                      l in
                                                  let uu____13758 =
                                                    FStar_Ident.range_of_lid
                                                      l in
                                                  (uu____13756, "Global",
                                                    uu____13758) in
                                            (match uu____13731 with
                                             | (nm, gl, rng) ->
                                                 let uu____13769 =
                                                   let uu____13775 =
                                                     FStar_Util.format2
                                                       "%s binding %s is recursive but not used in its body"
                                                       gl nm in
                                                   (FStar_Errors.Warning_UnusedLetRec,
                                                     uu____13775) in
                                                 FStar_Errors.log_issue rng
                                                   uu____13769)
                                          else ()) funs used_markers1
                             else ();
                             (let uu____13783 =
                                let uu____13786 =
                                  let uu____13787 =
                                    let uu____13801 =
                                      FStar_Syntax_Subst.close rec_bindings1
                                        body1 in
                                    ((is_rec, lbs1), uu____13801) in
                                  FStar_Syntax_Syntax.Tm_let uu____13787 in
                                FStar_All.pipe_left mk1 uu____13786 in
                              (uu____13783,
                                (FStar_List.append aq
                                   (FStar_List.flatten aqss))))))) in
            let ds_non_rec attrs_opt pat t1 t2 =
              let attrs =
                match attrs_opt with
                | FStar_Pervasives_Native.None -> []
                | FStar_Pervasives_Native.Some l ->
                    FStar_List.map (desugar_term env) l in
              let uu____13903 = desugar_term_aq env t1 in
              match uu____13903 with
              | (t11, aq0) ->
                  let uu____13924 =
                    desugar_binding_pat_maybe_top top_level env pat in
                  (match uu____13924 with
                   | (env1, binder, pat1) ->
                       let uu____13954 =
                         match binder with
                         | LetBinder (l, (t, _tacopt)) ->
                             let uu____13996 = desugar_term_aq env1 t2 in
                             (match uu____13996 with
                              | (body1, aq) ->
                                  let fv =
                                    let uu____14018 =
                                      FStar_Syntax_Util.incr_delta_qualifier
                                        t11 in
                                    FStar_Syntax_Syntax.lid_as_fv l
                                      uu____14018
                                      FStar_Pervasives_Native.None in
                                  let uu____14019 =
                                    FStar_All.pipe_left mk1
                                      (FStar_Syntax_Syntax.Tm_let
                                         ((false,
                                            [mk_lb
                                               (attrs, (FStar_Util.Inr fv),
                                                 t, t11,
                                                 (t11.FStar_Syntax_Syntax.pos))]),
                                           body1)) in
                                  (uu____14019, aq))
                         | LocalBinder (x, uu____14060) ->
                             let uu____14061 = desugar_term_aq env1 t2 in
                             (match uu____14061 with
                              | (body1, aq) ->
                                  let body2 =
                                    match pat1 with
                                    | [] -> body1
                                    | ({
                                         FStar_Syntax_Syntax.v =
                                           FStar_Syntax_Syntax.Pat_wild
                                           uu____14083;
                                         FStar_Syntax_Syntax.p = uu____14084;_},
                                       uu____14085)::[] -> body1
                                    | uu____14098 ->
                                        let uu____14101 =
                                          let uu____14108 =
                                            let uu____14109 =
                                              let uu____14132 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  x in
                                              let uu____14135 =
                                                desugar_disjunctive_pattern
                                                  pat1
                                                  FStar_Pervasives_Native.None
                                                  body1 in
                                              (uu____14132, uu____14135) in
                                            FStar_Syntax_Syntax.Tm_match
                                              uu____14109 in
                                          FStar_Syntax_Syntax.mk uu____14108 in
                                        uu____14101
                                          FStar_Pervasives_Native.None
                                          top.FStar_Parser_AST.range in
                                  let uu____14172 =
                                    let uu____14175 =
                                      let uu____14176 =
                                        let uu____14190 =
                                          let uu____14193 =
                                            let uu____14194 =
                                              FStar_Syntax_Syntax.mk_binder x in
                                            [uu____14194] in
                                          FStar_Syntax_Subst.close
                                            uu____14193 body2 in
                                        ((false,
                                           [mk_lb
                                              (attrs, (FStar_Util.Inl x),
                                                (x.FStar_Syntax_Syntax.sort),
                                                t11,
                                                (t11.FStar_Syntax_Syntax.pos))]),
                                          uu____14190) in
                                      FStar_Syntax_Syntax.Tm_let uu____14176 in
                                    FStar_All.pipe_left mk1 uu____14175 in
                                  (uu____14172, aq)) in
                       (match uu____13954 with
                        | (tm, aq1) -> (tm, (FStar_List.append aq0 aq1)))) in
            let uu____14302 = FStar_List.hd lbs in
            (match uu____14302 with
             | (attrs, (head_pat, defn)) ->
                 let uu____14346 = is_rec || (is_app_pattern head_pat) in
                 if uu____14346
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1, t2, t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun in
            let t_bool1 =
              let uu____14362 =
                let uu____14363 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None in
                FStar_Syntax_Syntax.Tm_fvar uu____14363 in
              mk1 uu____14362 in
            let uu____14364 = desugar_term_aq env t1 in
            (match uu____14364 with
             | (t1', aq1) ->
                 let uu____14375 = desugar_term_aq env t2 in
                 (match uu____14375 with
                  | (t2', aq2) ->
                      let uu____14386 = desugar_term_aq env t3 in
                      (match uu____14386 with
                       | (t3', aq3) ->
                           let uu____14397 =
                             let uu____14398 =
                               let uu____14399 =
                                 let uu____14422 =
                                   let uu____14439 =
                                     let uu____14454 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t1.FStar_Parser_AST.range in
                                     (uu____14454,
                                       FStar_Pervasives_Native.None, t2') in
                                   let uu____14468 =
                                     let uu____14485 =
                                       let uu____14500 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t1.FStar_Parser_AST.range in
                                       (uu____14500,
                                         FStar_Pervasives_Native.None, t3') in
                                     [uu____14485] in
                                   uu____14439 :: uu____14468 in
                                 (t1', uu____14422) in
                               FStar_Syntax_Syntax.Tm_match uu____14399 in
                             mk1 uu____14398 in
                           (uu____14397, (join_aqs [aq1; aq2; aq3])))))
        | FStar_Parser_AST.TryWith (e, branches) ->
            let r = top.FStar_Parser_AST.range in
            let handler = FStar_Parser_AST.mk_function branches r r in
            let body =
              FStar_Parser_AST.mk_function
                [((FStar_Parser_AST.mk_pattern
                     (FStar_Parser_AST.PatConst FStar_Const.Const_unit) r),
                   FStar_Pervasives_Native.None, e)] r r in
            let try_with_lid1 = FStar_Ident.lid_of_path ["try_with"] r in
            let try_with1 =
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Var try_with_lid1) r
                FStar_Parser_AST.Expr in
            let a1 =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   (try_with1, body, FStar_Parser_AST.Nothing)) r
                top.FStar_Parser_AST.level in
            let a2 =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App (a1, handler, FStar_Parser_AST.Nothing))
                r top.FStar_Parser_AST.level in
            desugar_term_aq env a2
        | FStar_Parser_AST.Match (e, branches) ->
            let desugar_branch uu____14696 =
              match uu____14696 with
              | (pat, wopt, b) ->
                  let uu____14718 = desugar_match_pat env pat in
                  (match uu____14718 with
                   | (env1, pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____14749 = desugar_term env1 e1 in
                             FStar_Pervasives_Native.Some uu____14749 in
                       let uu____14754 = desugar_term_aq env1 b in
                       (match uu____14754 with
                        | (b1, aq) ->
                            let uu____14767 =
                              desugar_disjunctive_pattern pat1 wopt1 b1 in
                            (uu____14767, aq))) in
            let uu____14772 = desugar_term_aq env e in
            (match uu____14772 with
             | (e1, aq) ->
                 let uu____14783 =
                   let uu____14814 =
                     let uu____14847 = FStar_List.map desugar_branch branches in
                     FStar_All.pipe_right uu____14847 FStar_List.unzip in
                   FStar_All.pipe_right uu____14814
                     (fun uu____15065 ->
                        match uu____15065 with
                        | (x, y) -> ((FStar_List.flatten x), y)) in
                 (match uu____14783 with
                  | (brs, aqs) ->
                      let uu____15284 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs)) in
                      (uu____15284, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e, t, tac_opt) ->
            let uu____15318 =
              let uu____15339 = is_comp_type env t in
              if uu____15339
              then
                let comp = desugar_comp t.FStar_Parser_AST.range true env t in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____15394 = desugar_term_aq env t in
                 match uu____15394 with
                 | (tm, aq) -> ((FStar_Util.Inl tm), aq)) in
            (match uu____15318 with
             | (annot, aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env) in
                 let uu____15486 = desugar_term_aq env e in
                 (match uu____15486 with
                  | (e1, aq) ->
                      let uu____15497 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None)) in
                      (uu____15497, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____15536, []) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt, fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range in
            let user_ns =
              let uu____15579 = FStar_List.hd fields in
              match uu____15579 with | (f, uu____15591) -> f.FStar_Ident.ns in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____15637 ->
                        match uu____15637 with
                        | (g, uu____15644) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText)) in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f]) in
              match found with
              | FStar_Pervasives_Native.Some (uu____15651, e) -> (fn, e)
              | FStar_Pervasives_Native.None ->
                  (match xopt with
                   | FStar_Pervasives_Native.None ->
                       let uu____15665 =
                         let uu____15671 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____15671) in
                       FStar_Errors.raise_error uu____15665
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
                  let uu____15682 =
                    let uu____15693 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____15724 ->
                              match uu____15724 with
                              | (f, uu____15734) ->
                                  let uu____15735 =
                                    let uu____15736 =
                                      get_field FStar_Pervasives_Native.None
                                        f in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____15736 in
                                  (uu____15735, FStar_Parser_AST.Nothing))) in
                    (user_constrname, uu____15693) in
                  FStar_Parser_AST.Construct uu____15682
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range in
                  let xterm =
                    let uu____15754 =
                      let uu____15755 = FStar_Ident.lid_of_ids [x] in
                      FStar_Parser_AST.Var uu____15755 in
                    FStar_Parser_AST.mk_term uu____15754
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr in
                  let record1 =
                    let uu____15757 =
                      let uu____15770 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____15800 ->
                                match uu____15800 with
                                | (f, uu____15810) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f)) in
                      (FStar_Pervasives_Native.None, uu____15770) in
                    FStar_Parser_AST.Record uu____15757 in
                  FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier,
                      [(FStar_Pervasives_Native.None,
                         ((FStar_Parser_AST.mk_pattern
                             (FStar_Parser_AST.PatVar
                                (x, FStar_Pervasives_Native.None))
                             x.FStar_Ident.idRange), e))],
                      (FStar_Parser_AST.mk_term record1
                         top.FStar_Parser_AST.range
                         top.FStar_Parser_AST.level)) in
            let recterm1 =
              FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level in
            let uu____15870 = desugar_term_aq env recterm1 in
            (match uu____15870 with
             | (e, s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____15886;
                         FStar_Syntax_Syntax.vars = uu____15887;_},
                       args)
                      ->
                      let uu____15913 =
                        let uu____15914 =
                          let uu____15915 =
                            let uu____15932 =
                              let uu____15935 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos in
                              let uu____15936 =
                                let uu____15939 =
                                  let uu____15940 =
                                    let uu____15947 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst) in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____15947) in
                                  FStar_Syntax_Syntax.Record_ctor uu____15940 in
                                FStar_Pervasives_Native.Some uu____15939 in
                              FStar_Syntax_Syntax.fvar uu____15935
                                FStar_Syntax_Syntax.delta_constant
                                uu____15936 in
                            (uu____15932, args) in
                          FStar_Syntax_Syntax.Tm_app uu____15915 in
                        FStar_All.pipe_left mk1 uu____15914 in
                      (uu____15913, s)
                  | uu____15976 -> (e, s)))
        | FStar_Parser_AST.Project (e, f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____15980 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f in
              match uu____15980 with
              | (constrname, is_rec) ->
                  let uu____15999 = desugar_term_aq env e in
                  (match uu____15999 with
                   | (e1, s) ->
                       let projname =
                         FStar_Syntax_Util.mk_field_projector_name_from_ident
                           constrname f.FStar_Ident.ident in
                       let qual =
                         if is_rec
                         then
                           FStar_Pervasives_Native.Some
                             (FStar_Syntax_Syntax.Record_projector
                                (constrname, (f.FStar_Ident.ident)))
                         else FStar_Pervasives_Native.None in
                       let uu____16019 =
                         let uu____16020 =
                           let uu____16021 =
                             let uu____16038 =
                               let uu____16041 =
                                 let uu____16042 = FStar_Ident.range_of_lid f in
                                 FStar_Ident.set_lid_range projname
                                   uu____16042 in
                               FStar_Syntax_Syntax.fvar uu____16041
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    Prims.int_one) qual in
                             let uu____16044 =
                               let uu____16055 =
                                 FStar_Syntax_Syntax.as_arg e1 in
                               [uu____16055] in
                             (uu____16038, uu____16044) in
                           FStar_Syntax_Syntax.Tm_app uu____16021 in
                         FStar_All.pipe_left mk1 uu____16020 in
                       (uu____16019, s))))
        | FStar_Parser_AST.NamedTyp (uu____16092, e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e in
            let uu____16102 =
              let uu____16103 = FStar_Syntax_Subst.compress tm in
              uu____16103.FStar_Syntax_Syntax.n in
            (match uu____16102 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____16111 =
                   let uu___2111_16112 =
                     let uu____16113 =
                       let uu____16115 = FStar_Syntax_Syntax.lid_of_fv fv in
                       FStar_Ident.string_of_lid uu____16115 in
                     FStar_Syntax_Util.exp_string uu____16113 in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___2111_16112.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___2111_16112.FStar_Syntax_Syntax.vars)
                   } in
                 (uu____16111, noaqs)
             | uu____16116 ->
                 let uu____16117 =
                   let uu____16123 =
                     let uu____16125 = FStar_Syntax_Print.term_to_string tm in
                     Prims.op_Hat "VQuote, expected an fvar, got: "
                       uu____16125 in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____16123) in
                 FStar_Errors.raise_error uu____16117
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e, FStar_Parser_AST.Static) ->
            let uu____16134 = desugar_term_aq env e in
            (match uu____16134 with
             | (tm, vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   } in
                 let uu____16146 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi)) in
                 (uu____16146, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun in
            let uu____16151 = FStar_Syntax_Syntax.bv_to_name bv in
            let uu____16152 =
              let uu____16153 =
                let uu____16160 = desugar_term env e in (bv, uu____16160) in
              [uu____16153] in
            (uu____16151, uu____16152)
        | FStar_Parser_AST.Quote (e, FStar_Parser_AST.Dynamic) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              } in
            let uu____16185 =
              let uu____16186 =
                let uu____16187 =
                  let uu____16194 = desugar_term env e in (uu____16194, qi) in
                FStar_Syntax_Syntax.Tm_quoted uu____16187 in
              FStar_All.pipe_left mk1 uu____16186 in
            (uu____16185, noaqs)
        | FStar_Parser_AST.CalcProof (rel, init_expr, steps) ->
            let eta_and_annot rel1 =
              let x = FStar_Ident.gen rel1.FStar_Parser_AST.range in
              let y = FStar_Ident.gen rel1.FStar_Parser_AST.range in
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
              let uu____16223 =
                let uu____16224 =
                  let uu____16231 =
                    let uu____16232 =
                      let uu____16233 =
                        let uu____16242 =
                          FStar_Parser_AST.mkApp rel1
                            [(xt, FStar_Parser_AST.Nothing);
                            (yt, FStar_Parser_AST.Nothing)]
                            rel1.FStar_Parser_AST.range in
                        let uu____16255 =
                          let uu____16256 =
                            let uu____16257 = FStar_Ident.lid_of_str "Type0" in
                            FStar_Parser_AST.Name uu____16257 in
                          FStar_Parser_AST.mk_term uu____16256
                            rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr in
                        (uu____16242, uu____16255,
                          FStar_Pervasives_Native.None) in
                      FStar_Parser_AST.Ascribed uu____16233 in
                    FStar_Parser_AST.mk_term uu____16232
                      rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr in
                  (pats, uu____16231) in
                FStar_Parser_AST.Abs uu____16224 in
              FStar_Parser_AST.mk_term uu____16223
                rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr in
            let rel1 = eta_and_annot rel in
            let wild r =
              FStar_Parser_AST.mk_term FStar_Parser_AST.Wild r
                FStar_Parser_AST.Expr in
            let init1 =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Var FStar_Parser_Const.calc_init_lid)
                FStar_Range.dummyRange FStar_Parser_AST.Expr in
            let last_expr =
              let uu____16272 = FStar_List.last steps in
              match uu____16272 with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.CalcStep
                  (uu____16275, uu____16276, last_expr)) -> last_expr
              | uu____16278 -> failwith "impossible: no last_expr on calc" in
            let step r =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Var FStar_Parser_Const.calc_step_lid) r
                FStar_Parser_AST.Expr in
            let finish1 =
              FStar_Parser_AST.mkApp
                (FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Var FStar_Parser_Const.calc_finish_lid)
                   top.FStar_Parser_AST.range FStar_Parser_AST.Expr)
                [(rel1, FStar_Parser_AST.Nothing)] top.FStar_Parser_AST.range in
            let e =
              FStar_Parser_AST.mkApp init1
                [(init_expr, FStar_Parser_AST.Nothing)]
                FStar_Range.dummyRange in
            let uu____16306 =
              FStar_List.fold_left
                (fun uu____16323 ->
                   fun uu____16324 ->
                     match (uu____16323, uu____16324) with
                     | ((e1, prev), FStar_Parser_AST.CalcStep
                        (rel2, just, next_expr)) ->
                         let pf =
                           let uu____16347 =
                             let uu____16354 =
                               let uu____16361 =
                                 let uu____16368 =
                                   let uu____16375 =
                                     let uu____16380 = eta_and_annot rel2 in
                                     (uu____16380, FStar_Parser_AST.Nothing) in
                                   let uu____16381 =
                                     let uu____16388 =
                                       let uu____16395 =
                                         let uu____16400 =
                                           FStar_Parser_AST.thunk e1 in
                                         (uu____16400,
                                           FStar_Parser_AST.Nothing) in
                                       let uu____16401 =
                                         let uu____16408 =
                                           let uu____16413 =
                                             FStar_Parser_AST.thunk just in
                                           (uu____16413,
                                             FStar_Parser_AST.Nothing) in
                                         [uu____16408] in
                                       uu____16395 :: uu____16401 in
                                     (next_expr, FStar_Parser_AST.Nothing) ::
                                       uu____16388 in
                                   uu____16375 :: uu____16381 in
                                 (prev, FStar_Parser_AST.Hash) :: uu____16368 in
                               (init_expr, FStar_Parser_AST.Hash) ::
                                 uu____16361 in
                             ((wild rel2.FStar_Parser_AST.range),
                               FStar_Parser_AST.Hash) :: uu____16354 in
                           FStar_Parser_AST.mkApp
                             (step rel2.FStar_Parser_AST.range) uu____16347
                             FStar_Range.dummyRange in
                         (pf, next_expr)) (e, init_expr) steps in
            (match uu____16306 with
             | (e1, uu____16451) ->
                 let e2 =
                   let uu____16453 =
                     let uu____16460 =
                       let uu____16467 =
                         let uu____16474 =
                           let uu____16479 = FStar_Parser_AST.thunk e1 in
                           (uu____16479, FStar_Parser_AST.Nothing) in
                         [uu____16474] in
                       (last_expr, FStar_Parser_AST.Hash) :: uu____16467 in
                     (init_expr, FStar_Parser_AST.Hash) :: uu____16460 in
                   FStar_Parser_AST.mkApp finish1 uu____16453
                     FStar_Range.dummyRange in
                 desugar_term_maybe_top top_level env e2)
        | uu____16496 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____16497 = desugar_formula env top in (uu____16497, noaqs)
        | uu____16498 ->
            let uu____16499 =
              let uu____16505 =
                let uu____16507 = FStar_Parser_AST.term_to_string top in
                Prims.op_Hat "Unexpected term: " uu____16507 in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____16505) in
            FStar_Errors.raise_error uu____16499 top.FStar_Parser_AST.range
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
           (fun uu____16551 ->
              match uu____16551 with
              | (a, imp) ->
                  let uu____16564 = desugar_term env a in
                  arg_withimp_e imp uu____16564))
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
          let fail1 err = FStar_Errors.raise_error err r in
          let is_requires uu____16601 =
            match uu____16601 with
            | (t1, uu____16608) ->
                let uu____16609 =
                  let uu____16610 = unparen t1 in
                  uu____16610.FStar_Parser_AST.tm in
                (match uu____16609 with
                 | FStar_Parser_AST.Requires uu____16612 -> true
                 | uu____16621 -> false) in
          let is_ensures uu____16633 =
            match uu____16633 with
            | (t1, uu____16640) ->
                let uu____16641 =
                  let uu____16642 = unparen t1 in
                  uu____16642.FStar_Parser_AST.tm in
                (match uu____16641 with
                 | FStar_Parser_AST.Ensures uu____16644 -> true
                 | uu____16653 -> false) in
          let is_app head1 uu____16671 =
            match uu____16671 with
            | (t1, uu____16679) ->
                let uu____16680 =
                  let uu____16681 = unparen t1 in
                  uu____16681.FStar_Parser_AST.tm in
                (match uu____16680 with
                 | FStar_Parser_AST.App
                     ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                        FStar_Parser_AST.range = uu____16684;
                        FStar_Parser_AST.level = uu____16685;_},
                      uu____16686, uu____16687)
                     -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
                 | uu____16689 -> false) in
          let is_smt_pat uu____16701 =
            match uu____16701 with
            | (t1, uu____16708) ->
                let uu____16709 =
                  let uu____16710 = unparen t1 in
                  uu____16710.FStar_Parser_AST.tm in
                (match uu____16709 with
                 | FStar_Parser_AST.Construct
                     (cons1,
                      ({
                         FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                           (smtpat, uu____16714);
                         FStar_Parser_AST.range = uu____16715;
                         FStar_Parser_AST.level = uu____16716;_},
                       uu____16717)::uu____16718::[])
                     ->
                     (FStar_Ident.lid_equals cons1
                        FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s -> smtpat.FStar_Ident.str = s)
                          ["SMTPat"; "SMTPatT"; "SMTPatOr"])
                 | FStar_Parser_AST.Construct
                     (cons1,
                      ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var smtpat;
                         FStar_Parser_AST.range = uu____16767;
                         FStar_Parser_AST.level = uu____16768;_},
                       uu____16769)::uu____16770::[])
                     ->
                     (FStar_Ident.lid_equals cons1
                        FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s -> smtpat.FStar_Ident.str = s)
                          ["smt_pat"; "smt_pat_or"])
                 | uu____16803 -> false) in
          let is_decreases = is_app "decreases" in
          let pre_process_comp_typ t1 =
            let uu____16838 = head_and_args t1 in
            match uu____16838 with
            | (head1, args) ->
                (match head1.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Name lemma when
                     (lemma.FStar_Ident.ident).FStar_Ident.idText = "Lemma"
                     ->
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
                     let thunk_ens uu____16931 =
                       match uu____16931 with
                       | (e, i) ->
                           let uu____16942 = FStar_Parser_AST.thunk e in
                           (uu____16942, i) in
                     let fail_lemma uu____16954 =
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
                           let uu____17060 =
                             let uu____17067 =
                               let uu____17074 = thunk_ens ens in
                               [uu____17074; nil_pat] in
                             req_true :: uu____17067 in
                           unit_tm :: uu____17060
                       | req::ens::[] when
                           (is_requires req) && (is_ensures ens) ->
                           let uu____17121 =
                             let uu____17128 =
                               let uu____17135 = thunk_ens ens in
                               [uu____17135; nil_pat] in
                             req :: uu____17128 in
                           unit_tm :: uu____17121
                       | ens::smtpat::[] when
                           (((let uu____17184 = is_requires ens in
                              Prims.op_Negation uu____17184) &&
                               (let uu____17187 = is_smt_pat ens in
                                Prims.op_Negation uu____17187))
                              &&
                              (let uu____17190 = is_decreases ens in
                               Prims.op_Negation uu____17190))
                             && (is_smt_pat smtpat)
                           ->
                           let uu____17192 =
                             let uu____17199 =
                               let uu____17206 = thunk_ens ens in
                               [uu____17206; smtpat] in
                             req_true :: uu____17199 in
                           unit_tm :: uu____17192
                       | ens::dec::[] when
                           (is_ensures ens) && (is_decreases dec) ->
                           let uu____17253 =
                             let uu____17260 =
                               let uu____17267 = thunk_ens ens in
                               [uu____17267; nil_pat; dec] in
                             req_true :: uu____17260 in
                           unit_tm :: uu____17253
                       | ens::dec::smtpat::[] when
                           ((is_ensures ens) && (is_decreases dec)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____17327 =
                             let uu____17334 =
                               let uu____17341 = thunk_ens ens in
                               [uu____17341; smtpat; dec] in
                             req_true :: uu____17334 in
                           unit_tm :: uu____17327
                       | req::ens::dec::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_decreases dec)
                           ->
                           let uu____17401 =
                             let uu____17408 =
                               let uu____17415 = thunk_ens ens in
                               [uu____17415; nil_pat; dec] in
                             req :: uu____17408 in
                           unit_tm :: uu____17401
                       | req::ens::smtpat::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____17475 =
                             let uu____17482 =
                               let uu____17489 = thunk_ens ens in
                               [uu____17489; smtpat] in
                             req :: uu____17482 in
                           unit_tm :: uu____17475
                       | req::ens::dec::smtpat::[] when
                           (((is_requires req) && (is_ensures ens)) &&
                              (is_smt_pat smtpat))
                             && (is_decreases dec)
                           ->
                           let uu____17554 =
                             let uu____17561 =
                               let uu____17568 = thunk_ens ens in
                               [uu____17568; dec; smtpat] in
                             req :: uu____17561 in
                           unit_tm :: uu____17554
                       | _other -> fail_lemma () in
                     let head_and_attributes =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) lemma in
                     (head_and_attributes, args1)
                 | FStar_Parser_AST.Name l when
                     FStar_Syntax_DsEnv.is_effect_name env l ->
                     let uu____17630 =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) l in
                     (uu____17630, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____17658 = FStar_Syntax_DsEnv.current_module env in
                      FStar_Ident.lid_equals uu____17658
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                     ->
                     let uu____17661 =
                       let uu____17668 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range in
                       (uu____17668, []) in
                     (uu____17661, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____17686 = FStar_Syntax_DsEnv.current_module env in
                      FStar_Ident.lid_equals uu____17686
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                     ->
                     let uu____17689 =
                       let uu____17696 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_GTot_lid
                           head1.FStar_Parser_AST.range in
                       (uu____17696, []) in
                     (uu____17689, args)
                 | FStar_Parser_AST.Name l when
                     (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                        ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                       ||
                       ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                     ->
                     let uu____17718 =
                       let uu____17725 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range in
                       (uu____17725, []) in
                     (uu____17718, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17748 when allow_type_promotion ->
                     let default_effect =
                       let uu____17750 = FStar_Options.ml_ish () in
                       if uu____17750
                       then FStar_Parser_Const.effect_ML_lid
                       else
                         ((let uu____17756 =
                             FStar_Options.warn_default_effects () in
                           if uu____17756
                           then
                             FStar_Errors.log_issue
                               head1.FStar_Parser_AST.range
                               (FStar_Errors.Warning_UseDefaultEffect,
                                 "Using default effect Tot")
                           else ());
                          FStar_Parser_Const.effect_Tot_lid) in
                     let uu____17763 =
                       let uu____17770 =
                         FStar_Ident.set_lid_range default_effect
                           head1.FStar_Parser_AST.range in
                       (uu____17770, []) in
                     (uu____17763, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17793 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_EffectNotFound,
                         "Expected an effect constructor")
                       t1.FStar_Parser_AST.range) in
          let uu____17812 = pre_process_comp_typ t in
          match uu____17812 with
          | ((eff, cattributes), args) ->
              (if (FStar_List.length args) = Prims.int_zero
               then
                 (let uu____17864 =
                    let uu____17870 =
                      let uu____17872 = FStar_Syntax_Print.lid_to_string eff in
                      FStar_Util.format1 "Not enough args to effect %s"
                        uu____17872 in
                    (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____17870) in
                  fail1 uu____17864)
               else ();
               (let is_universe uu____17888 =
                  match uu____17888 with
                  | (uu____17894, imp) -> imp = FStar_Parser_AST.UnivApp in
                let uu____17896 = FStar_Util.take is_universe args in
                match uu____17896 with
                | (universes, args1) ->
                    let universes1 =
                      FStar_List.map
                        (fun uu____17955 ->
                           match uu____17955 with
                           | (u, imp) -> desugar_universe u) universes in
                    let uu____17962 =
                      let uu____17977 = FStar_List.hd args1 in
                      let uu____17986 = FStar_List.tl args1 in
                      (uu____17977, uu____17986) in
                    (match uu____17962 with
                     | (result_arg, rest) ->
                         let result_typ =
                           desugar_typ env
                             (FStar_Pervasives_Native.fst result_arg) in
                         let rest1 = desugar_args env rest in
                         let uu____18041 =
                           let is_decrease uu____18080 =
                             match uu____18080 with
                             | (t1, uu____18091) ->
                                 (match t1.FStar_Syntax_Syntax.n with
                                  | FStar_Syntax_Syntax.Tm_app
                                      ({
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_fvar fv;
                                         FStar_Syntax_Syntax.pos =
                                           uu____18102;
                                         FStar_Syntax_Syntax.vars =
                                           uu____18103;_},
                                       uu____18104::[])
                                      ->
                                      FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Parser_Const.decreases_lid
                                  | uu____18143 -> false) in
                           FStar_All.pipe_right rest1
                             (FStar_List.partition is_decrease) in
                         (match uu____18041 with
                          | (dec, rest2) ->
                              let decreases_clause =
                                FStar_All.pipe_right dec
                                  (FStar_List.map
                                     (fun uu____18260 ->
                                        match uu____18260 with
                                        | (t1, uu____18270) ->
                                            (match t1.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____18279,
                                                  (arg, uu____18281)::[])
                                                 ->
                                                 FStar_Syntax_Syntax.DECREASES
                                                   arg
                                             | uu____18320 ->
                                                 failwith "impos"))) in
                              let no_additional_args =
                                let is_empty l =
                                  match l with
                                  | [] -> true
                                  | uu____18341 -> false in
                                (((is_empty decreases_clause) &&
                                    (is_empty rest2))
                                   && (is_empty cattributes))
                                  && (is_empty universes1) in
                              let uu____18353 =
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_Tot_lid) in
                              if uu____18353
                              then FStar_Syntax_Syntax.mk_Total result_typ
                              else
                                (let uu____18360 =
                                   no_additional_args &&
                                     (FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_GTot_lid) in
                                 if uu____18360
                                 then
                                   FStar_Syntax_Syntax.mk_GTotal result_typ
                                 else
                                   (let flags =
                                      let uu____18370 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid in
                                      if uu____18370
                                      then [FStar_Syntax_Syntax.LEMMA]
                                      else
                                        (let uu____18377 =
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_Tot_lid in
                                         if uu____18377
                                         then [FStar_Syntax_Syntax.TOTAL]
                                         else
                                           (let uu____18384 =
                                              FStar_Ident.lid_equals eff
                                                FStar_Parser_Const.effect_ML_lid in
                                            if uu____18384
                                            then
                                              [FStar_Syntax_Syntax.MLEFFECT]
                                            else
                                              (let uu____18391 =
                                                 FStar_Ident.lid_equals eff
                                                   FStar_Parser_Const.effect_GTot_lid in
                                               if uu____18391
                                               then
                                                 [FStar_Syntax_Syntax.SOMETRIVIAL]
                                               else []))) in
                                    let flags1 =
                                      FStar_List.append flags cattributes in
                                    let rest3 =
                                      let uu____18412 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid in
                                      if uu____18412
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
                                                    let uu____18503 =
                                                      FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos in
                                                    FStar_Syntax_Syntax.fvar
                                                      uu____18503
                                                      FStar_Syntax_Syntax.delta_constant
                                                      FStar_Pervasives_Native.None in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    nil
                                                    [(pattern,
                                                       (FStar_Pervasives_Native.Some
                                                          FStar_Syntax_Syntax.imp_tag))]
                                                    FStar_Pervasives_Native.None
                                                    pat.FStar_Syntax_Syntax.pos
                                              | uu____18524 -> pat in
                                            let uu____18525 =
                                              let uu____18536 =
                                                let uu____18547 =
                                                  let uu____18556 =
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (pat1,
                                                           (FStar_Syntax_Syntax.Meta_desugared
                                                              FStar_Syntax_Syntax.Meta_smt_pat)))
                                                      FStar_Pervasives_Native.None
                                                      pat1.FStar_Syntax_Syntax.pos in
                                                  (uu____18556, aq) in
                                                [uu____18547] in
                                              ens :: uu____18536 in
                                            req :: uu____18525
                                        | uu____18597 -> rest2
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
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range in
      let setpos t =
        let uu___2406_18632 = t in
        {
          FStar_Syntax_Syntax.n = (uu___2406_18632.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___2406_18632.FStar_Syntax_Syntax.vars)
        } in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___2413_18686 = b in
             {
               FStar_Parser_AST.b = (uu___2413_18686.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___2413_18686.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___2413_18686.FStar_Parser_AST.aqual)
             }) in
        let with_pats env1 uu____18715 body1 =
          match uu____18715 with
          | (names1, pats1) ->
              (match (names1, pats1) with
               | ([], []) -> body1
               | ([], uu____18761::uu____18762) ->
                   failwith
                     "Impossible: Annotated pattern without binders in scope"
               | uu____18780 ->
                   let names2 =
                     FStar_All.pipe_right names1
                       (FStar_List.map
                          (fun i ->
                             let uu___2432_18807 =
                               FStar_Syntax_DsEnv.fail_or2
                                 (FStar_Syntax_DsEnv.try_lookup_id env1) i in
                             {
                               FStar_Syntax_Syntax.n =
                                 (uu___2432_18807.FStar_Syntax_Syntax.n);
                               FStar_Syntax_Syntax.pos =
                                 (i.FStar_Ident.idRange);
                               FStar_Syntax_Syntax.vars =
                                 (uu___2432_18807.FStar_Syntax_Syntax.vars)
                             })) in
                   let pats2 =
                     FStar_All.pipe_right pats1
                       (FStar_List.map
                          (fun es ->
                             FStar_All.pipe_right es
                               (FStar_List.map
                                  (fun e ->
                                     let uu____18870 = desugar_term env1 e in
                                     FStar_All.pipe_left
                                       (arg_withimp_t
                                          FStar_Parser_AST.Nothing)
                                       uu____18870)))) in
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (body1,
                          (FStar_Syntax_Syntax.Meta_pattern (names2, pats2))))) in
        match tk with
        | (FStar_Pervasives_Native.Some a, k) ->
            let uu____18901 = FStar_Syntax_DsEnv.push_bv env a in
            (match uu____18901 with
             | (env1, a1) ->
                 let a2 =
                   let uu___2445_18911 = a1 in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___2445_18911.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___2445_18911.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   } in
                 let body1 = desugar_formula env1 body in
                 let body2 = with_pats env1 pats body1 in
                 let body3 =
                   let uu____18917 =
                     let uu____18920 =
                       let uu____18921 = FStar_Syntax_Syntax.mk_binder a2 in
                       [uu____18921] in
                     no_annot_abs uu____18920 body2 in
                   FStar_All.pipe_left setpos uu____18917 in
                 let uu____18942 =
                   let uu____18943 =
                     let uu____18960 =
                       let uu____18963 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange in
                       FStar_Syntax_Syntax.fvar uu____18963
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            Prims.int_one) FStar_Pervasives_Native.None in
                     let uu____18965 =
                       let uu____18976 = FStar_Syntax_Syntax.as_arg body3 in
                       [uu____18976] in
                     (uu____18960, uu____18965) in
                   FStar_Syntax_Syntax.Tm_app uu____18943 in
                 FStar_All.pipe_left mk1 uu____18942)
        | uu____19015 -> failwith "impossible" in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest in
            let body1 =
              let uu____19080 = q (rest, pats, body) in
              let uu____19083 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range in
              FStar_Parser_AST.mk_term uu____19080 uu____19083
                FStar_Parser_AST.Formula in
            let uu____19084 = q ([b], ([], []), body1) in
            FStar_Parser_AST.mk_term uu____19084 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____19095 -> failwith "impossible" in
      let uu____19099 =
        let uu____19100 = unparen f in uu____19100.FStar_Parser_AST.tm in
      match uu____19099 with
      | FStar_Parser_AST.Labeled (f1, l, p) ->
          let f2 = desugar_formula env f1 in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([], uu____19113, uu____19114) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([], uu____19138, uu____19139) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3, pats, body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____19195 =
            push_quant (fun x -> FStar_Parser_AST.QForall x) binders pats
              body in
          desugar_formula env uu____19195
      | FStar_Parser_AST.QExists (_1::_2::_3, pats, body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____19239 =
            push_quant (fun x -> FStar_Parser_AST.QExists x) binders pats
              body in
          desugar_formula env uu____19239
      | FStar_Parser_AST.QForall (b::[], pats, body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[], pats, body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____19303 -> desugar_term env f
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
          let uu____19314 = desugar_typ env t in
          ((FStar_Pervasives_Native.Some x), uu____19314)
      | FStar_Parser_AST.Annotated (x, t) ->
          let uu____19319 = desugar_typ env t in
          ((FStar_Pervasives_Native.Some x), uu____19319)
      | FStar_Parser_AST.TVariable x ->
          let uu____19323 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange in
          ((FStar_Pervasives_Native.Some x), uu____19323)
      | FStar_Parser_AST.NoName t ->
          let uu____19327 = desugar_typ env t in
          (FStar_Pervasives_Native.None, uu____19327)
      | FStar_Parser_AST.Variable x ->
          ((FStar_Pervasives_Native.Some x), FStar_Syntax_Syntax.tun)
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
      fun uu___12_19335 ->
        match uu___12_19335 with
        | (FStar_Pervasives_Native.None, k) ->
            let uu____19357 = FStar_Syntax_Syntax.null_binder k in
            (uu____19357, env)
        | (FStar_Pervasives_Native.Some a, k) ->
            let uu____19374 = FStar_Syntax_DsEnv.push_bv env a in
            (match uu____19374 with
             | (env1, a1) ->
                 let uu____19391 =
                   let uu____19398 = trans_aqual env1 imp in
                   ((let uu___2545_19404 = a1 in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___2545_19404.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___2545_19404.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____19398) in
                 (uu____19391, env1))
and (trans_aqual :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env ->
    fun uu___13_19412 ->
      match uu___13_19412 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____19416 =
            let uu____19417 = desugar_term env t in
            FStar_Syntax_Syntax.Meta uu____19417 in
          FStar_Pervasives_Native.Some uu____19416
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
let (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.aqual) Prims.list))
  =
  fun env ->
    fun bs ->
      let uu____19445 =
        FStar_List.fold_left
          (fun uu____19478 ->
             fun b ->
               match uu____19478 with
               | (env1, out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___2563_19522 = b in
                        {
                          FStar_Parser_AST.b =
                            (uu___2563_19522.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___2563_19522.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___2563_19522.FStar_Parser_AST.aqual)
                        }) in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a, k) ->
                        let uu____19537 = FStar_Syntax_DsEnv.push_bv env1 a in
                        (match uu____19537 with
                         | (env2, a1) ->
                             let a2 =
                               let uu___2573_19555 = a1 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2573_19555.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2573_19555.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               } in
                             let uu____19556 =
                               let uu____19563 =
                                 let uu____19568 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual in
                                 (a2, uu____19568) in
                               uu____19563 :: out in
                             (env2, uu____19556))
                    | uu____19579 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs in
      match uu____19445 with
      | (env1, tpars) -> (env1, (FStar_List.rev tpars))
let (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun env ->
    fun cattributes ->
      let desugar_attribute t =
        let uu____19667 =
          let uu____19668 = unparen t in uu____19668.FStar_Parser_AST.tm in
        match uu____19667 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____19669; FStar_Ident.ident = uu____19670;
              FStar_Ident.nsstr = uu____19671; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____19676 ->
            let uu____19677 =
              let uu____19683 =
                let uu____19685 = FStar_Parser_AST.term_to_string t in
                Prims.op_Hat "Unknown attribute " uu____19685 in
              (FStar_Errors.Fatal_UnknownAttribute, uu____19683) in
            FStar_Errors.raise_error uu____19677 t.FStar_Parser_AST.range in
      FStar_List.map desugar_attribute cattributes
let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x, uu____19702) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x, uu____19704) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu____19707 -> FStar_Pervasives_Native.None
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs ->
    FStar_List.collect
      (fun b ->
         let uu____19725 = binder_ident b in
         FStar_Common.list_of_option uu____19725) bs
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
               (fun uu___14_19762 ->
                  match uu___14_19762 with
                  | FStar_Syntax_Syntax.NoExtract -> true
                  | FStar_Syntax_Syntax.Abstract -> true
                  | FStar_Syntax_Syntax.Private -> true
                  | uu____19767 -> false)) in
        let quals2 q =
          let uu____19781 =
            (let uu____19785 = FStar_Syntax_DsEnv.iface env in
             Prims.op_Negation uu____19785) ||
              (FStar_Syntax_DsEnv.admitted_iface env) in
          if uu____19781
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1 in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d in
                let uu____19802 = FStar_Ident.range_of_lid disc_name in
                let uu____19803 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d] in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____19802;
                  FStar_Syntax_Syntax.sigquals = uu____19803;
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
            let uu____19843 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i ->
                      fun uu____19881 ->
                        match uu____19881 with
                        | (x, uu____19892) ->
                            let uu____19897 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i in
                            (match uu____19897 with
                             | (field_name, uu____19905) ->
                                 let only_decl =
                                   ((let uu____19910 =
                                       FStar_Syntax_DsEnv.current_module env in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____19910)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____19912 =
                                        let uu____19914 =
                                          FStar_Syntax_DsEnv.current_module
                                            env in
                                        uu____19914.FStar_Ident.str in
                                      FStar_Options.dont_gen_projectors
                                        uu____19912) in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____19932 =
                                       FStar_List.filter
                                         (fun uu___15_19936 ->
                                            match uu___15_19936 with
                                            | FStar_Syntax_Syntax.Abstract ->
                                                false
                                            | uu____19939 -> true) q in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____19932
                                   else q in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___16_19954 ->
                                             match uu___16_19954 with
                                             | FStar_Syntax_Syntax.NoExtract
                                                 -> true
                                             | FStar_Syntax_Syntax.Abstract
                                                 -> true
                                             | FStar_Syntax_Syntax.Private ->
                                                 true
                                             | uu____19959 -> false)) in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1) in
                                 let decl =
                                   let uu____19962 =
                                     FStar_Ident.range_of_lid field_name in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____19962;
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
                                      let uu____19969 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract) in
                                      if uu____19969
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          (FStar_Syntax_Syntax.Delta_equational_at_level
                                             Prims.int_one)
                                      else
                                        FStar_Syntax_Syntax.Delta_equational_at_level
                                          Prims.int_one in
                                    let lb =
                                      let uu____19980 =
                                        let uu____19985 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None in
                                        FStar_Util.Inr uu____19985 in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____19980;
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
                                      let uu____19989 =
                                        let uu____19990 =
                                          let uu____19997 =
                                            let uu____20000 =
                                              let uu____20001 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right in
                                              FStar_All.pipe_right
                                                uu____20001
                                                (fun fv ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                            [uu____20000] in
                                          ((false, [lb]), uu____19997) in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____19990 in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____19989;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = [];
                                        FStar_Syntax_Syntax.sigopts =
                                          FStar_Pervasives_Native.None
                                      } in
                                    if no_decl then [impl] else [decl; impl])))) in
            FStar_All.pipe_right uu____19843 FStar_List.flatten
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
            (lid, uu____20050, t, uu____20052, n1, uu____20054) when
            let uu____20061 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid in
            Prims.op_Negation uu____20061 ->
            let uu____20063 = FStar_Syntax_Util.arrow_formals t in
            (match uu____20063 with
             | (formals, uu____20081) ->
                 (match formals with
                  | [] -> []
                  | uu____20110 ->
                      let filter_records uu___17_20126 =
                        match uu___17_20126 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____20129, fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____20141 -> FStar_Pervasives_Native.None in
                      let fv_qual =
                        let uu____20143 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records in
                        match uu____20143 with
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
                      let uu____20155 = FStar_Util.first_N n1 formals in
                      (match uu____20155 with
                       | (uu____20184, rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____20218 -> []
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
                        let uu____20312 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env lid in
                        FStar_All.pipe_right uu____20312
                          FStar_Pervasives_Native.snd in
                      let dd =
                        let uu____20336 =
                          FStar_All.pipe_right quals
                            (FStar_List.contains FStar_Syntax_Syntax.Abstract) in
                        if uu____20336
                        then
                          let uu____20342 =
                            FStar_Syntax_Util.incr_delta_qualifier t in
                          FStar_Syntax_Syntax.Delta_abstract uu____20342
                        else FStar_Syntax_Util.incr_delta_qualifier t in
                      let lb =
                        let uu____20346 =
                          let uu____20351 =
                            FStar_Syntax_Syntax.lid_as_fv lid dd
                              FStar_Pervasives_Native.None in
                          FStar_Util.Inr uu____20351 in
                        let uu____20352 =
                          if FStar_Util.is_some kopt
                          then
                            let uu____20358 =
                              let uu____20361 =
                                FStar_All.pipe_right kopt FStar_Util.must in
                              FStar_Syntax_Syntax.mk_Total uu____20361 in
                            FStar_Syntax_Util.arrow typars uu____20358
                          else FStar_Syntax_Syntax.tun in
                        let uu____20366 = no_annot_abs typars t in
                        {
                          FStar_Syntax_Syntax.lbname = uu____20346;
                          FStar_Syntax_Syntax.lbunivs = uvs;
                          FStar_Syntax_Syntax.lbtyp = uu____20352;
                          FStar_Syntax_Syntax.lbeff =
                            FStar_Parser_Const.effect_Tot_lid;
                          FStar_Syntax_Syntax.lbdef = uu____20366;
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
          let tycon_id uu___18_20420 =
            match uu___18_20420 with
            | FStar_Parser_AST.TyconAbstract (id1, uu____20422, uu____20423)
                -> id1
            | FStar_Parser_AST.TyconAbbrev
                (id1, uu____20433, uu____20434, uu____20435) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1, uu____20445, uu____20446, uu____20447) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1, uu____20477, uu____20478, uu____20479) -> id1 in
          let binder_to_term1 b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x, uu____20525) ->
                let uu____20526 =
                  let uu____20527 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____20527 in
                FStar_Parser_AST.mk_term uu____20526 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____20529 =
                  let uu____20530 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____20530 in
                FStar_Parser_AST.mk_term uu____20529 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a, uu____20532) ->
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  a.FStar_Ident.idRange FStar_Parser_AST.Type_level
            | FStar_Parser_AST.TVariable a ->
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  a.FStar_Ident.idRange FStar_Parser_AST.Type_level
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
              | uu____20563 -> FStar_Parser_AST.Nothing in
            FStar_List.fold_left
              (fun out ->
                 fun b ->
                   let uu____20571 =
                     let uu____20572 =
                       let uu____20579 = binder_to_term1 b in
                       (out, uu____20579, (imp_of_aqual b)) in
                     FStar_Parser_AST.App uu____20572 in
                   FStar_Parser_AST.mk_term uu____20571
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders in
          let tycon_record_as_variant uu___19_20591 =
            match uu___19_20591 with
            | FStar_Parser_AST.TyconRecord (id1, parms, kopt, fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.op_Hat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange)) in
                let mfields =
                  FStar_List.map
                    (fun uu____20648 ->
                       match uu____20648 with
                       | (x, t, uu____20659) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated (x, t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields in
                let result =
                  let uu____20665 =
                    let uu____20666 =
                      let uu____20667 = FStar_Ident.lid_of_ids [id1] in
                      FStar_Parser_AST.Var uu____20667 in
                    FStar_Parser_AST.mk_term uu____20666
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                  apply_binders uu____20665 parms in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                let names1 =
                  let uu____20674 = binder_idents parms in id1 :: uu____20674 in
                (FStar_List.iter
                   (fun uu____20692 ->
                      match uu____20692 with
                      | (f, uu____20702, uu____20703) ->
                          let uu____20708 =
                            FStar_Util.for_some
                              (fun i -> FStar_Ident.ident_equals f i) names1 in
                          if uu____20708
                          then
                            let uu____20713 =
                              let uu____20719 =
                                let uu____20721 =
                                  FStar_Ident.string_of_ident f in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu____20721 in
                              (FStar_Errors.Error_FieldShadow, uu____20719) in
                            FStar_Errors.raise_error uu____20713
                              f.FStar_Ident.idRange
                          else ()) fields;
                 (let uu____20727 =
                    FStar_All.pipe_right fields
                      (FStar_List.map
                         (fun uu____20754 ->
                            match uu____20754 with
                            | (x, uu____20764, uu____20765) -> x)) in
                  ((FStar_Parser_AST.TyconVariant
                      (id1, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp),
                           FStar_Pervasives_Native.None, false)])),
                    uu____20727)))
            | uu____20823 -> failwith "impossible" in
          let desugar_abstract_tc quals1 _env mutuals uu___20_20863 =
            match uu___20_20863 with
            | FStar_Parser_AST.TyconAbstract (id1, binders, kopt) ->
                let uu____20887 = typars_of_binders _env binders in
                (match uu____20887 with
                 | (_env', typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k in
                     let tconstr =
                       let uu____20923 =
                         let uu____20924 =
                           let uu____20925 = FStar_Ident.lid_of_ids [id1] in
                           FStar_Parser_AST.Var uu____20925 in
                         FStar_Parser_AST.mk_term uu____20924
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level in
                       apply_binders uu____20923 binders in
                     let qlid = FStar_Syntax_DsEnv.qualify _env id1 in
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
                     let uu____20934 =
                       FStar_Syntax_DsEnv.push_top_level_rec_binding _env id1
                         FStar_Syntax_Syntax.delta_constant in
                     (match uu____20934 with
                      | (_env1, uu____20951) ->
                          let uu____20958 =
                            FStar_Syntax_DsEnv.push_top_level_rec_binding
                              _env' id1 FStar_Syntax_Syntax.delta_constant in
                          (match uu____20958 with
                           | (_env2, uu____20975) ->
                               (_env1, _env2, se, tconstr))))
            | uu____20982 -> failwith "Unexpected tycon" in
          let push_tparams env1 bs =
            let uu____21025 =
              FStar_List.fold_left
                (fun uu____21059 ->
                   fun uu____21060 ->
                     match (uu____21059, uu____21060) with
                     | ((env2, tps), (x, imp)) ->
                         let uu____21129 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname in
                         (match uu____21129 with
                          | (env3, y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs in
            match uu____21025 with
            | (env2, bs1) -> (env2, (FStar_List.rev bs1)) in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1, bs, kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None ->
                    let uu____21220 = tm_type_z id1.FStar_Ident.idRange in
                    FStar_Pervasives_Native.Some uu____21220
                | uu____21221 -> kopt in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1) in
              let uu____21229 = desugar_abstract_tc quals env [] tc in
              (match uu____21229 with
               | (uu____21242, uu____21243, se, uu____21245) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l, uu____21248, typars, k, [], []) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____21267 =
                                 let uu____21269 = FStar_Options.ml_ish () in
                                 Prims.op_Negation uu____21269 in
                               if uu____21267
                               then
                                 let uu____21272 =
                                   let uu____21278 =
                                     let uu____21280 =
                                       FStar_Syntax_Print.lid_to_string l in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____21280 in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____21278) in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____21272
                               else ());
                              FStar_Syntax_Syntax.Assumption
                              ::
                              FStar_Syntax_Syntax.New
                              ::
                              quals1) in
                         let t =
                           match typars with
                           | [] -> k
                           | uu____21293 ->
                               let uu____21294 =
                                 let uu____21301 =
                                   let uu____21302 =
                                     let uu____21317 =
                                       FStar_Syntax_Syntax.mk_Total k in
                                     (typars, uu____21317) in
                                   FStar_Syntax_Syntax.Tm_arrow uu____21302 in
                                 FStar_Syntax_Syntax.mk uu____21301 in
                               uu____21294 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng in
                         let uu___2862_21330 = se in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___2862_21330.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___2862_21330.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___2862_21330.FStar_Syntax_Syntax.sigattrs);
                           FStar_Syntax_Syntax.sigopts =
                             (uu___2862_21330.FStar_Syntax_Syntax.sigopts)
                         }
                     | uu____21331 -> failwith "Impossible" in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1 in
                   let env2 =
                     let uu____21335 = FStar_Syntax_DsEnv.qualify env1 id1 in
                     FStar_Syntax_DsEnv.push_doc env1 uu____21335
                       d.FStar_Parser_AST.doc in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1, binders, kopt, t))::[] ->
              let uu____21348 = typars_of_binders env binders in
              (match uu____21348 with
               | (env', typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None ->
                         let uu____21382 =
                           FStar_Util.for_some
                             (fun uu___21_21385 ->
                                match uu___21_21385 with
                                | FStar_Syntax_Syntax.Effect -> true
                                | uu____21388 -> false) quals in
                         if uu____21382
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____21396 = desugar_term env' k in
                         FStar_Pervasives_Native.Some uu____21396 in
                   let t0 = t in
                   let quals1 =
                     let uu____21401 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___22_21407 ->
                               match uu___22_21407 with
                               | FStar_Syntax_Syntax.Logic -> true
                               | uu____21410 -> false)) in
                     if uu____21401
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1 in
                   let se =
                     let uu____21424 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect) in
                     if uu____21424
                     then
                       let uu____21430 =
                         let uu____21437 =
                           let uu____21438 = unparen t in
                           uu____21438.FStar_Parser_AST.tm in
                         match uu____21437 with
                         | FStar_Parser_AST.Construct (head1, args) ->
                             let uu____21459 =
                               match FStar_List.rev args with
                               | (last_arg, uu____21489)::args_rev ->
                                   let uu____21501 =
                                     let uu____21502 = unparen last_arg in
                                     uu____21502.FStar_Parser_AST.tm in
                                   (match uu____21501 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____21530 -> ([], args))
                               | uu____21539 -> ([], args) in
                             (match uu____21459 with
                              | (cattributes, args1) ->
                                  let uu____21578 =
                                    desugar_attributes env cattributes in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____21578))
                         | uu____21589 -> (t, []) in
                       match uu____21430 with
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
                                  (fun uu___23_21612 ->
                                     match uu___23_21612 with
                                     | FStar_Syntax_Syntax.Effect -> false
                                     | uu____21615 -> true)) in
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
                   let env2 =
                     FStar_Syntax_DsEnv.push_doc env1 qlid
                       d.FStar_Parser_AST.doc in
                   (env2, [se]))
          | (FStar_Parser_AST.TyconRecord uu____21624)::[] ->
              let trec = FStar_List.hd tcs in
              let uu____21648 = tycon_record_as_variant trec in
              (match uu____21648 with
               | (t, fs) ->
                   let uu____21665 =
                     let uu____21668 =
                       let uu____21669 =
                         let uu____21678 =
                           let uu____21681 =
                             FStar_Syntax_DsEnv.current_module env in
                           FStar_Ident.ids_of_lid uu____21681 in
                         (uu____21678, fs) in
                       FStar_Syntax_Syntax.RecordType uu____21669 in
                     uu____21668 :: quals in
                   desugar_tycon env d uu____21665 [t])
          | uu____21686::uu____21687 ->
              let env0 = env in
              let mutuals =
                FStar_List.map
                  (fun x ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs in
              let rec collect_tcs quals1 et tc =
                let uu____21857 = et in
                match uu____21857 with
                | (env1, tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____22087 ->
                         let trec = tc in
                         let uu____22111 = tycon_record_as_variant trec in
                         (match uu____22111 with
                          | (t, fs) ->
                              let uu____22171 =
                                let uu____22174 =
                                  let uu____22175 =
                                    let uu____22184 =
                                      let uu____22187 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1 in
                                      FStar_Ident.ids_of_lid uu____22187 in
                                    (uu____22184, fs) in
                                  FStar_Syntax_Syntax.RecordType uu____22175 in
                                uu____22174 :: quals1 in
                              collect_tcs uu____22171 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1, binders, kopt, constructors) ->
                         let uu____22277 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt)) in
                         (match uu____22277 with
                          | (env2, uu____22338, se, tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1, binders, kopt, t)
                         ->
                         let uu____22491 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt)) in
                         (match uu____22491 with
                          | (env2, uu____22552, se, tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____22680 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng) in
              let uu____22730 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs in
              (match uu____22730 with
               | (env1, tcs1) ->
                   let tcs2 = FStar_List.rev tcs1 in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___25_23246 ->
                             match uu___25_23246 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1, uvs, tpars, k, uu____23312,
                                       uu____23313);
                                    FStar_Syntax_Syntax.sigrng = uu____23314;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____23315;
                                    FStar_Syntax_Syntax.sigmeta = uu____23316;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____23317;
                                    FStar_Syntax_Syntax.sigopts = uu____23318;_},
                                  binders, t, quals1)
                                 ->
                                 let t1 =
                                   let uu____23384 =
                                     typars_of_binders env1 binders in
                                   match uu____23384 with
                                   | (env2, tpars1) ->
                                       let uu____23411 =
                                         push_tparams env2 tpars1 in
                                       (match uu____23411 with
                                        | (env_tps, tpars2) ->
                                            let t1 = desugar_typ env_tps t in
                                            let tpars3 =
                                              FStar_Syntax_Subst.close_binders
                                                tpars2 in
                                            FStar_Syntax_Subst.close tpars3
                                              t1) in
                                 let uu____23440 =
                                   let uu____23459 =
                                     mk_typ_abbrev env1 d id1 uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id1] quals1 rng in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____23459) in
                                 [uu____23440]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname, univs1, tpars, k, mutuals1,
                                       uu____23519);
                                    FStar_Syntax_Syntax.sigrng = uu____23520;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____23522;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____23523;
                                    FStar_Syntax_Syntax.sigopts = uu____23524;_},
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
                                 let uu____23627 = push_tparams env1 tpars in
                                 (match uu____23627 with
                                  | (env_tps, tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____23694 ->
                                             match uu____23694 with
                                             | (x, uu____23706) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps in
                                      let tot_tconstr = mk_tot tconstr in
                                      let attrs =
                                        FStar_List.map (desugar_term env1)
                                          d.FStar_Parser_AST.attrs in
                                      let val_attrs =
                                        let uu____23717 =
                                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                                            env1 tname in
                                        FStar_All.pipe_right uu____23717
                                          FStar_Pervasives_Native.snd in
                                      let uu____23740 =
                                        let uu____23767 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____23877 ->
                                                  match uu____23877 with
                                                  | (id1, topt, doc1,
                                                     of_notation) ->
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
                                                        let uu____23937 =
                                                          close env_tps t in
                                                        desugar_term env_tps
                                                          uu____23937 in
                                                      let name =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env1 id1 in
                                                      let quals2 =
                                                        FStar_All.pipe_right
                                                          tname_quals
                                                          (FStar_List.collect
                                                             (fun
                                                                uu___24_23948
                                                                ->
                                                                match uu___24_23948
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____23960
                                                                    -> [])) in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars in
                                                      let uu____23968 =
                                                        let uu____23987 =
                                                          let uu____23988 =
                                                            let uu____23989 =
                                                              let uu____24005
                                                                =
                                                                let uu____24006
                                                                  =
                                                                  let uu____24009
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____24009 in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____24006 in
                                                              (name, univs1,
                                                                uu____24005,
                                                                tname, ntps,
                                                                mutuals1) in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____23989 in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____23988;
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
                                                        ((name, doc1), tps,
                                                          uu____23987) in
                                                      (name, uu____23968))) in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____23767 in
                                      (match uu____23740 with
                                       | (constrNames, constrs1) ->
                                           ((tname, (d.FStar_Parser_AST.doc)),
                                             [],
                                             {
                                               FStar_Syntax_Syntax.sigel =
                                                 (FStar_Syntax_Syntax.Sig_inductive_typ
                                                    (tname, univs1, tpars, k,
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
                             | uu____24221 -> failwith "impossible")) in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____24349 ->
                             match uu____24349 with
                             | (name_doc, uu____24375, uu____24376) ->
                                 name_doc)) in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____24448 ->
                             match uu____24448 with
                             | (uu____24467, uu____24468, se) -> se)) in
                   let uu____24494 =
                     let uu____24501 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____24501 rng in
                   (match uu____24494 with
                    | (bundle, abbrevs) ->
                        let env2 = FStar_Syntax_DsEnv.push_sigelt env0 bundle in
                        let env3 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env2 abbrevs in
                        let data_ops =
                          FStar_All.pipe_right docs_tps_sigelts
                            (FStar_List.collect
                               (fun uu____24563 ->
                                  match uu____24563 with
                                  | (uu____24584, tps, se) ->
                                      mk_data_projector_names quals env3 se)) in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname, uu____24632, tps, k,
                                       uu____24635, constrs)
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
                                      let uu____24656 =
                                        FStar_All.pipe_right constrs
                                          (FStar_List.filter
                                             (fun data_lid ->
                                                let data_quals =
                                                  let data_se =
                                                    let uu____24671 =
                                                      FStar_All.pipe_right
                                                        sigelts
                                                        (FStar_List.find
                                                           (fun se1 ->
                                                              match se1.FStar_Syntax_Syntax.sigel
                                                              with
                                                              | FStar_Syntax_Syntax.Sig_datacon
                                                                  (name,
                                                                   uu____24688,
                                                                   uu____24689,
                                                                   uu____24690,
                                                                   uu____24691,
                                                                   uu____24692)
                                                                  ->
                                                                  FStar_Ident.lid_equals
                                                                    name
                                                                    data_lid
                                                              | uu____24699
                                                                  -> false)) in
                                                    FStar_All.pipe_right
                                                      uu____24671
                                                      FStar_Util.must in
                                                  data_se.FStar_Syntax_Syntax.sigquals in
                                                let uu____24703 =
                                                  FStar_All.pipe_right
                                                    data_quals
                                                    (FStar_List.existsb
                                                       (fun uu___26_24710 ->
                                                          match uu___26_24710
                                                          with
                                                          | FStar_Syntax_Syntax.RecordConstructor
                                                              uu____24712 ->
                                                              true
                                                          | uu____24722 ->
                                                              false)) in
                                                Prims.op_Negation uu____24703)) in
                                      mk_data_discriminators quals2 env3
                                        uu____24656
                                  | uu____24724 -> [])) in
                        let ops = FStar_List.append discs data_ops in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc ->
                               fun uu____24741 ->
                                 match uu____24741 with
                                 | (lid, doc1) ->
                                     FStar_Syntax_DsEnv.push_doc env4 lid
                                       doc1) env4 name_docs in
                        (env5,
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
      let uu____24786 =
        FStar_List.fold_left
          (fun uu____24821 ->
             fun b ->
               match uu____24821 with
               | (env1, binders1) ->
                   let uu____24865 = desugar_binder env1 b in
                   (match uu____24865 with
                    | (FStar_Pervasives_Native.Some a, k) ->
                        let uu____24888 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k) in
                        (match uu____24888 with
                         | (binder, env2) -> (env2, (binder :: binders1)))
                    | uu____24941 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders in
      match uu____24786 with
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
          let uu____25045 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___27_25052 ->
                    match uu___27_25052 with
                    | FStar_Syntax_Syntax.Reflectable uu____25054 -> true
                    | uu____25056 -> false)) in
          if uu____25045
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident in
            let reflect_lid =
              let uu____25061 = FStar_Ident.id_of_text "reflect" in
              FStar_All.pipe_right uu____25061
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
    fun at1 ->
      fun head1 ->
        let warn1 uu____25112 =
          if warn
          then
            let uu____25114 =
              let uu____25120 =
                let uu____25122 = FStar_Ident.string_of_lid head1 in
                FStar_Util.format1
                  "Found ill-applied '%s', argument should be a non-empty list of integer literals"
                  uu____25122 in
              (FStar_Errors.Warning_UnappliedFail, uu____25120) in
            FStar_Errors.log_issue at1.FStar_Syntax_Syntax.pos uu____25114
          else () in
        let uu____25128 = FStar_Syntax_Util.head_and_args at1 in
        match uu____25128 with
        | (hd1, args) ->
            let uu____25181 =
              let uu____25182 = FStar_Syntax_Subst.compress hd1 in
              uu____25182.FStar_Syntax_Syntax.n in
            (match uu____25181 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 FStar_Syntax_Syntax.fv_eq_lid fv head1 ->
                 (match args with
                  | [] -> ((FStar_Pervasives_Native.Some []), true)
                  | (a1, uu____25226)::[] ->
                      let uu____25251 =
                        let uu____25256 =
                          let uu____25265 =
                            FStar_Syntax_Embeddings.e_list
                              FStar_Syntax_Embeddings.e_int in
                          FStar_Syntax_Embeddings.unembed uu____25265 a1 in
                        uu____25256 true FStar_Syntax_Embeddings.id_norm_cb in
                      (match uu____25251 with
                       | FStar_Pervasives_Native.Some es ->
                           let uu____25288 =
                             let uu____25294 =
                               FStar_List.map FStar_BigInt.to_int_fs es in
                             FStar_Pervasives_Native.Some uu____25294 in
                           (uu____25288, true)
                       | uu____25309 ->
                           (warn1 (); (FStar_Pervasives_Native.None, true)))
                  | uu____25325 ->
                      (warn1 (); (FStar_Pervasives_Native.None, true)))
             | uu____25347 -> (FStar_Pervasives_Native.None, false))
let (get_fail_attr :
  Prims.bool ->
    FStar_Syntax_Syntax.term ->
      (Prims.int Prims.list * Prims.bool) FStar_Pervasives_Native.option)
  =
  fun warn ->
    fun at1 ->
      let rebind res b =
        match res with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some l ->
            FStar_Pervasives_Native.Some (l, b) in
      let uu____25464 =
        parse_attr_with_list warn at1 FStar_Parser_Const.fail_attr in
      match uu____25464 with
      | (res, matched) ->
          if matched
          then rebind res false
          else
            (let uu____25513 =
               parse_attr_with_list warn at1 FStar_Parser_Const.fail_lax_attr in
             match uu____25513 with | (res1, uu____25535) -> rebind res1 true)
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
        fun is_layered1 ->
          fun eff_name ->
            fun eff_binders ->
              fun eff_typ ->
                fun eff_decls ->
                  fun attrs ->
                    let env0 = env in
                    let monad_env =
                      FStar_Syntax_DsEnv.enter_monad_scope env eff_name in
                    let uu____25707 = desugar_binders monad_env eff_binders in
                    match uu____25707 with
                    | (env1, binders) ->
                        let eff_t = desugar_term env1 eff_typ in
                        let num_indices =
                          let uu____25746 =
                            let uu____25755 =
                              FStar_Syntax_Util.arrow_formals eff_t in
                            FStar_Pervasives_Native.fst uu____25755 in
                          FStar_List.length uu____25746 in
                        (if is_layered1 && (num_indices <= Prims.int_one)
                         then
                           (let uu____25789 =
                              let uu____25795 =
                                let uu____25797 =
                                  let uu____25799 =
                                    FStar_Ident.text_of_id eff_name in
                                  Prims.op_Hat uu____25799
                                    "is defined as a layered effect but has no indices" in
                                Prims.op_Hat "Effect " uu____25797 in
                              (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                uu____25795) in
                            FStar_Errors.raise_error uu____25789
                              d.FStar_Parser_AST.drange)
                         else ();
                         (let for_free = num_indices = Prims.int_one in
                          let mandatory_members =
                            let rr_members = ["repr"; "return"; "bind"] in
                            if for_free
                            then rr_members
                            else
                              if is_layered1
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
                                (uu____25867, uu____25868,
                                 (FStar_Parser_AST.TyconAbbrev
                                  (name, uu____25870, uu____25871,
                                   uu____25872),
                                  uu____25873)::[])
                                -> FStar_Ident.text_of_id name
                            | uu____25910 ->
                                failwith
                                  "Malformed effect member declaration." in
                          let uu____25913 =
                            FStar_List.partition
                              (fun decl ->
                                 let uu____25925 = name_of_eff_decl decl in
                                 FStar_List.mem uu____25925 mandatory_members)
                              eff_decls in
                          match uu____25913 with
                          | (mandatory_members_decls, actions) ->
                              let uu____25944 =
                                FStar_All.pipe_right mandatory_members_decls
                                  (FStar_List.fold_left
                                     (fun uu____25973 ->
                                        fun decl ->
                                          match uu____25973 with
                                          | (env2, out) ->
                                              let uu____25993 =
                                                desugar_decl env2 decl in
                                              (match uu____25993 with
                                               | (env3, ses) ->
                                                   let uu____26006 =
                                                     let uu____26009 =
                                                       FStar_List.hd ses in
                                                     uu____26009 :: out in
                                                   (env3, uu____26006)))
                                     (env1, [])) in
                              (match uu____25944 with
                               | (env2, decls) ->
                                   let binders1 =
                                     FStar_Syntax_Subst.close_binders binders in
                                   let actions_docs =
                                     FStar_All.pipe_right actions
                                       (FStar_List.map
                                          (fun d1 ->
                                             match d1.FStar_Parser_AST.d with
                                             | FStar_Parser_AST.Tycon
                                                 (uu____26078, uu____26079,
                                                  (FStar_Parser_AST.TyconAbbrev
                                                   (name, action_params,
                                                    uu____26082,
                                                    {
                                                      FStar_Parser_AST.tm =
                                                        FStar_Parser_AST.Construct
                                                        (uu____26083,
                                                         (def, uu____26085)::
                                                         (cps_type,
                                                          uu____26087)::[]);
                                                      FStar_Parser_AST.range
                                                        = uu____26088;
                                                      FStar_Parser_AST.level
                                                        = uu____26089;_}),
                                                   doc1)::[])
                                                 when
                                                 Prims.op_Negation for_free
                                                 ->
                                                 let uu____26145 =
                                                   desugar_binders env2
                                                     action_params in
                                                 (match uu____26145 with
                                                  | (env3, action_params1) ->
                                                      let action_params2 =
                                                        FStar_Syntax_Subst.close_binders
                                                          action_params1 in
                                                      let uu____26183 =
                                                        let uu____26184 =
                                                          FStar_Syntax_DsEnv.qualify
                                                            env3 name in
                                                        let uu____26185 =
                                                          let uu____26186 =
                                                            desugar_term env3
                                                              def in
                                                          FStar_Syntax_Subst.close
                                                            (FStar_List.append
                                                               binders1
                                                               action_params2)
                                                            uu____26186 in
                                                        let uu____26193 =
                                                          let uu____26194 =
                                                            desugar_typ env3
                                                              cps_type in
                                                          FStar_Syntax_Subst.close
                                                            (FStar_List.append
                                                               binders1
                                                               action_params2)
                                                            uu____26194 in
                                                        {
                                                          FStar_Syntax_Syntax.action_name
                                                            = uu____26184;
                                                          FStar_Syntax_Syntax.action_unqualified_name
                                                            = name;
                                                          FStar_Syntax_Syntax.action_univs
                                                            = [];
                                                          FStar_Syntax_Syntax.action_params
                                                            = action_params2;
                                                          FStar_Syntax_Syntax.action_defn
                                                            = uu____26185;
                                                          FStar_Syntax_Syntax.action_typ
                                                            = uu____26193
                                                        } in
                                                      (uu____26183, doc1))
                                             | FStar_Parser_AST.Tycon
                                                 (uu____26203, uu____26204,
                                                  (FStar_Parser_AST.TyconAbbrev
                                                   (name, action_params,
                                                    uu____26207, defn),
                                                   doc1)::[])
                                                 when for_free || is_layered1
                                                 ->
                                                 let uu____26246 =
                                                   desugar_binders env2
                                                     action_params in
                                                 (match uu____26246 with
                                                  | (env3, action_params1) ->
                                                      let action_params2 =
                                                        FStar_Syntax_Subst.close_binders
                                                          action_params1 in
                                                      let uu____26284 =
                                                        let uu____26285 =
                                                          FStar_Syntax_DsEnv.qualify
                                                            env3 name in
                                                        let uu____26286 =
                                                          let uu____26287 =
                                                            desugar_term env3
                                                              defn in
                                                          FStar_Syntax_Subst.close
                                                            (FStar_List.append
                                                               binders1
                                                               action_params2)
                                                            uu____26287 in
                                                        {
                                                          FStar_Syntax_Syntax.action_name
                                                            = uu____26285;
                                                          FStar_Syntax_Syntax.action_unqualified_name
                                                            = name;
                                                          FStar_Syntax_Syntax.action_univs
                                                            = [];
                                                          FStar_Syntax_Syntax.action_params
                                                            = action_params2;
                                                          FStar_Syntax_Syntax.action_defn
                                                            = uu____26286;
                                                          FStar_Syntax_Syntax.action_typ
                                                            =
                                                            FStar_Syntax_Syntax.tun
                                                        } in
                                                      (uu____26284, doc1))
                                             | uu____26296 ->
                                                 FStar_Errors.raise_error
                                                   (FStar_Errors.Fatal_MalformedActionDeclaration,
                                                     "Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples).")
                                                   d1.FStar_Parser_AST.drange)) in
                                   let actions1 =
                                     FStar_List.map
                                       FStar_Pervasives_Native.fst
                                       actions_docs in
                                   let eff_t1 =
                                     FStar_Syntax_Subst.close binders1 eff_t in
                                   let lookup1 s =
                                     let l =
                                       let uu____26332 =
                                         FStar_Ident.mk_ident
                                           (s, (d.FStar_Parser_AST.drange)) in
                                       FStar_Syntax_DsEnv.qualify env2
                                         uu____26332 in
                                     let uu____26334 =
                                       let uu____26335 =
                                         FStar_Syntax_DsEnv.fail_or env2
                                           (FStar_Syntax_DsEnv.try_lookup_definition
                                              env2) l in
                                       FStar_All.pipe_left
                                         (FStar_Syntax_Subst.close binders1)
                                         uu____26335 in
                                     ([], uu____26334) in
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
                                       let uu____26357 =
                                         let uu____26358 =
                                           let uu____26361 = lookup1 "repr" in
                                           FStar_Pervasives_Native.Some
                                             uu____26361 in
                                         let uu____26363 =
                                           let uu____26366 = lookup1 "return" in
                                           FStar_Pervasives_Native.Some
                                             uu____26366 in
                                         let uu____26368 =
                                           let uu____26371 = lookup1 "bind" in
                                           FStar_Pervasives_Native.Some
                                             uu____26371 in
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
                                             uu____26358;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____26363;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____26368
                                         } in
                                       FStar_Syntax_Syntax.DM4F_eff
                                         uu____26357
                                     else
                                       if is_layered1
                                       then
                                         (let to_comb uu____26409 =
                                            match uu____26409 with
                                            | (us, t) ->
                                                ((us, t), dummy_tscheme) in
                                          let uu____26468 =
                                            let uu____26469 =
                                              FStar_Ident.lid_of_str "" in
                                            let uu____26471 =
                                              let uu____26476 =
                                                lookup1 "repr" in
                                              FStar_All.pipe_right
                                                uu____26476 to_comb in
                                            let uu____26498 =
                                              let uu____26503 =
                                                lookup1 "return" in
                                              FStar_All.pipe_right
                                                uu____26503 to_comb in
                                            let uu____26525 =
                                              let uu____26530 =
                                                lookup1 "bind" in
                                              FStar_All.pipe_right
                                                uu____26530 to_comb in
                                            let uu____26552 =
                                              let uu____26557 =
                                                lookup1 "subcomp" in
                                              FStar_All.pipe_right
                                                uu____26557 to_comb in
                                            let uu____26579 =
                                              let uu____26584 =
                                                lookup1 "if_then_else" in
                                              FStar_All.pipe_right
                                                uu____26584 to_comb in
                                            {
                                              FStar_Syntax_Syntax.l_base_effect
                                                = uu____26469;
                                              FStar_Syntax_Syntax.l_repr =
                                                uu____26471;
                                              FStar_Syntax_Syntax.l_return =
                                                uu____26498;
                                              FStar_Syntax_Syntax.l_bind =
                                                uu____26525;
                                              FStar_Syntax_Syntax.l_subcomp =
                                                uu____26552;
                                              FStar_Syntax_Syntax.l_if_then_else
                                                = uu____26579
                                            } in
                                          FStar_Syntax_Syntax.Layered_eff
                                            uu____26468)
                                       else
                                         (let rr =
                                            FStar_Util.for_some
                                              (fun uu___28_26611 ->
                                                 match uu___28_26611 with
                                                 | FStar_Syntax_Syntax.Reifiable
                                                     -> true
                                                 | FStar_Syntax_Syntax.Reflectable
                                                     uu____26614 -> true
                                                 | uu____26616 -> false)
                                              qualifiers in
                                          let uu____26618 =
                                            let uu____26619 =
                                              lookup1 "return_wp" in
                                            let uu____26621 =
                                              lookup1 "bind_wp" in
                                            let uu____26623 =
                                              lookup1 "stronger" in
                                            let uu____26625 =
                                              lookup1 "if_then_else" in
                                            let uu____26627 =
                                              lookup1 "ite_wp" in
                                            let uu____26629 =
                                              lookup1 "close_wp" in
                                            let uu____26631 =
                                              lookup1 "trivial" in
                                            let uu____26633 =
                                              if rr
                                              then
                                                let uu____26639 =
                                                  lookup1 "repr" in
                                                FStar_Pervasives_Native.Some
                                                  uu____26639
                                              else
                                                FStar_Pervasives_Native.None in
                                            let uu____26643 =
                                              if rr
                                              then
                                                let uu____26649 =
                                                  lookup1 "return" in
                                                FStar_Pervasives_Native.Some
                                                  uu____26649
                                              else
                                                FStar_Pervasives_Native.None in
                                            let uu____26653 =
                                              if rr
                                              then
                                                let uu____26659 =
                                                  lookup1 "bind" in
                                                FStar_Pervasives_Native.Some
                                                  uu____26659
                                              else
                                                FStar_Pervasives_Native.None in
                                            {
                                              FStar_Syntax_Syntax.ret_wp =
                                                uu____26619;
                                              FStar_Syntax_Syntax.bind_wp =
                                                uu____26621;
                                              FStar_Syntax_Syntax.stronger =
                                                uu____26623;
                                              FStar_Syntax_Syntax.if_then_else
                                                = uu____26625;
                                              FStar_Syntax_Syntax.ite_wp =
                                                uu____26627;
                                              FStar_Syntax_Syntax.close_wp =
                                                uu____26629;
                                              FStar_Syntax_Syntax.trivial =
                                                uu____26631;
                                              FStar_Syntax_Syntax.repr =
                                                uu____26633;
                                              FStar_Syntax_Syntax.return_repr
                                                = uu____26643;
                                              FStar_Syntax_Syntax.bind_repr =
                                                uu____26653
                                            } in
                                          FStar_Syntax_Syntax.Primitive_eff
                                            uu____26618) in
                                   let sigel =
                                     let uu____26664 =
                                       let uu____26665 =
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
                                           uu____26665
                                       } in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____26664 in
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
                                     FStar_Syntax_DsEnv.push_doc env3 mname
                                       d.FStar_Parser_AST.doc in
                                   let env5 =
                                     FStar_All.pipe_right actions_docs
                                       (FStar_List.fold_left
                                          (fun env5 ->
                                             fun uu____26696 ->
                                               match uu____26696 with
                                               | (a, doc1) ->
                                                   let env6 =
                                                     let uu____26710 =
                                                       FStar_Syntax_Util.action_as_lb
                                                         mname a
                                                         (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                                                     FStar_Syntax_DsEnv.push_sigelt
                                                       env5 uu____26710 in
                                                   FStar_Syntax_DsEnv.push_doc
                                                     env6
                                                     a.FStar_Syntax_Syntax.action_name
                                                     doc1) env4) in
                                   let env6 =
                                     push_reflect_effect env5 qualifiers
                                       mname d.FStar_Parser_AST.drange in
                                   let env7 =
                                     FStar_Syntax_DsEnv.push_doc env6 mname
                                       d.FStar_Parser_AST.doc in
                                   (env7, [se]))))
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
                let uu____26734 = desugar_binders env1 eff_binders in
                match uu____26734 with
                | (env2, binders) ->
                    let uu____26771 =
                      let uu____26782 = head_and_args defn in
                      match uu____26782 with
                      | (head1, args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____26819 ->
                                let uu____26820 =
                                  let uu____26826 =
                                    let uu____26828 =
                                      let uu____26830 =
                                        FStar_Parser_AST.term_to_string head1 in
                                      Prims.op_Hat uu____26830 " not found" in
                                    Prims.op_Hat "Effect " uu____26828 in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____26826) in
                                FStar_Errors.raise_error uu____26820
                                  d.FStar_Parser_AST.drange in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid in
                          let uu____26836 =
                            match FStar_List.rev args with
                            | (last_arg, uu____26866)::args_rev ->
                                let uu____26878 =
                                  let uu____26879 = unparen last_arg in
                                  uu____26879.FStar_Parser_AST.tm in
                                (match uu____26878 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____26907 -> ([], args))
                            | uu____26916 -> ([], args) in
                          (match uu____26836 with
                           | (cattributes, args1) ->
                               let uu____26959 = desugar_args env2 args1 in
                               let uu____26960 =
                                 desugar_attributes env2 cattributes in
                               (lid, ed, uu____26959, uu____26960)) in
                    (match uu____26771 with
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
                          (let uu____27000 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit in
                           match uu____27000 with
                           | (ed_binders, uu____27014, ed_binders_opening) ->
                               let sub' shift_n uu____27033 =
                                 match uu____27033 with
                                 | (us, x) ->
                                     let x1 =
                                       let uu____27048 =
                                         FStar_Syntax_Subst.shift_subst
                                           (shift_n + (FStar_List.length us))
                                           ed_binders_opening in
                                       FStar_Syntax_Subst.subst uu____27048 x in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args in
                                     let uu____27052 =
                                       let uu____27053 =
                                         FStar_Syntax_Subst.subst s x1 in
                                       (us, uu____27053) in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____27052 in
                               let sub1 = sub' Prims.int_zero in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name in
                               let ed1 =
                                 let uu____27074 =
                                   sub1 ed.FStar_Syntax_Syntax.signature in
                                 let uu____27075 =
                                   FStar_Syntax_Util.apply_eff_combinators
                                     sub1 ed.FStar_Syntax_Syntax.combinators in
                                 let uu____27076 =
                                   FStar_List.map
                                     (fun action ->
                                        let nparam =
                                          FStar_List.length
                                            action.FStar_Syntax_Syntax.action_params in
                                        let uu____27092 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name in
                                        let uu____27093 =
                                          let uu____27094 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn)) in
                                          FStar_Pervasives_Native.snd
                                            uu____27094 in
                                        let uu____27109 =
                                          let uu____27110 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ)) in
                                          FStar_Pervasives_Native.snd
                                            uu____27110 in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____27092;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____27093;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____27109
                                        }) ed.FStar_Syntax_Syntax.actions in
                                 {
                                   FStar_Syntax_Syntax.mname = mname;
                                   FStar_Syntax_Syntax.cattributes =
                                     cattributes;
                                   FStar_Syntax_Syntax.univs =
                                     (ed.FStar_Syntax_Syntax.univs);
                                   FStar_Syntax_Syntax.binders = binders1;
                                   FStar_Syntax_Syntax.signature =
                                     uu____27074;
                                   FStar_Syntax_Syntax.combinators =
                                     uu____27075;
                                   FStar_Syntax_Syntax.actions = uu____27076;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 } in
                               let se =
                                 let uu____27126 =
                                   let uu____27129 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname) in
                                   FStar_List.map uu____27129 quals in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (FStar_Syntax_Syntax.Sig_new_effect ed1);
                                   FStar_Syntax_Syntax.sigrng =
                                     (d.FStar_Parser_AST.drange);
                                   FStar_Syntax_Syntax.sigquals = uu____27126;
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
                                 FStar_Syntax_DsEnv.push_doc env3 ed_lid
                                   d.FStar_Parser_AST.doc in
                               let env5 =
                                 FStar_All.pipe_right
                                   ed1.FStar_Syntax_Syntax.actions
                                   (FStar_List.fold_left
                                      (fun env5 ->
                                         fun a ->
                                           let doc1 =
                                             FStar_Syntax_DsEnv.try_lookup_doc
                                               env5
                                               a.FStar_Syntax_Syntax.action_name in
                                           let env6 =
                                             let uu____27150 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____27150 in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4) in
                               let env6 =
                                 let uu____27152 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable) in
                                 if uu____27152
                                 then
                                   let reflect_lid =
                                     let uu____27159 =
                                       FStar_Ident.id_of_text "reflect" in
                                     FStar_All.pipe_right uu____27159
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
                                   FStar_Syntax_DsEnv.push_sigelt env5
                                     refl_decl
                                 else env5 in
                               let env7 =
                                 FStar_Syntax_DsEnv.push_doc env6 mname
                                   d.FStar_Parser_AST.doc in
                               (env7, [se]))))
and (mk_comment_attr :
  FStar_Parser_AST.decl ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list)
  =
  fun d ->
    let uu____27171 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc in
    match uu____27171 with
    | (text, kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.op_Hat "  " (Prims.op_Hat s "\n") in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____27258 ->
              let uu____27261 =
                let uu____27263 =
                  FStar_Parser_ToDocument.signature_to_document d in
                FStar_Pprint.pretty_string 0.95 (Prims.of_int (80))
                  uu____27263 in
              Prims.op_Hat "\n  " uu____27261
          | uu____27266 -> "" in
        let other =
          FStar_List.filter_map
            (fun uu____27285 ->
               match uu____27285 with
               | (k, v1) ->
                   if (k <> "summary") && (k <> "type")
                   then
                     FStar_Pervasives_Native.Some
                       (Prims.op_Hat k (Prims.op_Hat ": " v1))
                   else FStar_Pervasives_Native.None) kv in
        let other1 =
          if other <> []
          then Prims.op_Hat (FStar_String.concat "\n" other) "\n"
          else "" in
        let str =
          Prims.op_Hat summary (Prims.op_Hat pp (Prims.op_Hat other1 text)) in
        let fv =
          let uu____27330 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment" in
          FStar_Syntax_Syntax.fvar uu____27330
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        if str = ""
        then []
        else
          (let arg = FStar_Syntax_Util.exp_string str in
           let uu____27344 =
             let uu____27347 =
               let uu____27358 = FStar_Syntax_Syntax.as_arg arg in
               [uu____27358] in
             FStar_Syntax_Util.mk_app fv uu____27347 in
           [uu____27344])
and (desugar_decl_aux :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts))
  =
  fun env ->
    fun d ->
      let env0 =
        let uu____27394 = FStar_Syntax_DsEnv.snapshot env in
        FStar_All.pipe_right uu____27394 FStar_Pervasives_Native.snd in
      let uu____27406 = desugar_decl_noattrs env d in
      match uu____27406 with
      | (env1, sigelts) ->
          let attrs =
            FStar_List.map (desugar_term env1) d.FStar_Parser_AST.attrs in
          let val_attrs =
            match sigelts with
            | {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                  uu____27433;
                FStar_Syntax_Syntax.sigrng = uu____27434;
                FStar_Syntax_Syntax.sigquals = uu____27435;
                FStar_Syntax_Syntax.sigmeta = uu____27436;
                FStar_Syntax_Syntax.sigattrs = uu____27437;
                FStar_Syntax_Syntax.sigopts = uu____27438;_}::[] ->
                let uu____27451 =
                  let uu____27454 =
                    let uu____27457 = FStar_List.hd sigelts in
                    FStar_Syntax_Util.lids_of_sigelt uu____27457 in
                  FStar_All.pipe_right uu____27454
                    (FStar_List.collect
                       (fun nm ->
                          let uu____27465 =
                            FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                              env0 nm in
                          FStar_Pervasives_Native.snd uu____27465)) in
                FStar_All.pipe_right uu____27451
                  (FStar_List.filter
                     (fun t ->
                        let uu____27487 = get_fail_attr false t in
                        FStar_Option.isNone uu____27487))
            | {
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_inductive_typ uu____27507;
                FStar_Syntax_Syntax.sigrng = uu____27508;
                FStar_Syntax_Syntax.sigquals = uu____27509;
                FStar_Syntax_Syntax.sigmeta = uu____27510;
                FStar_Syntax_Syntax.sigattrs = uu____27511;
                FStar_Syntax_Syntax.sigopts = uu____27512;_}::uu____27513 ->
                let uu____27538 =
                  let uu____27541 =
                    let uu____27544 = FStar_List.hd sigelts in
                    FStar_Syntax_Util.lids_of_sigelt uu____27544 in
                  FStar_All.pipe_right uu____27541
                    (FStar_List.collect
                       (fun nm ->
                          let uu____27552 =
                            FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                              env0 nm in
                          FStar_Pervasives_Native.snd uu____27552)) in
                FStar_All.pipe_right uu____27538
                  (FStar_List.filter
                     (fun t ->
                        let uu____27574 = get_fail_attr false t in
                        FStar_Option.isNone uu____27574))
            | uu____27594 -> [] in
          let attrs1 =
            let uu____27602 = mk_comment_attr d in
            FStar_List.append uu____27602 (FStar_List.append attrs val_attrs) in
          let uu____27611 =
            FStar_List.mapi
              (fun i ->
                 fun sigelt ->
                   if i = Prims.int_zero
                   then
                     let uu___3464_27621 = sigelt in
                     {
                       FStar_Syntax_Syntax.sigel =
                         (uu___3464_27621.FStar_Syntax_Syntax.sigel);
                       FStar_Syntax_Syntax.sigrng =
                         (uu___3464_27621.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___3464_27621.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___3464_27621.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs = attrs1;
                       FStar_Syntax_Syntax.sigopts =
                         (uu___3464_27621.FStar_Syntax_Syntax.sigopts)
                     }
                   else
                     (let uu___3466_27624 = sigelt in
                      let uu____27625 =
                        FStar_List.filter
                          (fun at1 ->
                             let uu____27631 = get_fail_attr false at1 in
                             FStar_Option.isNone uu____27631) attrs1 in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___3466_27624.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___3466_27624.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___3466_27624.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___3466_27624.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs = uu____27625;
                        FStar_Syntax_Syntax.sigopts =
                          (uu___3466_27624.FStar_Syntax_Syntax.sigopts)
                      })) sigelts in
          (env1, uu____27611)
and (desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env ->
    fun d ->
      let uu____27657 = desugar_decl_aux env d in
      match uu____27657 with
      | (env1, ses) ->
          let uu____27668 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs) in
          (env1, uu____27668)
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
      | FStar_Parser_AST.Fsdoc uu____27696 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid in (env1, [])
      | FStar_Parser_AST.Friend lid ->
          let uu____27701 = FStar_Syntax_DsEnv.iface env in
          if uu____27701
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____27716 =
               let uu____27718 =
                 let uu____27720 = FStar_Syntax_DsEnv.dep_graph env in
                 let uu____27721 = FStar_Syntax_DsEnv.current_module env in
                 FStar_Parser_Dep.module_has_interface uu____27720
                   uu____27721 in
               Prims.op_Negation uu____27718 in
             if uu____27716
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____27735 =
                  let uu____27737 =
                    let uu____27739 = FStar_Syntax_DsEnv.dep_graph env in
                    FStar_Parser_Dep.module_has_interface uu____27739 lid in
                  Prims.op_Negation uu____27737 in
                if uu____27735
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____27753 =
                     let uu____27755 =
                       let uu____27757 = FStar_Syntax_DsEnv.dep_graph env in
                       FStar_Parser_Dep.deps_has_implementation uu____27757
                         lid in
                     Prims.op_Negation uu____27755 in
                   if uu____27753
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x, l) ->
          let uu____27775 = FStar_Syntax_DsEnv.push_module_abbrev env x l in
          (uu____27775, [])
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
              | (FStar_Parser_AST.TyconRecord uu____27816, uu____27817)::[]
                  -> FStar_Parser_AST.Noeq :: quals1
              | uu____27856 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1 in
          let tcs1 =
            FStar_List.map
              (fun uu____27883 ->
                 match uu____27883 with | (x, uu____27891) -> x) tcs in
          let uu____27896 =
            let uu____27901 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2 in
            desugar_tycon env d uu____27901 tcs1 in
          (match uu____27896 with
           | (env1, ses) ->
               let mkclass lid =
                 let uu____27918 =
                   let uu____27919 =
                     let uu____27926 =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun in
                     FStar_Syntax_Syntax.mk_binder uu____27926 in
                   [uu____27919] in
                 let uu____27939 =
                   let uu____27942 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid in
                   let uu____27945 =
                     let uu____27956 =
                       let uu____27965 =
                         let uu____27966 = FStar_Ident.string_of_lid lid in
                         FStar_Syntax_Util.exp_string uu____27966 in
                       FStar_Syntax_Syntax.as_arg uu____27965 in
                     [uu____27956] in
                   FStar_Syntax_Util.mk_app uu____27942 uu____27945 in
                 FStar_Syntax_Util.abs uu____27918 uu____27939
                   FStar_Pervasives_Native.None in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____28006, id1))::uu____28008 ->
                       FStar_Pervasives_Native.Some id1
                   | uu____28011::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None in
                 let uu____28015 = get_fname se.FStar_Syntax_Syntax.sigquals in
                 match uu____28015 with
                 | FStar_Pervasives_Native.None -> []
                 | FStar_Pervasives_Native.Some id1 ->
                     let uu____28021 = FStar_Syntax_DsEnv.qualify env1 id1 in
                     [uu____28021] in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1, uu____28042) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid, uu____28052, uu____28053, uu____28054,
                      uu____28055, uu____28056)
                     ->
                     let uu____28065 =
                       let uu____28066 =
                         let uu____28067 =
                           let uu____28074 = mkclass lid in
                           (meths, uu____28074) in
                         FStar_Syntax_Syntax.Sig_splice uu____28067 in
                       {
                         FStar_Syntax_Syntax.sigel = uu____28066;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = [];
                         FStar_Syntax_Syntax.sigopts =
                           FStar_Pervasives_Native.None
                       } in
                     [uu____28065]
                 | uu____28077 -> [] in
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
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____28111;
                    FStar_Parser_AST.prange = uu____28112;_},
                  uu____28113)::[] -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____28123;
                    FStar_Parser_AST.prange = uu____28124;_},
                  uu____28125)::[] -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____28141;
                         FStar_Parser_AST.prange = uu____28142;_},
                       uu____28143);
                    FStar_Parser_AST.prange = uu____28144;_},
                  uu____28145)::[] -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____28167;
                         FStar_Parser_AST.prange = uu____28168;_},
                       uu____28169);
                    FStar_Parser_AST.prange = uu____28170;_},
                  uu____28171)::[] -> false
               | (p, uu____28200)::[] ->
                   let uu____28209 = is_app_pattern p in
                   Prims.op_Negation uu____28209
               | uu____28211 -> false) in
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
            let uu____28286 = desugar_term_maybe_top true env as_inner_let in
            (match uu____28286 with
             | (ds_lets, aq) ->
                 (check_no_aq aq;
                  (let uu____28299 =
                     let uu____28300 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets in
                     uu____28300.FStar_Syntax_Syntax.n in
                   match uu____28299 with
                   | FStar_Syntax_Syntax.Tm_let (lbs, uu____28310) ->
                       let fvs =
                         FStar_All.pipe_right
                           (FStar_Pervasives_Native.snd lbs)
                           (FStar_List.map
                              (fun lb ->
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname)) in
                       let uu____28341 =
                         FStar_List.fold_right
                           (fun fv ->
                              fun uu____28366 ->
                                match uu____28366 with
                                | (qs, ats) ->
                                    let uu____28393 =
                                      FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                                        env
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    (match uu____28393 with
                                     | (qs', ats') ->
                                         ((FStar_List.append qs' qs),
                                           (FStar_List.append ats' ats))))
                           fvs ([], []) in
                       (match uu____28341 with
                        | (val_quals, val_attrs) ->
                            let quals1 =
                              match quals with
                              | uu____28447::uu____28448 ->
                                  FStar_List.map
                                    (trans_qual1 FStar_Pervasives_Native.None)
                                    quals
                              | uu____28451 -> val_quals in
                            let quals2 =
                              let uu____28455 =
                                FStar_All.pipe_right lets1
                                  (FStar_Util.for_some
                                     (fun uu____28488 ->
                                        match uu____28488 with
                                        | (uu____28502, (uu____28503, t)) ->
                                            t.FStar_Parser_AST.level =
                                              FStar_Parser_AST.Formula)) in
                              if uu____28455
                              then FStar_Syntax_Syntax.Logic :: quals1
                              else quals1 in
                            let lbs1 =
                              let uu____28523 =
                                FStar_All.pipe_right quals2
                                  (FStar_List.contains
                                     FStar_Syntax_Syntax.Abstract) in
                              if uu____28523
                              then
                                let uu____28529 =
                                  FStar_All.pipe_right
                                    (FStar_Pervasives_Native.snd lbs)
                                    (FStar_List.map
                                       (fun lb ->
                                          let fv =
                                            FStar_Util.right
                                              lb.FStar_Syntax_Syntax.lbname in
                                          let uu___3652_28544 = lb in
                                          {
                                            FStar_Syntax_Syntax.lbname =
                                              (FStar_Util.Inr
                                                 (let uu___3654_28546 = fv in
                                                  {
                                                    FStar_Syntax_Syntax.fv_name
                                                      =
                                                      (uu___3654_28546.FStar_Syntax_Syntax.fv_name);
                                                    FStar_Syntax_Syntax.fv_delta
                                                      =
                                                      (FStar_Syntax_Syntax.Delta_abstract
                                                         (fv.FStar_Syntax_Syntax.fv_delta));
                                                    FStar_Syntax_Syntax.fv_qual
                                                      =
                                                      (uu___3654_28546.FStar_Syntax_Syntax.fv_qual)
                                                  }));
                                            FStar_Syntax_Syntax.lbunivs =
                                              (uu___3652_28544.FStar_Syntax_Syntax.lbunivs);
                                            FStar_Syntax_Syntax.lbtyp =
                                              (uu___3652_28544.FStar_Syntax_Syntax.lbtyp);
                                            FStar_Syntax_Syntax.lbeff =
                                              (uu___3652_28544.FStar_Syntax_Syntax.lbeff);
                                            FStar_Syntax_Syntax.lbdef =
                                              (uu___3652_28544.FStar_Syntax_Syntax.lbdef);
                                            FStar_Syntax_Syntax.lbattrs =
                                              (uu___3652_28544.FStar_Syntax_Syntax.lbattrs);
                                            FStar_Syntax_Syntax.lbpos =
                                              (uu___3652_28544.FStar_Syntax_Syntax.lbpos)
                                          })) in
                                ((FStar_Pervasives_Native.fst lbs),
                                  uu____28529)
                              else lbs in
                            let names1 =
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
                                  (FStar_Syntax_Syntax.Sig_let (lbs1, names1));
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
                            let env2 =
                              FStar_List.fold_left
                                (fun env2 ->
                                   fun id1 ->
                                     FStar_Syntax_DsEnv.push_doc env2 id1
                                       d.FStar_Parser_AST.doc) env1 names1 in
                            (env2, [s]))
                   | uu____28576 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____28584 =
               match lets with
               | (pat, body)::[] -> (pat, body)
               | uu____28603 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets" in
             match uu____28584 with
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
                       let uu___3680_28640 = pat1 in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___3680_28640.FStar_Parser_AST.prange)
                       }
                   | uu____28647 -> var_pat in
                 let main_let =
                   desugar_decl env
                     (let uu___3684_28654 = d in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___3684_28654.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___3684_28654.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___3684_28654.FStar_Parser_AST.attrs)
                      }) in
                 let build_projection uu____28690 id1 =
                   match uu____28690 with
                   | (env1, ses) ->
                       let main =
                         let uu____28711 =
                           let uu____28712 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name] in
                           FStar_Parser_AST.Var uu____28712 in
                         FStar_Parser_AST.mk_term uu____28711
                           FStar_Range.dummyRange FStar_Parser_AST.Expr in
                       let lid = FStar_Ident.lid_of_ids [id1] in
                       let projectee =
                         FStar_Parser_AST.mk_term (FStar_Parser_AST.Var lid)
                           FStar_Range.dummyRange FStar_Parser_AST.Expr in
                       let body1 =
                         FStar_Parser_AST.mk_term
                           (FStar_Parser_AST.Match
                              (main,
                                [(pat, FStar_Pervasives_Native.None,
                                   projectee)])) FStar_Range.dummyRange
                           FStar_Parser_AST.Expr in
                       let bv_pat =
                         FStar_Parser_AST.mk_pattern
                           (FStar_Parser_AST.PatVar
                              (id1, FStar_Pervasives_Native.None))
                           FStar_Range.dummyRange in
                       let id_decl =
                         FStar_Parser_AST.mk_decl
                           (FStar_Parser_AST.TopLevelLet
                              (FStar_Parser_AST.NoLetQualifier,
                                [(bv_pat, body1)])) FStar_Range.dummyRange [] in
                       let uu____28762 = desugar_decl env1 id_decl in
                       (match uu____28762 with
                        | (env2, ses') ->
                            (env2, (FStar_List.append ses ses'))) in
                 let bvs =
                   let uu____28780 = gather_pattern_bound_vars true pat in
                   FStar_All.pipe_right uu____28780 FStar_Util.set_elements in
                 FStar_List.fold_left build_projection main_let bvs)
      | FStar_Parser_AST.Main t ->
          let e = desugar_term env t in
          let se =
            {
              FStar_Syntax_Syntax.sigel = (FStar_Syntax_Syntax.Sig_main e);
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = [];
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = [];
              FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
            } in
          (env, [se])
      | FStar_Parser_AST.Assume (id1, t) ->
          let f = desugar_formula env t in
          let lid = FStar_Syntax_DsEnv.qualify env id1 in
          let env1 =
            FStar_Syntax_DsEnv.push_doc env lid d.FStar_Parser_AST.doc in
          (env1,
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
      | FStar_Parser_AST.Val (id1, t) ->
          let quals = d.FStar_Parser_AST.quals in
          let t1 =
            let uu____28804 = close_fun env t in desugar_term env uu____28804 in
          let quals1 =
            let uu____28808 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env) in
            if uu____28808
            then FStar_Parser_AST.Assumption :: quals
            else quals in
          let lid = FStar_Syntax_DsEnv.qualify env id1 in
          let attrs =
            FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs in
          let se =
            let uu____28820 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1 in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____28820;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = attrs;
              FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
            } in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se in
          let env2 =
            FStar_Syntax_DsEnv.push_doc env1 lid d.FStar_Parser_AST.doc in
          (env2, [se])
      | FStar_Parser_AST.Exception (id1, t_opt) ->
          let t =
            match t_opt with
            | FStar_Pervasives_Native.None ->
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_lid env)
                  FStar_Parser_Const.exn_lid
            | FStar_Pervasives_Native.Some term ->
                let t = desugar_term env term in
                let uu____28834 =
                  let uu____28843 = FStar_Syntax_Syntax.null_binder t in
                  [uu____28843] in
                let uu____28862 =
                  let uu____28865 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total
                    uu____28865 in
                FStar_Syntax_Util.arrow uu____28834 uu____28862 in
          let l = FStar_Syntax_DsEnv.qualify env id1 in
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
          let env2 =
            FStar_Syntax_DsEnv.push_doc env1 l d.FStar_Parser_AST.doc in
          let data_ops = mk_data_projector_names [] env2 se in
          let discs = mk_data_discriminators [] env2 [l] in
          let env3 =
            FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt env2
              (FStar_List.append discs data_ops) in
          (env3, (FStar_List.append (se' :: discs) data_ops))
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
      | FStar_Parser_AST.SubEffect l ->
          let lookup1 l1 =
            let uu____28936 =
              FStar_Syntax_DsEnv.try_lookup_effect_defn env l1 in
            match uu____28936 with
            | FStar_Pervasives_Native.None ->
                let uu____28939 =
                  let uu____28945 =
                    let uu____28947 =
                      let uu____28949 = FStar_Syntax_Print.lid_to_string l1 in
                      Prims.op_Hat uu____28949 " not found" in
                    Prims.op_Hat "Effect name " uu____28947 in
                  (FStar_Errors.Fatal_EffectNotFound, uu____28945) in
                FStar_Errors.raise_error uu____28939
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2 in
          let src_ed = lookup1 l.FStar_Parser_AST.msource in
          let dst_ed = lookup1 l.FStar_Parser_AST.mdest in
          let uu____28957 =
            let uu____28959 =
              (FStar_Syntax_Util.is_layered src_ed) ||
                (FStar_Syntax_Util.is_layered dst_ed) in
            Prims.op_Negation uu____28959 in
          if uu____28957
          then
            let uu____28966 =
              match l.FStar_Parser_AST.lift_op with
              | FStar_Parser_AST.NonReifiableLift t ->
                  let uu____28984 =
                    let uu____28987 =
                      let uu____28988 = desugar_term env t in
                      ([], uu____28988) in
                    FStar_Pervasives_Native.Some uu____28987 in
                  (uu____28984, FStar_Pervasives_Native.None)
              | FStar_Parser_AST.ReifiableLift (wp, t) ->
                  let uu____29001 =
                    let uu____29004 =
                      let uu____29005 = desugar_term env wp in
                      ([], uu____29005) in
                    FStar_Pervasives_Native.Some uu____29004 in
                  let uu____29012 =
                    let uu____29015 =
                      let uu____29016 = desugar_term env t in
                      ([], uu____29016) in
                    FStar_Pervasives_Native.Some uu____29015 in
                  (uu____29001, uu____29012)
              | FStar_Parser_AST.LiftForFree t ->
                  let uu____29028 =
                    let uu____29031 =
                      let uu____29032 = desugar_term env t in
                      ([], uu____29032) in
                    FStar_Pervasives_Native.Some uu____29031 in
                  (FStar_Pervasives_Native.None, uu____29028) in
            (match uu____28966 with
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
                   let uu____29066 =
                     let uu____29069 =
                       let uu____29070 = desugar_term env t in
                       ([], uu____29070) in
                     FStar_Pervasives_Native.Some uu____29069 in
                   {
                     FStar_Syntax_Syntax.source =
                       (src_ed.FStar_Syntax_Syntax.mname);
                     FStar_Syntax_Syntax.target =
                       (dst_ed.FStar_Syntax_Syntax.mname);
                     FStar_Syntax_Syntax.lift_wp =
                       FStar_Pervasives_Native.None;
                     FStar_Syntax_Syntax.lift = uu____29066
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
             | uu____29077 ->
                 failwith
                   "Impossible! unexpected lift_op for lift to a layered effect")
      | FStar_Parser_AST.Splice (ids, t) ->
          let t1 = desugar_term env t in
          let se =
            let uu____29091 =
              let uu____29092 =
                let uu____29099 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids in
                (uu____29099, t1) in
              FStar_Syntax_Syntax.Sig_splice uu____29092 in
            {
              FStar_Syntax_Syntax.sigel = uu____29091;
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
      let uu____29126 =
        FStar_List.fold_left
          (fun uu____29146 ->
             fun d ->
               match uu____29146 with
               | (env1, sigelts) ->
                   let uu____29166 = desugar_decl env1 d in
                   (match uu____29166 with
                    | (env2, se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls in
      match uu____29126 with | (env1, sigelts) -> (env1, sigelts)
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
          | (FStar_Pervasives_Native.None, uu____29257) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____29261;
               FStar_Syntax_Syntax.exports = uu____29262;
               FStar_Syntax_Syntax.is_interface = uu____29263;_},
             FStar_Parser_AST.Module (current_lid, uu____29265)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod, uu____29274) ->
              let uu____29277 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod in
              FStar_Pervasives_Native.fst uu____29277 in
        let uu____29282 =
          match m with
          | FStar_Parser_AST.Interface (mname, decls, admitted) ->
              let uu____29324 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii in
              (uu____29324, mname, decls, true)
          | FStar_Parser_AST.Module (mname, decls) ->
              let uu____29346 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii in
              (uu____29346, mname, decls, false) in
        match uu____29282 with
        | ((env2, pop_when_done), mname, decls, intf) ->
            let uu____29388 = desugar_decls env2 decls in
            (match uu____29388 with
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
          let uu____29456 =
            (FStar_Options.interactive ()) &&
              (let uu____29459 =
                 let uu____29461 =
                   let uu____29463 = FStar_Options.file_list () in
                   FStar_List.hd uu____29463 in
                 FStar_Util.get_file_extension uu____29461 in
               FStar_List.mem uu____29459 ["fsti"; "fsi"]) in
          if uu____29456 then as_interface m else m in
        let uu____29477 = desugar_modul_common curmod env m1 in
        match uu____29477 with
        | (env1, modul, pop_when_done) ->
            if pop_when_done
            then
              let uu____29499 = FStar_Syntax_DsEnv.pop () in
              (uu____29499, modul)
            else (env1, modul)
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun env ->
    fun m ->
      let uu____29521 =
        desugar_modul_common FStar_Pervasives_Native.None env m in
      match uu____29521 with
      | (env1, modul, pop_when_done) ->
          let uu____29538 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul in
          (match uu____29538 with
           | (env2, modul1) ->
               ((let uu____29550 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str in
                 if uu____29550
                 then
                   let uu____29553 =
                     FStar_Syntax_Print.modul_to_string modul1 in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____29553
                 else ());
                (let uu____29558 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2 in
                 (uu____29558, modul1))))
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
        (fun uu____29608 ->
           let uu____29609 = desugar_modul env modul in
           match uu____29609 with | (e, m) -> (m, e))
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls ->
    fun env ->
      with_options
        (fun uu____29647 ->
           let uu____29648 = desugar_decls env decls in
           match uu____29648 with | (env1, sigelts) -> (sigelts, env1))
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul ->
    fun a_modul ->
      fun env ->
        with_options
          (fun uu____29699 ->
             let uu____29700 = desugar_partial_modul modul env a_modul in
             match uu____29700 with | (env1, modul1) -> (modul1, env1))
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
              | uu____29795 ->
                  let t =
                    let uu____29805 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange in
                    erase_univs uu____29805 in
                  let uu____29818 =
                    let uu____29819 = FStar_Syntax_Subst.compress t in
                    uu____29819.FStar_Syntax_Syntax.n in
                  (match uu____29818 with
                   | FStar_Syntax_Syntax.Tm_abs
                       (bs1, uu____29831, uu____29832) -> bs1
                   | uu____29857 -> failwith "Impossible") in
            let uu____29867 =
              let uu____29874 = erase_binders ed.FStar_Syntax_Syntax.binders in
              FStar_Syntax_Subst.open_term' uu____29874
                FStar_Syntax_Syntax.t_unit in
            match uu____29867 with
            | (binders, uu____29876, binders_opening) ->
                let erase_term t =
                  let uu____29884 =
                    let uu____29885 =
                      FStar_Syntax_Subst.subst binders_opening t in
                    erase_univs uu____29885 in
                  FStar_Syntax_Subst.close binders uu____29884 in
                let erase_tscheme uu____29903 =
                  match uu____29903 with
                  | (us, t) ->
                      let t1 =
                        let uu____29923 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening in
                        FStar_Syntax_Subst.subst uu____29923 t in
                      let uu____29926 =
                        let uu____29927 = erase_univs t1 in
                        FStar_Syntax_Subst.close binders uu____29927 in
                      ([], uu____29926) in
                let erase_action action =
                  let opening =
                    FStar_Syntax_Subst.shift_subst
                      (FStar_List.length
                         action.FStar_Syntax_Syntax.action_univs)
                      binders_opening in
                  let erased_action_params =
                    match action.FStar_Syntax_Syntax.action_params with
                    | [] -> []
                    | uu____29950 ->
                        let bs =
                          let uu____29960 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params in
                          FStar_All.pipe_left erase_binders uu____29960 in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange in
                        let uu____30000 =
                          let uu____30001 =
                            let uu____30004 =
                              FStar_Syntax_Subst.close binders t in
                            FStar_Syntax_Subst.compress uu____30004 in
                          uu____30001.FStar_Syntax_Syntax.n in
                        (match uu____30000 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1, uu____30006, uu____30007) -> bs1
                         | uu____30032 -> failwith "Impossible") in
                  let erase_term1 t =
                    let uu____30040 =
                      let uu____30041 = FStar_Syntax_Subst.subst opening t in
                      erase_univs uu____30041 in
                    FStar_Syntax_Subst.close binders uu____30040 in
                  let uu___3956_30042 = action in
                  let uu____30043 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn in
                  let uu____30044 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___3956_30042.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___3956_30042.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____30043;
                    FStar_Syntax_Syntax.action_typ = uu____30044
                  } in
                let uu___3958_30045 = ed in
                let uu____30046 = FStar_Syntax_Subst.close_binders binders in
                let uu____30047 =
                  erase_tscheme ed.FStar_Syntax_Syntax.signature in
                let uu____30048 =
                  FStar_Syntax_Util.apply_eff_combinators erase_tscheme
                    ed.FStar_Syntax_Syntax.combinators in
                let uu____30049 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions in
                {
                  FStar_Syntax_Syntax.mname =
                    (uu___3958_30045.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.cattributes =
                    (uu___3958_30045.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____30046;
                  FStar_Syntax_Syntax.signature = uu____30047;
                  FStar_Syntax_Syntax.combinators = uu____30048;
                  FStar_Syntax_Syntax.actions = uu____30049;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___3958_30045.FStar_Syntax_Syntax.eff_attrs)
                } in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___3965_30065 = se in
                  let uu____30066 =
                    let uu____30067 = erase_univs_ed ed in
                    FStar_Syntax_Syntax.Sig_new_effect uu____30067 in
                  {
                    FStar_Syntax_Syntax.sigel = uu____30066;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___3965_30065.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___3965_30065.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___3965_30065.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___3965_30065.FStar_Syntax_Syntax.sigattrs);
                    FStar_Syntax_Syntax.sigopts =
                      (uu___3965_30065.FStar_Syntax_Syntax.sigopts)
                  } in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se' in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____30069 -> FStar_Syntax_DsEnv.push_sigelt env se in
          let uu____30070 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii in
          match uu____30070 with
          | (en1, pop_when_done) ->
              let en2 =
                let uu____30087 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name in
                FStar_List.fold_left push_sigelt1 uu____30087
                  m.FStar_Syntax_Syntax.exports in
              let env = FStar_Syntax_DsEnv.finish en2 m in
              let uu____30089 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env in
              ((), uu____30089)