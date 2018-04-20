open Prims
let (desugar_disjunctive_pattern :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t Prims.list ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.branch Prims.list)
  =
  fun pats ->
    fun when_opt ->
      fun branch1 ->
        FStar_All.pipe_right pats
          (FStar_List.map
             (fun pat -> FStar_Syntax_Util.branch (pat, when_opt, branch1)))
let (trans_aqual :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
  =
  fun uu___83_58 ->
    match uu___83_58 with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit) ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality) ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
    | uu____63 -> FStar_Pervasives_Native.None
let (trans_qual :
  FStar_Range.range ->
    FStar_Ident.lident FStar_Pervasives_Native.option ->
      FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier Prims.list)
  =
  fun r ->
    fun maybe_effect_id ->
      fun q ->
        match q with
        | FStar_Parser_AST.Logic ->
            (FStar_Errors.log_issue r
               (FStar_Errors.Warning_DeprecatedDefinition,
                 "The 'logic' qualifier is deprecated and redundant; please remove it");
             [])
        | uu____84 ->
            let uu____85 =
              match q with
              | FStar_Parser_AST.Private -> FStar_Syntax_Syntax.Private
              | FStar_Parser_AST.Assumption -> FStar_Syntax_Syntax.Assumption
              | FStar_Parser_AST.Unfold_for_unification_and_vcgen ->
                  FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
              | FStar_Parser_AST.Inline_for_extraction ->
                  FStar_Syntax_Syntax.Inline_for_extraction
              | FStar_Parser_AST.NoExtract -> FStar_Syntax_Syntax.NoExtract
              | FStar_Parser_AST.Irreducible ->
                  FStar_Syntax_Syntax.Irreducible
              | FStar_Parser_AST.TotalEffect ->
                  FStar_Syntax_Syntax.TotalEffect
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
              | FStar_Parser_AST.Logic ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_UnsupportedQualifier,
                      "Unsupported qualifier") r in
            [uu____85]
let (trans_pragma : FStar_Parser_AST.pragma -> FStar_Syntax_Syntax.pragma) =
  fun uu___84_90 ->
    match uu___84_90 with
    | FStar_Parser_AST.SetOptions s -> FStar_Syntax_Syntax.SetOptions s
    | FStar_Parser_AST.ResetOptions sopt ->
        FStar_Syntax_Syntax.ResetOptions sopt
    | FStar_Parser_AST.LightOff -> FStar_Syntax_Syntax.LightOff
let (as_imp :
  FStar_Parser_AST.imp ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
  =
  fun uu___85_99 ->
    match uu___85_99 with
    | FStar_Parser_AST.Hash ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | uu____102 -> FStar_Pervasives_Native.None
let arg_withimp_e :
  'Auu____106 .
    FStar_Parser_AST.imp ->
      'Auu____106 ->
        ('Auu____106,
          FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2
  = fun imp -> fun t -> (t, (as_imp imp))
let arg_withimp_t :
  'Auu____126 .
    FStar_Parser_AST.imp ->
      'Auu____126 ->
        ('Auu____126,
          FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2
  =
  fun imp ->
    fun t ->
      match imp with
      | FStar_Parser_AST.Hash ->
          (t, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag))
      | uu____143 -> (t, FStar_Pervasives_Native.None)
let (contains_binder : FStar_Parser_AST.binder Prims.list -> Prims.bool) =
  fun binders ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____158 -> true
            | uu____163 -> false))
let rec (unparen : FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun t ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____168 -> t
let (tm_type_z : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r ->
    let uu____172 =
      let uu____173 = FStar_Ident.lid_of_path ["Type0"] r in
      FStar_Parser_AST.Name uu____173 in
    FStar_Parser_AST.mk_term uu____172 r FStar_Parser_AST.Kind
let (tm_type : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r ->
    let uu____177 =
      let uu____178 = FStar_Ident.lid_of_path ["Type"] r in
      FStar_Parser_AST.Name uu____178 in
    FStar_Parser_AST.mk_term uu____177 r FStar_Parser_AST.Kind
let rec (is_comp_type :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun env ->
    fun t ->
      let uu____185 =
        let uu____186 = unparen t in uu____186.FStar_Parser_AST.tm in
      match uu____185 with
      | FStar_Parser_AST.Name l ->
          let uu____188 = FStar_Syntax_DsEnv.try_lookup_effect_name env l in
          FStar_All.pipe_right uu____188 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l, uu____194) ->
          let uu____207 = FStar_Syntax_DsEnv.try_lookup_effect_name env l in
          FStar_All.pipe_right uu____207 FStar_Option.isSome
      | FStar_Parser_AST.App (head1, uu____213, uu____214) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1, uu____217, uu____218) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____223, t1) -> is_comp_type env t1
      | uu____225 -> false
let (unit_ty : FStar_Parser_AST.term) =
  FStar_Parser_AST.mk_term
    (FStar_Parser_AST.Name FStar_Parser_Const.unit_lid)
    FStar_Range.dummyRange FStar_Parser_AST.Type_level
let (compile_op_lid :
  Prims.int -> Prims.string -> FStar_Range.range -> FStar_Ident.lident) =
  fun n1 ->
    fun s ->
      fun r ->
        let uu____235 =
          let uu____238 =
            let uu____239 =
              let uu____244 = FStar_Parser_AST.compile_op n1 s r in
              (uu____244, r) in
            FStar_Ident.mk_ident uu____239 in
          [uu____238] in
        FStar_All.pipe_right uu____235 FStar_Ident.lid_of_ids
let op_as_term :
  'Auu____252 .
    FStar_Syntax_DsEnv.env ->
      Prims.int ->
        'Auu____252 ->
          FStar_Ident.ident ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env ->
    fun arity ->
      fun rng ->
        fun op ->
          let r l dd =
            let uu____280 =
              let uu____281 =
                FStar_Syntax_Syntax.lid_as_fv
                  (FStar_Ident.set_lid_range l op.FStar_Ident.idRange) dd
                  FStar_Pervasives_Native.None in
              FStar_All.pipe_right uu____281 FStar_Syntax_Syntax.fv_to_tm in
            FStar_Pervasives_Native.Some uu____280 in
          let fallback uu____287 =
            match FStar_Ident.text_of_id op with
            | "=" ->
                r FStar_Parser_Const.op_Eq
                  FStar_Syntax_Syntax.Delta_equational
            | ":=" ->
                r FStar_Parser_Const.write_lid
                  FStar_Syntax_Syntax.Delta_equational
            | "<" ->
                r FStar_Parser_Const.op_LT
                  FStar_Syntax_Syntax.Delta_equational
            | "<=" ->
                r FStar_Parser_Const.op_LTE
                  FStar_Syntax_Syntax.Delta_equational
            | ">" ->
                r FStar_Parser_Const.op_GT
                  FStar_Syntax_Syntax.Delta_equational
            | ">=" ->
                r FStar_Parser_Const.op_GTE
                  FStar_Syntax_Syntax.Delta_equational
            | "&&" ->
                r FStar_Parser_Const.op_And
                  FStar_Syntax_Syntax.Delta_equational
            | "||" ->
                r FStar_Parser_Const.op_Or
                  FStar_Syntax_Syntax.Delta_equational
            | "+" ->
                r FStar_Parser_Const.op_Addition
                  FStar_Syntax_Syntax.Delta_equational
            | "-" when arity = (Prims.parse_int "1") ->
                r FStar_Parser_Const.op_Minus
                  FStar_Syntax_Syntax.Delta_equational
            | "-" ->
                r FStar_Parser_Const.op_Subtraction
                  FStar_Syntax_Syntax.Delta_equational
            | "/" ->
                r FStar_Parser_Const.op_Division
                  FStar_Syntax_Syntax.Delta_equational
            | "%" ->
                r FStar_Parser_Const.op_Modulus
                  FStar_Syntax_Syntax.Delta_equational
            | "!" ->
                r FStar_Parser_Const.read_lid
                  FStar_Syntax_Syntax.Delta_equational
            | "@" ->
                let uu____290 = FStar_Options.ml_ish () in
                if uu____290
                then
                  r FStar_Parser_Const.list_append_lid
                    FStar_Syntax_Syntax.Delta_equational
                else
                  r FStar_Parser_Const.list_tot_append_lid
                    FStar_Syntax_Syntax.Delta_equational
            | "^" ->
                r FStar_Parser_Const.strcat_lid
                  FStar_Syntax_Syntax.Delta_equational
            | "|>" ->
                r FStar_Parser_Const.pipe_right_lid
                  FStar_Syntax_Syntax.Delta_equational
            | "<|" ->
                r FStar_Parser_Const.pipe_left_lid
                  FStar_Syntax_Syntax.Delta_equational
            | "<>" ->
                r FStar_Parser_Const.op_notEq
                  FStar_Syntax_Syntax.Delta_equational
            | "~" ->
                r FStar_Parser_Const.not_lid
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "2"))
            | "==" ->
                r FStar_Parser_Const.eq2_lid
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "2"))
            | "<<" ->
                r FStar_Parser_Const.precedes_lid
                  FStar_Syntax_Syntax.Delta_constant
            | "/\\" ->
                r FStar_Parser_Const.and_lid
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1"))
            | "\\/" ->
                r FStar_Parser_Const.or_lid
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1"))
            | "==>" ->
                r FStar_Parser_Const.imp_lid
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "1"))
            | "<==>" ->
                r FStar_Parser_Const.iff_lid
                  (FStar_Syntax_Syntax.Delta_defined_at_level
                     (Prims.parse_int "2"))
            | uu____294 -> FStar_Pervasives_Native.None in
          let uu____295 =
            let uu____302 =
              compile_op_lid arity op.FStar_Ident.idText
                op.FStar_Ident.idRange in
            FStar_Syntax_DsEnv.try_lookup_lid env uu____302 in
          match uu____295 with
          | FStar_Pervasives_Native.Some t ->
              FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst t)
          | uu____314 -> fallback ()
let (sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list)
  =
  fun ftv ->
    let uu____330 =
      FStar_Util.remove_dups
        (fun x -> fun y -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x ->
            fun y ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____330
let rec (free_type_vars_b :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Syntax_DsEnv.env, FStar_Ident.ident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun binder ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____369 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____373 = FStar_Syntax_DsEnv.push_bv env x in
          (match uu____373 with | (env1, uu____385) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____388, term) ->
          let uu____390 = free_type_vars env term in (env, uu____390)
      | FStar_Parser_AST.TAnnotated (id1, uu____396) ->
          let uu____397 = FStar_Syntax_DsEnv.push_bv env id1 in
          (match uu____397 with | (env1, uu____409) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____413 = free_type_vars env t in (env, uu____413)
and (free_type_vars :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list)
  =
  fun env ->
    fun t ->
      let uu____420 =
        let uu____421 = unparen t in uu____421.FStar_Parser_AST.tm in
      match uu____420 with
      | FStar_Parser_AST.Labeled uu____424 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____434 = FStar_Syntax_DsEnv.try_lookup_id env a in
          (match uu____434 with
           | FStar_Pervasives_Native.None -> [a]
           | uu____447 -> [])
      | FStar_Parser_AST.Wild -> []
      | FStar_Parser_AST.Const uu____454 -> []
      | FStar_Parser_AST.Uvar uu____455 -> []
      | FStar_Parser_AST.Var uu____456 -> []
      | FStar_Parser_AST.Projector uu____457 -> []
      | FStar_Parser_AST.Discrim uu____462 -> []
      | FStar_Parser_AST.Name uu____463 -> []
      | FStar_Parser_AST.Requires (t1, uu____465) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1, uu____471) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____476, t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1, t', tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None -> []
             | FStar_Pervasives_Native.Some t2 -> [t2]) in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____494, ts) ->
          FStar_List.collect
            (fun uu____515 ->
               match uu____515 with
               | (t1, uu____523) -> free_type_vars env t1) ts
      | FStar_Parser_AST.Op (uu____524, ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1, t2, uu____532) ->
          let uu____533 = free_type_vars env t1 in
          let uu____536 = free_type_vars env t2 in
          FStar_List.append uu____533 uu____536
      | FStar_Parser_AST.Refine (b, t1) ->
          let uu____541 = free_type_vars_b env b in
          (match uu____541 with
           | (env1, f) ->
               let uu____556 = free_type_vars env1 t1 in
               FStar_List.append f uu____556)
      | FStar_Parser_AST.Product (binders, body) ->
          let uu____565 =
            FStar_List.fold_left
              (fun uu____585 ->
                 fun binder ->
                   match uu____585 with
                   | (env1, free) ->
                       let uu____605 = free_type_vars_b env1 binder in
                       (match uu____605 with
                        | (env2, f) -> (env2, (FStar_List.append f free))))
              (env, []) binders in
          (match uu____565 with
           | (env1, free) ->
               let uu____636 = free_type_vars env1 body in
               FStar_List.append free uu____636)
      | FStar_Parser_AST.Sum (binders, body) ->
          let uu____645 =
            FStar_List.fold_left
              (fun uu____665 ->
                 fun binder ->
                   match uu____665 with
                   | (env1, free) ->
                       let uu____685 = free_type_vars_b env1 binder in
                       (match uu____685 with
                        | (env2, f) -> (env2, (FStar_List.append f free))))
              (env, []) binders in
          (match uu____645 with
           | (env1, free) ->
               let uu____716 = free_type_vars env1 body in
               FStar_List.append free uu____716)
      | FStar_Parser_AST.Project (t1, uu____720) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.Abs uu____724 -> []
      | FStar_Parser_AST.Let uu____731 -> []
      | FStar_Parser_AST.LetOpen uu____752 -> []
      | FStar_Parser_AST.If uu____757 -> []
      | FStar_Parser_AST.QForall uu____764 -> []
      | FStar_Parser_AST.QExists uu____777 -> []
      | FStar_Parser_AST.Record uu____790 -> []
      | FStar_Parser_AST.Match uu____803 -> []
      | FStar_Parser_AST.TryWith uu____818 -> []
      | FStar_Parser_AST.Bind uu____833 -> []
      | FStar_Parser_AST.Quote uu____840 -> []
      | FStar_Parser_AST.VQuote uu____845 -> []
      | FStar_Parser_AST.Seq uu____846 -> []
let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term,
      (FStar_Parser_AST.term, FStar_Parser_AST.imp)
        FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun t ->
    let rec aux args t1 =
      let uu____893 =
        let uu____894 = unparen t1 in uu____894.FStar_Parser_AST.tm in
      match uu____893 with
      | FStar_Parser_AST.App (t2, arg, imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l, args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____936 -> (t1, args) in
    aux [] t
let (close :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env ->
    fun t ->
      let ftv =
        let uu____956 = free_type_vars env t in
        FStar_All.pipe_left sort_ftv uu____956 in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x ->
                   let uu____974 =
                     let uu____975 =
                       let uu____980 = tm_type x.FStar_Ident.idRange in
                       (x, uu____980) in
                     FStar_Parser_AST.TAnnotated uu____975 in
                   FStar_Parser_AST.mk_binder uu____974 x.FStar_Ident.idRange
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
        let uu____993 = free_type_vars env t in
        FStar_All.pipe_left sort_ftv uu____993 in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x ->
                   let uu____1011 =
                     let uu____1012 =
                       let uu____1017 = tm_type x.FStar_Ident.idRange in
                       (x, uu____1017) in
                     FStar_Parser_AST.TAnnotated uu____1012 in
                   FStar_Parser_AST.mk_binder uu____1011
                     x.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit))) in
         let t1 =
           let uu____1019 =
             let uu____1020 = unparen t in uu____1020.FStar_Parser_AST.tm in
           match uu____1019 with
           | FStar_Parser_AST.Product uu____1021 -> t
           | uu____1028 ->
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
      (FStar_Parser_AST.binder Prims.list, FStar_Parser_AST.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun bs ->
    fun t ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (binders, t1) ->
          uncurry (FStar_List.append bs binders) t1
      | uu____1060 -> (bs, t)
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild -> true
    | FStar_Parser_AST.PatTvar (uu____1066, uu____1067) -> true
    | FStar_Parser_AST.PatVar (uu____1072, uu____1073) -> true
    | FStar_Parser_AST.PatAscribed (p1, uu____1079) -> is_var_pattern p1
    | uu____1092 -> false
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1, uu____1097) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____1110;
           FStar_Parser_AST.prange = uu____1111;_},
         uu____1112)
        -> true
    | uu____1123 -> false
let (replace_unit_pattern :
  FStar_Parser_AST.pattern -> FStar_Parser_AST.pattern) =
  fun p ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatConst (FStar_Const.Const_unit) ->
        FStar_Parser_AST.mk_pattern
          (FStar_Parser_AST.PatAscribed
             ((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild
                 p.FStar_Parser_AST.prange),
               (unit_ty, FStar_Pervasives_Native.None)))
          p.FStar_Parser_AST.prange
    | uu____1135 -> p
let rec (destruct_app_pattern :
  FStar_Syntax_DsEnv.env ->
    Prims.bool ->
      FStar_Parser_AST.pattern ->
        ((FStar_Ident.ident, FStar_Ident.lident) FStar_Util.either,
          FStar_Parser_AST.pattern Prims.list,
          (FStar_Parser_AST.term,
            FStar_Parser_AST.term FStar_Pervasives_Native.option)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple3)
  =
  fun env ->
    fun is_top_level1 ->
      fun p ->
        match p.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatAscribed (p1, t) ->
            let uu____1199 = destruct_app_pattern env is_top_level1 p1 in
            (match uu____1199 with
             | (name, args, uu____1242) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1, uu____1292);
               FStar_Parser_AST.prange = uu____1293;_},
             args)
            when is_top_level1 ->
            let uu____1303 =
              let uu____1308 = FStar_Syntax_DsEnv.qualify env id1 in
              FStar_Util.Inr uu____1308 in
            (uu____1303, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1, uu____1330);
               FStar_Parser_AST.prange = uu____1331;_},
             args)
            -> ((FStar_Util.Inl id1), args, FStar_Pervasives_Native.None)
        | uu____1361 -> failwith "Not an app pattern"
let rec (gather_pattern_bound_vars_maybe_top :
  FStar_Ident.ident FStar_Util.set ->
    FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set)
  =
  fun acc ->
    fun p ->
      let gather_pattern_bound_vars_from_list =
        FStar_List.fold_left gather_pattern_bound_vars_maybe_top acc in
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatWild -> acc
      | FStar_Parser_AST.PatConst uu____1405 -> acc
      | FStar_Parser_AST.PatVar
          (uu____1406, FStar_Pervasives_Native.Some
           (FStar_Parser_AST.Implicit))
          -> acc
      | FStar_Parser_AST.PatName uu____1409 -> acc
      | FStar_Parser_AST.PatTvar uu____1410 -> acc
      | FStar_Parser_AST.PatOp uu____1417 -> acc
      | FStar_Parser_AST.PatApp (phead, pats) ->
          gather_pattern_bound_vars_from_list (phead :: pats)
      | FStar_Parser_AST.PatVar (x, uu____1425) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatTuple (pats, uu____1434) ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu____1449 =
            FStar_List.map FStar_Pervasives_Native.snd guarded_pats in
          gather_pattern_bound_vars_from_list uu____1449
      | FStar_Parser_AST.PatAscribed (pat, uu____1457) ->
          gather_pattern_bound_vars_maybe_top acc pat
let (gather_pattern_bound_vars :
  FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set) =
  let acc =
    FStar_Util.new_set
      (fun id1 ->
         fun id2 ->
           if id1.FStar_Ident.idText = id2.FStar_Ident.idText
           then (Prims.parse_int "0")
           else (Prims.parse_int "1")) in
  fun p -> gather_pattern_bound_vars_maybe_top acc p
type bnd =
  | LocalBinder of (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.aqual)
  FStar_Pervasives_Native.tuple2 
  | LetBinder of (FStar_Ident.lident,
  (FStar_Syntax_Syntax.term,
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2)
  FStar_Pervasives_Native.tuple2 [@@deriving show]
let (uu___is_LocalBinder : bnd -> Prims.bool) =
  fun projectee ->
    match projectee with | LocalBinder _0 -> true | uu____1513 -> false
let (__proj__LocalBinder__item___0 :
  bnd ->
    (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2)
  = fun projectee -> match projectee with | LocalBinder _0 -> _0
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee ->
    match projectee with | LetBinder _0 -> true | uu____1547 -> false
let (__proj__LetBinder__item___0 :
  bnd ->
    (FStar_Ident.lident,
      (FStar_Syntax_Syntax.term,
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2)
      FStar_Pervasives_Native.tuple2)
  = fun projectee -> match projectee with | LetBinder _0 -> _0
let (binder_of_bnd :
  bnd ->
    (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___86_1591 ->
    match uu___86_1591 with
    | LocalBinder (a, aq) -> (a, aq)
    | uu____1598 -> failwith "Impossible"
let (as_binder :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      (FStar_Ident.ident FStar_Pervasives_Native.option,
        FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.binder, FStar_Syntax_DsEnv.env)
          FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun imp ->
      fun uu___87_1623 ->
        match uu___87_1623 with
        | (FStar_Pervasives_Native.None, k) ->
            let uu____1639 = FStar_Syntax_Syntax.null_binder k in
            (uu____1639, env)
        | (FStar_Pervasives_Native.Some a, k) ->
            let uu____1644 = FStar_Syntax_DsEnv.push_bv env a in
            (match uu____1644 with
             | (env1, a1) ->
                 (((let uu___110_1664 = a1 in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___110_1664.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___110_1664.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = k
                    }), (trans_aqual imp)), env1))
type env_t = FStar_Syntax_DsEnv.env[@@deriving show]
type lenv_t = FStar_Syntax_Syntax.bv Prims.list[@@deriving show]
let (mk_lb :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list,
    (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either,
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax, FStar_Range.range)
    FStar_Pervasives_Native.tuple5 -> FStar_Syntax_Syntax.letbinding)
  =
  fun uu____1691 ->
    match uu____1691 with
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
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun bs -> fun t -> FStar_Syntax_Util.abs bs t FStar_Pervasives_Native.None
let (mk_ref_read :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm ->
    let tm' =
      let uu____1759 =
        let uu____1774 =
          let uu____1775 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
          FStar_Syntax_Syntax.fv_to_tm uu____1775 in
        let uu____1776 =
          let uu____1785 =
            let uu____1792 = FStar_Syntax_Syntax.as_implicit false in
            (tm, uu____1792) in
          [uu____1785] in
        (uu____1774, uu____1776) in
      FStar_Syntax_Syntax.Tm_app uu____1759 in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm ->
    let tm' =
      let uu____1825 =
        let uu____1840 =
          let uu____1841 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
          FStar_Syntax_Syntax.fv_to_tm uu____1841 in
        let uu____1842 =
          let uu____1851 =
            let uu____1858 = FStar_Syntax_Syntax.as_implicit false in
            (tm, uu____1858) in
          [uu____1851] in
        (uu____1840, uu____1842) in
      FStar_Syntax_Syntax.Tm_app uu____1825 in
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
          let uu____1901 =
            let uu____1916 =
              let uu____1917 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Syntax_Syntax.fv_to_tm uu____1917 in
            let uu____1918 =
              let uu____1927 =
                let uu____1934 = FStar_Syntax_Syntax.as_implicit false in
                (t1, uu____1934) in
              let uu____1937 =
                let uu____1946 =
                  let uu____1953 = FStar_Syntax_Syntax.as_implicit false in
                  (t2, uu____1953) in
                [uu____1946] in
              uu____1927 :: uu____1937 in
            (uu____1916, uu____1918) in
          FStar_Syntax_Syntax.Tm_app uu____1901 in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___88_1984 ->
    match uu___88_1984 with
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
    | uu____1985 -> false
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u ->
    fun n1 ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____1993 = sum_to_universe u (n1 - (Prims.parse_int "1")) in
         FStar_Syntax_Syntax.U_succ uu____1993)
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1 -> sum_to_universe FStar_Syntax_Syntax.U_zero n1
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int, FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t ->
    let uu____2008 =
      let uu____2009 = unparen t in uu____2009.FStar_Parser_AST.tm in
    match uu____2008 with
    | FStar_Parser_AST.Wild ->
        let uu____2014 =
          let uu____2015 = FStar_Syntax_Unionfind.univ_fresh () in
          FStar_Syntax_Syntax.U_unif uu____2015 in
        FStar_Util.Inr uu____2014
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr, uu____2026)) ->
        let n1 = FStar_Util.int_of_string repr in
        (if n1 < (Prims.parse_int "0")
         then
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_NegativeUniverseConstFatal_NotSupported,
               (Prims.strcat
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
             let uu____2098 = sum_to_universe u n1 in
             FStar_Util.Inr uu____2098
         | (FStar_Util.Inr u, FStar_Util.Inl n1) ->
             let uu____2109 = sum_to_universe u n1 in
             FStar_Util.Inr uu____2109
         | (FStar_Util.Inr u11, FStar_Util.Inr u21) ->
             let uu____2120 =
               let uu____2125 =
                 let uu____2126 = FStar_Parser_AST.term_to_string t in
                 Prims.strcat
                   "This universe might contain a sum of two universe variables "
                   uu____2126 in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____2125) in
             FStar_Errors.raise_error uu____2120 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____2131 ->
        let rec aux t1 univargs =
          let uu____2161 =
            let uu____2162 = unparen t1 in uu____2162.FStar_Parser_AST.tm in
          match uu____2161 with
          | FStar_Parser_AST.App (t2, targ, uu____2169) ->
              let uarg = desugar_maybe_non_constant_universe targ in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___89_2199 ->
                     match uu___89_2199 with
                     | FStar_Util.Inr uu____2204 -> true
                     | uu____2205 -> false) univargs
              then
                let uu____2210 =
                  let uu____2211 =
                    FStar_List.map
                      (fun uu___90_2220 ->
                         match uu___90_2220 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs in
                  FStar_Syntax_Syntax.U_max uu____2211 in
                FStar_Util.Inr uu____2210
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___91_2237 ->
                        match uu___91_2237 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____2243 -> failwith "impossible")
                     univargs in
                 let uu____2244 =
                   FStar_List.fold_left
                     (fun m -> fun n1 -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs in
                 FStar_Util.Inl uu____2244)
          | uu____2250 ->
              let uu____2251 =
                let uu____2256 =
                  let uu____2257 =
                    let uu____2258 = FStar_Parser_AST.term_to_string t1 in
                    Prims.strcat uu____2258 " in universe context" in
                  Prims.strcat "Unexpected term " uu____2257 in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____2256) in
              FStar_Errors.raise_error uu____2251 t1.FStar_Parser_AST.range in
        aux t []
    | uu____2267 ->
        let uu____2268 =
          let uu____2273 =
            let uu____2274 =
              let uu____2275 = FStar_Parser_AST.term_to_string t in
              Prims.strcat uu____2275 " in universe context" in
            Prims.strcat "Unexpected term " uu____2274 in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____2273) in
        FStar_Errors.raise_error uu____2268 t.FStar_Parser_AST.range
let rec (desugar_universe :
  FStar_Parser_AST.term -> FStar_Syntax_Syntax.universe) =
  fun t ->
    let u = desugar_maybe_non_constant_universe t in
    match u with
    | FStar_Util.Inl n1 -> int_to_universe n1
    | FStar_Util.Inr u1 -> u1
let (check_no_aq : FStar_Syntax_Syntax.antiquotations -> Prims.unit) =
  fun aq ->
    match aq with
    | [] -> ()
    | (bv, b, e)::uu____2304 ->
        let uu____2327 =
          let uu____2332 =
            let uu____2333 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format2 "Unexpected antiquotation: %s(%s)"
              (if b then "`@" else "`#") uu____2333 in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____2332) in
        FStar_Errors.raise_error uu____2327 e.FStar_Syntax_Syntax.pos
let check_fields :
  'Auu____2339 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident, 'Auu____2339) FStar_Pervasives_Native.tuple2
        Prims.list -> FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env ->
    fun fields ->
      fun rg ->
        let uu____2364 = FStar_List.hd fields in
        match uu____2364 with
        | (f, uu____2374) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f in
              let check_field uu____2384 =
                match uu____2384 with
                | (f', uu____2390) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____2392 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record in
                      if uu____2392
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
              (let uu____2396 = FStar_List.tl fields in
               FStar_List.iter check_field uu____2396);
              (match () with | () -> record)))
let rec (desugar_data_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern ->
      Prims.bool ->
        (env_t, bnd, FStar_Syntax_Syntax.pat Prims.list)
          FStar_Pervasives_Native.tuple3)
  =
  fun env ->
    fun p ->
      fun is_mut ->
        let check_linear_pattern_variables pats r =
          let rec pat_vars p1 =
            match p1.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_dot_term uu____2645 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_wild uu____2652 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_constant uu____2653 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_var x ->
                FStar_Util.set_add x FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_cons (uu____2655, pats1) ->
                let aux out uu____2689 =
                  match uu____2689 with
                  | (p2, uu____2701) ->
                      let intersection =
                        let uu____2709 = pat_vars p2 in
                        FStar_Util.set_intersect uu____2709 out in
                      let uu____2712 = FStar_Util.set_is_empty intersection in
                      if uu____2712
                      then
                        let uu____2715 = pat_vars p2 in
                        FStar_Util.set_union out uu____2715
                      else
                        (let duplicate_bv =
                           let uu____2720 =
                             FStar_Util.set_elements intersection in
                           FStar_List.hd uu____2720 in
                         let uu____2723 =
                           let uu____2728 =
                             FStar_Util.format1
                               "Non-linear patterns are not permitted. %s appears more than once in this pattern."
                               (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
                           (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                             uu____2728) in
                         FStar_Errors.raise_error uu____2723 r) in
                FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1 in
          match pats with
          | [] -> ()
          | p1::[] ->
              let uu____2748 = pat_vars p1 in
              FStar_All.pipe_right uu____2748 FStar_Pervasives.ignore
          | p1::ps ->
              let pvars = pat_vars p1 in
              let aux p2 =
                let uu____2768 =
                  let uu____2769 = pat_vars p2 in
                  FStar_Util.set_eq pvars uu____2769 in
                if uu____2768
                then ()
                else
                  (let nonlinear_vars =
                     let uu____2776 = pat_vars p2 in
                     FStar_Util.set_symmetric_difference pvars uu____2776 in
                   let first_nonlinear_var =
                     let uu____2780 = FStar_Util.set_elements nonlinear_vars in
                     FStar_List.hd uu____2780 in
                   let uu____2783 =
                     let uu____2788 =
                       FStar_Util.format1
                         "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                         (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
                     (FStar_Errors.Fatal_IncoherentPatterns, uu____2788) in
                   FStar_Errors.raise_error uu____2783 r) in
              FStar_List.iter aux ps in
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false, uu____2792) -> ()
         | (true, FStar_Parser_AST.PatVar uu____2793) -> ()
         | (true, uu____2800) ->
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_LetMutableForVariablesOnly,
                 "let-mutable is for variables only")
               p.FStar_Parser_AST.prange);
        (let push_bv_maybe_mut =
           if is_mut
           then FStar_Syntax_DsEnv.push_bv_mutable
           else FStar_Syntax_DsEnv.push_bv in
         let resolvex l e x =
           let uu____2835 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText)) in
           match uu____2835 with
           | FStar_Pervasives_Native.Some y -> (l, e, y)
           | uu____2849 ->
               let uu____2852 = push_bv_maybe_mut e x in
               (match uu____2852 with | (e1, x1) -> ((x1 :: l), e1, x1)) in
         let rec aux' top loc env1 p1 =
           let pos q =
             FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange in
           let pos_r r q = FStar_Syntax_Syntax.withinfo q r in
           let orig = p1 in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr uu____2939 -> failwith "impossible"
           | FStar_Parser_AST.PatOp op ->
               let uu____2955 =
                 let uu____2956 =
                   let uu____2957 =
                     let uu____2964 =
                       let uu____2965 =
                         let uu____2970 =
                           FStar_Parser_AST.compile_op (Prims.parse_int "0")
                             op.FStar_Ident.idText op.FStar_Ident.idRange in
                         (uu____2970, (op.FStar_Ident.idRange)) in
                       FStar_Ident.mk_ident uu____2965 in
                     (uu____2964, FStar_Pervasives_Native.None) in
                   FStar_Parser_AST.PatVar uu____2957 in
                 {
                   FStar_Parser_AST.pat = uu____2956;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 } in
               aux loc env1 uu____2955
           | FStar_Parser_AST.PatAscribed (p2, (t, tacopt)) ->
               ((match tacopt with
                 | FStar_Pervasives_Native.None -> ()
                 | FStar_Pervasives_Native.Some uu____2987 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                         "Type ascriptions within patterns are cannot be associated with a tactic")
                       orig.FStar_Parser_AST.prange);
                (let uu____2988 = aux loc env1 p2 in
                 match uu____2988 with
                 | (loc1, env', binder, p3, imp) ->
                     let annot_pat_var p4 t1 =
                       match p4.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let uu___111_3042 = p4 in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var
                                  (let uu___112_3047 = x in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___112_3047.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___112_3047.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }));
                             FStar_Syntax_Syntax.p =
                               (uu___111_3042.FStar_Syntax_Syntax.p)
                           }
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let uu___113_3049 = p4 in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild
                                  (let uu___114_3054 = x in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___114_3054.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___114_3054.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }));
                             FStar_Syntax_Syntax.p =
                               (uu___113_3049.FStar_Syntax_Syntax.p)
                           }
                       | uu____3055 when top -> p4
                       | uu____3056 ->
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                               "Type ascriptions within patterns are only allowed on variables")
                             orig.FStar_Parser_AST.prange in
                     let uu____3059 =
                       match binder with
                       | LetBinder uu____3072 -> failwith "impossible"
                       | LocalBinder (x, aq) ->
                           let t1 =
                             let uu____3092 = close_fun env1 t in
                             desugar_term env1 uu____3092 in
                           (if
                              (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                               with
                               | FStar_Syntax_Syntax.Tm_unknown -> false
                               | uu____3094 -> true)
                            then
                              (let uu____3095 =
                                 let uu____3100 =
                                   let uu____3101 =
                                     FStar_Syntax_Print.bv_to_string x in
                                   let uu____3102 =
                                     FStar_Syntax_Print.term_to_string
                                       x.FStar_Syntax_Syntax.sort in
                                   let uu____3103 =
                                     FStar_Syntax_Print.term_to_string t1 in
                                   FStar_Util.format3
                                     "Multiple ascriptions for %s in pattern, type %s was shadowed by %s\n"
                                     uu____3101 uu____3102 uu____3103 in
                                 (FStar_Errors.Warning_MultipleAscriptions,
                                   uu____3100) in
                               FStar_Errors.log_issue
                                 orig.FStar_Parser_AST.prange uu____3095)
                            else ();
                            (let uu____3105 = annot_pat_var p3 t1 in
                             (uu____3105,
                               (LocalBinder
                                  ((let uu___115_3111 = x in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___115_3111.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___115_3111.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    }), aq))))) in
                     (match uu____3059 with
                      | (p4, binder1) -> (loc1, env', binder1, p4, imp))))
           | FStar_Parser_AST.PatWild ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____3133 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x) in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____3133, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____3144 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c) in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____3144, false)
           | FStar_Parser_AST.PatTvar (x, aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit) in
               let aq1 = trans_aqual aq in
               let uu____3165 = resolvex loc env1 x in
               (match uu____3165 with
                | (loc1, env2, xbv) ->
                    let uu____3187 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv) in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____3187, imp))
           | FStar_Parser_AST.PatVar (x, aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit) in
               let aq1 = trans_aqual aq in
               let uu____3208 = resolvex loc env1 x in
               (match uu____3208 with
                | (loc1, env2, xbv) ->
                    let uu____3230 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv) in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____3230, imp))
           | FStar_Parser_AST.PatName l ->
               let l1 =
                 FStar_Syntax_DsEnv.fail_or env1
                   (FStar_Syntax_DsEnv.try_lookup_datacon env1) l in
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____3242 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, [])) in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____3242, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____3266;_},
                args)
               ->
               let uu____3272 =
                 FStar_List.fold_right
                   (fun arg ->
                      fun uu____3313 ->
                        match uu____3313 with
                        | (loc1, env2, args1) ->
                            let uu____3361 = aux loc1 env2 arg in
                            (match uu____3361 with
                             | (loc2, env3, uu____3390, arg1, imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, []) in
               (match uu____3272 with
                | (loc1, env2, args1) ->
                    let l1 =
                      FStar_Syntax_DsEnv.fail_or env2
                        (FStar_Syntax_DsEnv.try_lookup_datacon env2) l in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun in
                    let uu____3460 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1)) in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)),
                      uu____3460, false))
           | FStar_Parser_AST.PatApp uu____3477 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                 p1.FStar_Parser_AST.prange
           | FStar_Parser_AST.PatList pats ->
               let uu____3499 =
                 FStar_List.fold_right
                   (fun pat ->
                      fun uu____3532 ->
                        match uu____3532 with
                        | (loc1, env2, pats1) ->
                            let uu____3564 = aux loc1 env2 pat in
                            (match uu____3564 with
                             | (loc2, env3, uu____3589, pat1, uu____3591) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, []) in
               (match uu____3499 with
                | (loc1, env2, pats1) ->
                    let pat =
                      let uu____3634 =
                        let uu____3637 =
                          let uu____3642 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange in
                          pos_r uu____3642 in
                        let uu____3643 =
                          let uu____3644 =
                            let uu____3657 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Parser_Const.nil_lid
                                FStar_Syntax_Syntax.Delta_constant
                                (FStar_Pervasives_Native.Some
                                   FStar_Syntax_Syntax.Data_ctor) in
                            (uu____3657, []) in
                          FStar_Syntax_Syntax.Pat_cons uu____3644 in
                        FStar_All.pipe_left uu____3637 uu____3643 in
                      FStar_List.fold_right
                        (fun hd1 ->
                           fun tl1 ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p in
                             let uu____3689 =
                               let uu____3690 =
                                 let uu____3703 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.cons_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Data_ctor) in
                                 (uu____3703, [(hd1, false); (tl1, false)]) in
                               FStar_Syntax_Syntax.Pat_cons uu____3690 in
                             FStar_All.pipe_left (pos_r r) uu____3689) pats1
                        uu____3634 in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)), pat,
                      false))
           | FStar_Parser_AST.PatTuple (args, dep1) ->
               let uu____3747 =
                 FStar_List.fold_left
                   (fun uu____3787 ->
                      fun p2 ->
                        match uu____3787 with
                        | (loc1, env2, pats) ->
                            let uu____3836 = aux loc1 env2 p2 in
                            (match uu____3836 with
                             | (loc2, env3, uu____3865, pat, uu____3867) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args in
               (match uu____3747 with
                | (loc1, env2, args1) ->
                    let args2 = FStar_List.rev args1 in
                    let l =
                      if dep1
                      then
                        FStar_Parser_Const.mk_dtuple_data_lid
                          (FStar_List.length args2)
                          p1.FStar_Parser_AST.prange
                      else
                        FStar_Parser_Const.mk_tuple_data_lid
                          (FStar_List.length args2)
                          p1.FStar_Parser_AST.prange in
                    let uu____3962 =
                      FStar_Syntax_DsEnv.fail_or env2
                        (FStar_Syntax_DsEnv.try_lookup_lid env2) l in
                    (match uu____3962 with
                     | (constr, uu____3984) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____3987 -> failwith "impossible" in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (FStar_Pervasives_Native.Some
                                (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun in
                         let uu____3989 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2)) in
                         (loc1, env2,
                           (LocalBinder (x, FStar_Pervasives_Native.None)),
                           uu____3989, false)))
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
                      (fun uu____4060 ->
                         match uu____4060 with
                         | (f, p2) -> ((f.FStar_Ident.ident), p2))) in
               let args =
                 FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                   (FStar_List.map
                      (fun uu____4090 ->
                         match uu____4090 with
                         | (f, uu____4096) ->
                             let uu____4097 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____4123 ->
                                       match uu____4123 with
                                       | (g, uu____4129) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText)) in
                             (match uu____4097 with
                              | FStar_Pervasives_Native.None ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
                              | FStar_Pervasives_Native.Some (uu____4134, p2)
                                  -> p2))) in
               let app =
                 let uu____4141 =
                   let uu____4142 =
                     let uu____4149 =
                       let uu____4150 =
                         let uu____4151 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                                [record.FStar_Syntax_DsEnv.constrname]) in
                         FStar_Parser_AST.PatName uu____4151 in
                       FStar_Parser_AST.mk_pattern uu____4150
                         p1.FStar_Parser_AST.prange in
                     (uu____4149, args) in
                   FStar_Parser_AST.PatApp uu____4142 in
                 FStar_Parser_AST.mk_pattern uu____4141
                   p1.FStar_Parser_AST.prange in
               let uu____4154 = aux loc env1 app in
               (match uu____4154 with
                | (env2, e, b, p2, uu____4183) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv, args1) ->
                          let uu____4211 =
                            let uu____4212 =
                              let uu____4225 =
                                let uu___116_4226 = fv in
                                let uu____4227 =
                                  let uu____4230 =
                                    let uu____4231 =
                                      let uu____4238 =
                                        FStar_All.pipe_right
                                          record.FStar_Syntax_DsEnv.fields
                                          (FStar_List.map
                                             FStar_Pervasives_Native.fst) in
                                      ((record.FStar_Syntax_DsEnv.typename),
                                        uu____4238) in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____4231 in
                                  FStar_Pervasives_Native.Some uu____4230 in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___116_4226.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___116_4226.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____4227
                                } in
                              (uu____4225, args1) in
                            FStar_Syntax_Syntax.Pat_cons uu____4212 in
                          FStar_All.pipe_left pos uu____4211
                      | uu____4265 -> p2 in
                    (env2, e, b, p3, false))
         and aux loc env1 p1 = aux' false loc env1 p1 in
         let aux_maybe_or env1 p1 =
           let loc = [] in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____4315 = aux' true loc env1 p2 in
               (match uu____4315 with
                | (loc1, env2, var, p3, uu____4342) ->
                    let uu____4347 =
                      FStar_List.fold_left
                        (fun uu____4379 ->
                           fun p4 ->
                             match uu____4379 with
                             | (loc2, env3, ps1) ->
                                 let uu____4412 = aux' true loc2 env3 p4 in
                                 (match uu____4412 with
                                  | (loc3, env4, uu____4437, p5, uu____4439)
                                      -> (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps in
                    (match uu____4347 with
                     | (loc2, env3, ps1) ->
                         let pats = p3 :: (FStar_List.rev ps1) in
                         (env3, var, pats)))
           | uu____4490 ->
               let uu____4491 = aux' true loc env1 p1 in
               (match uu____4491 with
                | (loc1, env2, vars, pat, b) -> (env2, vars, [pat])) in
         let uu____4531 = aux_maybe_or env p in
         match uu____4531 with
         | (env1, b, pats) ->
             (check_linear_pattern_variables pats p.FStar_Parser_AST.prange;
              (env1, b, pats)))
and (desugar_binding_pat_maybe_top :
  Prims.bool ->
    FStar_Syntax_DsEnv.env ->
      FStar_Parser_AST.pattern ->
        Prims.bool ->
          (env_t, bnd, FStar_Syntax_Syntax.pat Prims.list)
            FStar_Pervasives_Native.tuple3)
  =
  fun top ->
    fun env ->
      fun p ->
        fun is_mut ->
          let mklet x =
            let uu____4590 =
              let uu____4591 =
                let uu____4602 = FStar_Syntax_DsEnv.qualify env x in
                (uu____4602,
                  (FStar_Syntax_Syntax.tun, FStar_Pervasives_Native.None)) in
              LetBinder uu____4591 in
            (env, uu____4590, []) in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____4630 =
                  let uu____4631 =
                    let uu____4636 =
                      FStar_Parser_AST.compile_op (Prims.parse_int "0")
                        x.FStar_Ident.idText x.FStar_Ident.idRange in
                    (uu____4636, (x.FStar_Ident.idRange)) in
                  FStar_Ident.mk_ident uu____4631 in
                mklet uu____4630
            | FStar_Parser_AST.PatVar (x, uu____4638) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x, uu____4644);
                   FStar_Parser_AST.prange = uu____4645;_},
                 (t, tacopt))
                ->
                let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env) in
                let uu____4665 =
                  let uu____4666 =
                    let uu____4677 = FStar_Syntax_DsEnv.qualify env x in
                    let uu____4678 =
                      let uu____4685 = desugar_term env t in
                      (uu____4685, tacopt1) in
                    (uu____4677, uu____4678) in
                  LetBinder uu____4666 in
                (env, uu____4665, [])
            | uu____4696 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_UnexpectedPattern,
                    "Unexpected pattern at the top-level")
                  p.FStar_Parser_AST.prange
          else
            (let uu____4706 = desugar_data_pat env p is_mut in
             match uu____4706 with
             | (env1, binder, p1) ->
                 let p2 =
                   match p1 with
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                         uu____4735;
                       FStar_Syntax_Syntax.p = uu____4736;_}::[] -> []
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                         uu____4741;
                       FStar_Syntax_Syntax.p = uu____4742;_}::[] -> []
                   | uu____4747 -> p1 in
                 (env1, binder, p2))
and (desugar_binding_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern ->
      (env_t, bnd, FStar_Syntax_Syntax.pat Prims.list)
        FStar_Pervasives_Native.tuple3)
  = fun env -> fun p -> desugar_binding_pat_maybe_top false env p false
and (desugar_match_pat_maybe_top :
  Prims.bool ->
    FStar_Syntax_DsEnv.env ->
      FStar_Parser_AST.pattern ->
        (env_t, FStar_Syntax_Syntax.pat Prims.list)
          FStar_Pervasives_Native.tuple2)
  =
  fun uu____4754 ->
    fun env ->
      fun pat ->
        let uu____4757 = desugar_data_pat env pat false in
        match uu____4757 with | (env1, uu____4773, pat1) -> (env1, pat1)
and (desugar_match_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern ->
      (env_t, FStar_Syntax_Syntax.pat Prims.list)
        FStar_Pervasives_Native.tuple2)
  = fun env -> fun p -> desugar_match_pat_maybe_top false env p
and (desugar_term_aq :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term ->
      (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.antiquotations)
        FStar_Pervasives_Native.tuple2)
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
      let uu____4792 = desugar_term_aq env e in
      match uu____4792 with | (t, aq) -> (check_no_aq aq; t)
and (desugar_typ_aq :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term ->
      (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.antiquotations)
        FStar_Pervasives_Native.tuple2)
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
      let uu____4809 = desugar_typ_aq env e in
      match uu____4809 with | (t, aq) -> (check_no_aq aq; t)
and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness, FStar_Const.width)
        FStar_Pervasives_Native.tuple2 ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun repr ->
      fun uu____4819 ->
        fun range ->
          match uu____4819 with
          | (signedness, width) ->
              let tnm =
                Prims.strcat "FStar."
                  (Prims.strcat
                     (match signedness with
                      | FStar_Const.Unsigned -> "U"
                      | FStar_Const.Signed -> "")
                     (Prims.strcat "Int"
                        (match width with
                         | FStar_Const.Int8 -> "8"
                         | FStar_Const.Int16 -> "16"
                         | FStar_Const.Int32 -> "32"
                         | FStar_Const.Int64 -> "64"))) in
              ((let uu____4829 =
                  let uu____4830 =
                    FStar_Const.within_bounds repr signedness width in
                  Prims.op_Negation uu____4830 in
                if uu____4829
                then
                  let uu____4831 =
                    let uu____4836 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm in
                    (FStar_Errors.Error_OutOfRange, uu____4836) in
                  FStar_Errors.log_issue range uu____4831
                else ());
               (let private_intro_nm =
                  Prims.strcat tnm
                    (Prims.strcat ".__"
                       (Prims.strcat
                          (match signedness with
                           | FStar_Const.Unsigned -> "u"
                           | FStar_Const.Signed -> "") "int_to_t")) in
                let intro_nm =
                  Prims.strcat tnm
                    (Prims.strcat "."
                       (Prims.strcat
                          (match signedness with
                           | FStar_Const.Unsigned -> "u"
                           | FStar_Const.Signed -> "") "int_to_t")) in
                let lid =
                  FStar_Ident.lid_of_path (FStar_Ident.path_of_text intro_nm)
                    range in
                let lid1 =
                  let uu____4844 = FStar_Syntax_DsEnv.try_lookup_lid env lid in
                  match uu____4844 with
                  | FStar_Pervasives_Native.Some (intro_term, uu____4854) ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             FStar_Ident.lid_of_path
                               (FStar_Ident.path_of_text private_intro_nm)
                               range in
                           let private_fv =
                             let uu____4864 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____4864 fv.FStar_Syntax_Syntax.fv_qual in
                           let uu___117_4865 = intro_term in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___117_4865.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___117_4865.FStar_Syntax_Syntax.vars)
                           }
                       | uu____4866 ->
                           failwith
                             (Prims.strcat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None ->
                      let uu____4873 =
                        let uu____4878 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____4878) in
                      FStar_Errors.raise_error uu____4873 range in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range in
                let uu____4894 =
                  let uu____4897 =
                    let uu____4898 =
                      let uu____4913 =
                        let uu____4922 =
                          let uu____4929 =
                            FStar_Syntax_Syntax.as_implicit false in
                          (repr1, uu____4929) in
                        [uu____4922] in
                      (lid1, uu____4913) in
                    FStar_Syntax_Syntax.Tm_app uu____4898 in
                  FStar_Syntax_Syntax.mk uu____4897 in
                uu____4894 FStar_Pervasives_Native.None range))
and (desugar_name :
  (FStar_Syntax_Syntax.term' -> FStar_Syntax_Syntax.term) ->
    (FStar_Syntax_Syntax.term ->
       FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
      -> env_t -> Prims.bool -> FStar_Ident.lid -> FStar_Syntax_Syntax.term)
  =
  fun mk1 ->
    fun setpos ->
      fun env ->
        fun resolve ->
          fun l ->
            let uu____4968 =
              FStar_Syntax_DsEnv.fail_or env
                ((if resolve
                  then FStar_Syntax_DsEnv.try_lookup_lid_with_attributes
                  else
                    FStar_Syntax_DsEnv.try_lookup_lid_with_attributes_no_resolve)
                   env) l in
            match uu____4968 with
            | (tm, mut, attrs) ->
                let warn_if_deprecated attrs1 =
                  FStar_List.iter
                    (fun a ->
                       match a.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_app
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____5014;
                              FStar_Syntax_Syntax.vars = uu____5015;_},
                            args)
                           when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____5038 =
                               FStar_Syntax_Print.term_to_string tm in
                             Prims.strcat uu____5038 " is deprecated" in
                           let msg1 =
                             if
                               (FStar_List.length args) >
                                 (Prims.parse_int "0")
                             then
                               let uu____5046 =
                                 let uu____5047 =
                                   let uu____5050 = FStar_List.hd args in
                                   FStar_Pervasives_Native.fst uu____5050 in
                                 uu____5047.FStar_Syntax_Syntax.n in
                               match uu____5046 with
                               | FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_string (s, uu____5066))
                                   when
                                   Prims.op_Negation
                                     ((FStar_Util.trim_string s) = "")
                                   ->
                                   Prims.strcat msg
                                     (Prims.strcat ", use "
                                        (Prims.strcat s " instead"))
                               | uu____5067 -> msg
                             else msg in
                           FStar_Errors.log_issue
                             (FStar_Ident.range_of_lid l)
                             (FStar_Errors.Warning_DeprecatedDefinition,
                               msg1)
                       | FStar_Syntax_Syntax.Tm_fvar fv when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____5071 =
                               FStar_Syntax_Print.term_to_string tm in
                             Prims.strcat uu____5071 " is deprecated" in
                           FStar_Errors.log_issue
                             (FStar_Ident.range_of_lid l)
                             (FStar_Errors.Warning_DeprecatedDefinition, msg)
                       | uu____5072 -> ()) attrs1 in
                (warn_if_deprecated attrs;
                 (let tm1 = setpos tm in
                  if mut
                  then
                    let uu____5077 =
                      let uu____5078 =
                        let uu____5085 = mk_ref_read tm1 in
                        (uu____5085,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Mutable_rval)) in
                      FStar_Syntax_Syntax.Tm_meta uu____5078 in
                    FStar_All.pipe_left mk1 uu____5077
                  else tm1))
and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun env ->
    fun cattributes ->
      let desugar_attribute t =
        let uu____5101 =
          let uu____5102 = unparen t in uu____5102.FStar_Parser_AST.tm in
        match uu____5101 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____5103; FStar_Ident.ident = uu____5104;
              FStar_Ident.nsstr = uu____5105; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____5108 ->
            let uu____5109 =
              let uu____5114 =
                let uu____5115 = FStar_Parser_AST.term_to_string t in
                Prims.strcat "Unknown attribute " uu____5115 in
              (FStar_Errors.Fatal_UnknownAttribute, uu____5114) in
            FStar_Errors.raise_error uu____5109 t.FStar_Parser_AST.range in
      FStar_List.map desugar_attribute cattributes
and (desugar_term_maybe_top :
  Prims.bool ->
    env_t ->
      FStar_Parser_AST.term ->
        (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.antiquotations)
          FStar_Pervasives_Native.tuple2)
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
          let uu___118_5204 = e in
          {
            FStar_Syntax_Syntax.n = (uu___118_5204.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___118_5204.FStar_Syntax_Syntax.vars)
          } in
        let uu____5207 =
          let uu____5208 = unparen top in uu____5208.FStar_Parser_AST.tm in
        match uu____5207 with
        | FStar_Parser_AST.Wild -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____5225 ->
            let uu____5232 = desugar_formula env top in (uu____5232, noaqs)
        | FStar_Parser_AST.Requires (t, lopt) ->
            let uu____5249 = desugar_formula env t in (uu____5249, noaqs)
        | FStar_Parser_AST.Ensures (t, lopt) ->
            let uu____5266 = desugar_formula env t in (uu____5266, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i, FStar_Pervasives_Native.Some size)) ->
            let uu____5300 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range in
            (uu____5300, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____5312 = mk1 (FStar_Syntax_Syntax.Tm_constant c) in
            (uu____5312, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_}, args)
            ->
            let e =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Op ((FStar_Ident.mk_ident ("==", r)), args))
                top.FStar_Parser_AST.range top.FStar_Parser_AST.level in
            desugar_term_aq env
              (FStar_Parser_AST.mk_term
                 (FStar_Parser_AST.Op ((FStar_Ident.mk_ident ("~", r)), [e]))
                 top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
        | FStar_Parser_AST.Op (op_star, uu____5339::uu____5340::[]) when
            ((FStar_Ident.text_of_id op_star) = "*") &&
              (let uu____5344 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star in
               FStar_All.pipe_right uu____5344 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____5357;_},
                   t1::t2::[])
                  ->
                  let uu____5362 = flatten1 t1 in
                  FStar_List.append uu____5362 [t2]
              | uu____5365 -> [t] in
            let uu____5366 =
              let uu____5375 =
                let uu____5382 =
                  let uu____5385 = unparen top in flatten1 uu____5385 in
                FStar_All.pipe_right uu____5382
                  (FStar_List.map
                     (fun t ->
                        let uu____5404 = desugar_typ_aq env t in
                        match uu____5404 with
                        | (t', aq) ->
                            let uu____5415 = FStar_Syntax_Syntax.as_arg t' in
                            (uu____5415, aq))) in
              FStar_All.pipe_right uu____5375 FStar_List.unzip in
            (match uu____5366 with
             | (targs, aqs) ->
                 let uu____5444 =
                   let uu____5449 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____5449 in
                 (match uu____5444 with
                  | (tup, uu____5459) ->
                      let uu____5460 =
                        mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs)) in
                      (uu____5460, (join_aqs aqs))))
        | FStar_Parser_AST.Tvar a ->
            let uu____5478 =
              let uu____5481 =
                let uu____5484 =
                  FStar_Syntax_DsEnv.fail_or2
                    (FStar_Syntax_DsEnv.try_lookup_id env) a in
                FStar_Pervasives_Native.fst uu____5484 in
              FStar_All.pipe_left setpos uu____5481 in
            (uu____5478, noaqs)
        | FStar_Parser_AST.Uvar u ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedUniverseVariable,
                (Prims.strcat "Unexpected universe variable "
                   (Prims.strcat (FStar_Ident.text_of_id u)
                      " in non-universe context")))
              top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s, args) ->
            let uu____5520 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s in
            (match uu____5520 with
             | FStar_Pervasives_Native.None ->
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     (Prims.strcat "Unexpected or unbound operator: "
                        (FStar_Ident.text_of_id s)))
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let uu____5536 =
                     let uu____5551 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t ->
                               let uu____5593 = desugar_term_aq env t in
                               match uu____5593 with
                               | (t', s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1))) in
                     FStar_All.pipe_right uu____5551 FStar_List.unzip in
                   (match uu____5536 with
                    | (args1, aqs) ->
                        let uu____5676 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1)) in
                        (uu____5676, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1, (a, uu____5712)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____5727 =
              let uu___119_5728 = top in
              let uu____5729 =
                let uu____5730 =
                  let uu____5737 =
                    let uu___120_5738 = top in
                    let uu____5739 =
                      let uu____5740 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____5740 in
                    {
                      FStar_Parser_AST.tm = uu____5739;
                      FStar_Parser_AST.range =
                        (uu___120_5738.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___120_5738.FStar_Parser_AST.level)
                    } in
                  (uu____5737, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____5730 in
              {
                FStar_Parser_AST.tm = uu____5729;
                FStar_Parser_AST.range =
                  (uu___119_5728.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___119_5728.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____5727
        | FStar_Parser_AST.Construct (n1, (a, uu____5743)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____5759 =
                let uu___121_5760 = top in
                let uu____5761 =
                  let uu____5762 =
                    let uu____5769 =
                      let uu___122_5770 = top in
                      let uu____5771 =
                        let uu____5772 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range in
                        FStar_Parser_AST.Var uu____5772 in
                      {
                        FStar_Parser_AST.tm = uu____5771;
                        FStar_Parser_AST.range =
                          (uu___122_5770.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___122_5770.FStar_Parser_AST.level)
                      } in
                    (uu____5769, a, FStar_Parser_AST.Nothing) in
                  FStar_Parser_AST.App uu____5762 in
                {
                  FStar_Parser_AST.tm = uu____5761;
                  FStar_Parser_AST.range =
                    (uu___121_5760.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___121_5760.FStar_Parser_AST.level)
                } in
              desugar_term_maybe_top top_level env uu____5759))
        | FStar_Parser_AST.Construct (n1, (a, uu____5775)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____5790 =
              let uu___123_5791 = top in
              let uu____5792 =
                let uu____5793 =
                  let uu____5800 =
                    let uu___124_5801 = top in
                    let uu____5802 =
                      let uu____5803 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____5803 in
                    {
                      FStar_Parser_AST.tm = uu____5802;
                      FStar_Parser_AST.range =
                        (uu___124_5801.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___124_5801.FStar_Parser_AST.level)
                    } in
                  (uu____5800, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____5793 in
              {
                FStar_Parser_AST.tm = uu____5792;
                FStar_Parser_AST.range =
                  (uu___123_5791.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___123_5791.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____5790
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5804; FStar_Ident.ident = uu____5805;
              FStar_Ident.nsstr = uu____5806; FStar_Ident.str = "Type0";_}
            ->
            let uu____5809 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero) in
            (uu____5809, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5824; FStar_Ident.ident = uu____5825;
              FStar_Ident.nsstr = uu____5826; FStar_Ident.str = "Type";_}
            ->
            let uu____5829 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown) in
            (uu____5829, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____5844; FStar_Ident.ident = uu____5845;
               FStar_Ident.nsstr = uu____5846; FStar_Ident.str = "Type";_},
             (t, FStar_Parser_AST.UnivApp)::[])
            ->
            let uu____5864 =
              let uu____5867 =
                let uu____5868 = desugar_universe t in
                FStar_Syntax_Syntax.Tm_type uu____5868 in
              mk1 uu____5867 in
            (uu____5864, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5881; FStar_Ident.ident = uu____5882;
              FStar_Ident.nsstr = uu____5883; FStar_Ident.str = "Effect";_}
            ->
            let uu____5886 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect) in
            (uu____5886, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5901; FStar_Ident.ident = uu____5902;
              FStar_Ident.nsstr = uu____5903; FStar_Ident.str = "True";_}
            ->
            let uu____5906 =
              FStar_Syntax_Syntax.fvar
                (FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                   top.FStar_Parser_AST.range)
                FStar_Syntax_Syntax.Delta_constant
                FStar_Pervasives_Native.None in
            (uu____5906, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5917; FStar_Ident.ident = uu____5918;
              FStar_Ident.nsstr = uu____5919; FStar_Ident.str = "False";_}
            ->
            let uu____5922 =
              FStar_Syntax_Syntax.fvar
                (FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                   top.FStar_Parser_AST.range)
                FStar_Syntax_Syntax.Delta_constant
                FStar_Pervasives_Native.None in
            (uu____5922, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,
             { FStar_Ident.idText = txt; FStar_Ident.idRange = uu____5935;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____5937 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name in
              match uu____5937 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt in
                  let uu____5946 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_defined_at_level
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None in
                  (uu____5946, noaqs)
              | FStar_Pervasives_Native.None ->
                  let uu____5957 =
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      (FStar_Ident.text_of_lid eff_name) txt in
                  failwith uu____5957))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____5964 = desugar_name mk1 setpos env true l in
              (uu____5964, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____5977 = desugar_name mk1 setpos env true l in
              (uu____5977, noaqs)))
        | FStar_Parser_AST.Projector (l, i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____5998 = FStar_Syntax_DsEnv.try_lookup_datacon env l in
                match uu____5998 with
                | FStar_Pervasives_Native.Some uu____6007 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None ->
                    let uu____6012 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l in
                    (match uu____6012 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____6026 -> FStar_Pervasives_Native.None) in
              match name with
              | FStar_Pervasives_Native.Some (resolve, new_name) ->
                  let uu____6043 =
                    let uu____6044 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i in
                    desugar_name mk1 setpos env resolve uu____6044 in
                  (uu____6043, noaqs)
              | uu____6055 ->
                  let uu____6062 =
                    let uu____6067 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str in
                    (FStar_Errors.Fatal_EffectNotFound, uu____6067) in
                  FStar_Errors.raise_error uu____6062
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____6074 = FStar_Syntax_DsEnv.try_lookup_datacon env lid in
              match uu____6074 with
              | FStar_Pervasives_Native.None ->
                  let uu____6081 =
                    let uu____6086 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____6086) in
                  FStar_Errors.raise_error uu____6081
                    top.FStar_Parser_AST.range
              | uu____6091 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid in
                  let uu____6095 = desugar_name mk1 setpos env true lid' in
                  (uu____6095, noaqs)))
        | FStar_Parser_AST.Construct (l, args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____6121 = FStar_Syntax_DsEnv.try_lookup_datacon env l in
              match uu____6121 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1) in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____6152 ->
                       let uu____6159 =
                         FStar_Util.take
                           (fun uu____6183 ->
                              match uu____6183 with
                              | (uu____6188, imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args in
                       (match uu____6159 with
                        | (universes, args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes in
                            let uu____6233 =
                              let uu____6248 =
                                FStar_List.map
                                  (fun uu____6281 ->
                                     match uu____6281 with
                                     | (t, imp) ->
                                         let uu____6298 =
                                           desugar_term_aq env t in
                                         (match uu____6298 with
                                          | (te, aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1 in
                              FStar_All.pipe_right uu____6248
                                FStar_List.unzip in
                            (match uu____6233 with
                             | (args2, aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1)) in
                                 let uu____6391 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2)) in
                                 (uu____6391, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None ->
                  let err =
                    let uu____6421 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l in
                    match uu____6421 with
                    | FStar_Pervasives_Native.None ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.strcat "Constructor "
                             (Prims.strcat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____6428 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.strcat "Effect "
                             (Prims.strcat l.FStar_Ident.str
                                " used at an unexpected position"))) in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders, t) ->
            let uu____6439 =
              FStar_List.fold_left
                (fun uu____6484 ->
                   fun b ->
                     match uu____6484 with
                     | (env1, tparams, typs) ->
                         let uu____6541 = desugar_binder env1 b in
                         (match uu____6541 with
                          | (xopt, t1) ->
                              let uu____6570 =
                                match xopt with
                                | FStar_Pervasives_Native.None ->
                                    let uu____6579 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun in
                                    (env1, uu____6579)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x in
                              (match uu____6570 with
                               | (env2, x) ->
                                   let uu____6599 =
                                     let uu____6602 =
                                       let uu____6605 =
                                         let uu____6606 =
                                           no_annot_abs tparams t1 in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____6606 in
                                       [uu____6605] in
                                     FStar_List.append typs uu____6602 in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___125_6632 = x in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___125_6632.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___125_6632.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____6599)))) (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      FStar_Pervasives_Native.None]) in
            (match uu____6439 with
             | (env1, uu____6660, targs) ->
                 let uu____6682 =
                   let uu____6687 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____6687 in
                 (match uu____6682 with
                  | (tup, uu____6697) ->
                      let uu____6698 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_app (tup, targs)) in
                      (uu____6698, noaqs)))
        | FStar_Parser_AST.Product (binders, t) ->
            let uu____6723 = uncurry binders t in
            (match uu____6723 with
             | (bs, t1) ->
                 let rec aux env1 bs1 uu___92_6759 =
                   match uu___92_6759 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1 in
                       let uu____6773 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod in
                       FStar_All.pipe_left setpos uu____6773
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1 in
                       let uu____6795 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb in
                       (match uu____6795 with
                        | (b, env2) -> aux env2 (b :: bs1) tl1) in
                 let uu____6804 = aux env [] bs in (uu____6804, noaqs))
        | FStar_Parser_AST.Refine (b, f) ->
            let uu____6825 = desugar_binder env b in
            (match uu____6825 with
             | (FStar_Pervasives_Native.None, uu____6836) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____6850 =
                   as_binder env FStar_Pervasives_Native.None b1 in
                 (match uu____6850 with
                  | (x, env1) ->
                      let f1 = desugar_formula env1 f in
                      let t =
                        let uu____6865 =
                          FStar_Syntax_Util.refine
                            (FStar_Pervasives_Native.fst x) f1 in
                        FStar_All.pipe_left setpos uu____6865 in
                      (t, noaqs)))
        | FStar_Parser_AST.Abs (binders, body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern) in
            let uu____6897 =
              FStar_List.fold_left
                (fun uu____6917 ->
                   fun pat ->
                     match uu____6917 with
                     | (env1, ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed
                              (uu____6943, (t, FStar_Pervasives_Native.None))
                              ->
                              let uu____6953 =
                                let uu____6956 = free_type_vars env1 t in
                                FStar_List.append uu____6956 ftvs in
                              (env1, uu____6953)
                          | FStar_Parser_AST.PatAscribed
                              (uu____6961,
                               (t, FStar_Pervasives_Native.Some tac))
                              ->
                              let uu____6972 =
                                let uu____6975 = free_type_vars env1 t in
                                let uu____6978 =
                                  let uu____6981 = free_type_vars env1 tac in
                                  FStar_List.append uu____6981 ftvs in
                                FStar_List.append uu____6975 uu____6978 in
                              (env1, uu____6972)
                          | uu____6986 -> (env1, ftvs))) (env, []) binders1 in
            (match uu____6897 with
             | (uu____6995, ftv) ->
                 let ftv1 = sort_ftv ftv in
                 let binders2 =
                   let uu____7007 =
                     FStar_All.pipe_right ftv1
                       (FStar_List.map
                          (fun a ->
                             FStar_Parser_AST.mk_pattern
                               (FStar_Parser_AST.PatTvar
                                  (a,
                                    (FStar_Pervasives_Native.Some
                                       FStar_Parser_AST.Implicit)))
                               top.FStar_Parser_AST.range)) in
                   FStar_List.append uu____7007 binders1 in
                 let rec aux env1 bs sc_pat_opt uu___93_7052 =
                   match uu___93_7052 with
                   | [] ->
                       let uu____7075 = desugar_term_aq env1 body in
                       (match uu____7075 with
                        | (body1, aq) ->
                            let body2 =
                              match sc_pat_opt with
                              | FStar_Pervasives_Native.Some (sc, pat) ->
                                  let body2 =
                                    let uu____7106 =
                                      let uu____7107 =
                                        FStar_Syntax_Syntax.pat_bvs pat in
                                      FStar_All.pipe_right uu____7107
                                        (FStar_List.map
                                           FStar_Syntax_Syntax.mk_binder) in
                                    FStar_Syntax_Subst.close uu____7106 body1 in
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_match
                                       (sc,
                                         [(pat, FStar_Pervasives_Native.None,
                                            body2)]))
                                    FStar_Pervasives_Native.None
                                    body2.FStar_Syntax_Syntax.pos
                              | FStar_Pervasives_Native.None -> body1 in
                            let uu____7160 =
                              let uu____7163 =
                                no_annot_abs (FStar_List.rev bs) body2 in
                              setpos uu____7163 in
                            (uu____7160, aq))
                   | p::rest ->
                       let uu____7176 = desugar_binding_pat env1 p in
                       (match uu____7176 with
                        | (env2, b, pat) ->
                            let pat1 =
                              match pat with
                              | [] -> FStar_Pervasives_Native.None
                              | p1::[] -> FStar_Pervasives_Native.Some p1
                              | uu____7204 ->
                                  FStar_Errors.raise_error
                                    (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                      "Disjunctive patterns are not supported in abstractions")
                                    p.FStar_Parser_AST.prange in
                            let uu____7209 =
                              match b with
                              | LetBinder uu____7242 -> failwith "Impossible"
                              | LocalBinder (x, aq) ->
                                  let sc_pat_opt1 =
                                    match (pat1, sc_pat_opt) with
                                    | (FStar_Pervasives_Native.None,
                                       uu____7298) -> sc_pat_opt
                                    | (FStar_Pervasives_Native.Some p1,
                                       FStar_Pervasives_Native.None) ->
                                        let uu____7334 =
                                          let uu____7339 =
                                            FStar_Syntax_Syntax.bv_to_name x in
                                          (uu____7339, p1) in
                                        FStar_Pervasives_Native.Some
                                          uu____7334
                                    | (FStar_Pervasives_Native.Some p1,
                                       FStar_Pervasives_Native.Some (sc, p'))
                                        ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____7375, uu____7376) ->
                                             let tup2 =
                                               let uu____7378 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____7378
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor) in
                                             let sc1 =
                                               let uu____7382 =
                                                 let uu____7385 =
                                                   let uu____7386 =
                                                     let uu____7401 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2) in
                                                     let uu____7404 =
                                                       let uu____7407 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc in
                                                       let uu____7408 =
                                                         let uu____7411 =
                                                           let uu____7412 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____7412 in
                                                         [uu____7411] in
                                                       uu____7407 ::
                                                         uu____7408 in
                                                     (uu____7401, uu____7404) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____7386 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____7385 in
                                               uu____7382
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Parser_AST.range in
                                             let p2 =
                                               let uu____7423 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p1, false)]))
                                                 uu____7423 in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____7454, args),
                                            FStar_Syntax_Syntax.Pat_cons
                                            (uu____7456, pats)) ->
                                             let tupn =
                                               let uu____7495 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____7495
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor) in
                                             let sc1 =
                                               let uu____7505 =
                                                 let uu____7506 =
                                                   let uu____7521 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn) in
                                                   let uu____7524 =
                                                     let uu____7533 =
                                                       let uu____7542 =
                                                         let uu____7543 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____7543 in
                                                       [uu____7542] in
                                                     FStar_List.append args
                                                       uu____7533 in
                                                   (uu____7521, uu____7524) in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____7506 in
                                               mk1 uu____7505 in
                                             let p2 =
                                               let uu____7563 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p1, false)])))
                                                 uu____7563 in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | uu____7598 ->
                                             failwith "Impossible") in
                                  ((x, aq), sc_pat_opt1) in
                            (match uu____7209 with
                             | (b1, sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest)) in
                 aux env [] FStar_Pervasives_Native.None binders2)
        | FStar_Parser_AST.App
            (uu____7669, uu____7670, FStar_Parser_AST.UnivApp) ->
            let rec aux universes e =
              let uu____7688 =
                let uu____7689 = unparen e in uu____7689.FStar_Parser_AST.tm in
              match uu____7688 with
              | FStar_Parser_AST.App (e1, t, FStar_Parser_AST.UnivApp) ->
                  let univ_arg = desugar_universe t in
                  aux (univ_arg :: universes) e1
              | uu____7699 ->
                  let uu____7700 = desugar_term_aq env e in
                  (match uu____7700 with
                   | (head1, aq) ->
                       let uu____7713 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes)) in
                       (uu____7713, aq)) in
            aux [] top
        | FStar_Parser_AST.App uu____7720 ->
            let rec aux args aqs e =
              let uu____7773 =
                let uu____7774 = unparen e in uu____7774.FStar_Parser_AST.tm in
              match uu____7773 with
              | FStar_Parser_AST.App (e1, t, imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____7794 = desugar_term_aq env t in
                  (match uu____7794 with
                   | (t1, aq) ->
                       let arg = arg_withimp_e imp t1 in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____7830 ->
                  let uu____7831 = desugar_term_aq env e in
                  (match uu____7831 with
                   | (head1, aq) ->
                       let uu____7854 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args)) in
                       (uu____7854, (join_aqs (aq :: aqs)))) in
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
            let uu____7894 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range in
            desugar_term_aq env uu____7894
        | FStar_Parser_AST.Seq (t1, t2) ->
            let t =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Let
                   (FStar_Parser_AST.NoLetQualifier,
                     [(FStar_Pervasives_Native.None,
                        ((FStar_Parser_AST.mk_pattern
                            FStar_Parser_AST.PatWild
                            t1.FStar_Parser_AST.range), t1))], t2))
                top.FStar_Parser_AST.range FStar_Parser_AST.Expr in
            let uu____7946 = desugar_term_aq env t in
            (match uu____7946 with
             | (tm, s) ->
                 let uu____7957 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence))) in
                 (uu____7957, s))
        | FStar_Parser_AST.LetOpen (lid, e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid in
            let uu____7965 =
              let uu____7974 = FStar_Syntax_DsEnv.expect_typ env1 in
              if uu____7974 then desugar_typ_aq else desugar_term_aq in
            uu____7965 env1 e
        | FStar_Parser_AST.Let (qual, lbs, body) ->
            let is_rec = qual = FStar_Parser_AST.Rec in
            let ds_let_rec_or_app uu____8025 =
              let bindings = lbs in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____8168 ->
                        match uu____8168 with
                        | (attr_opt, (p, def)) ->
                            let uu____8226 = is_app_pattern p in
                            if uu____8226
                            then
                              let uu____8257 =
                                destruct_app_pattern env top_level p in
                              (attr_opt, uu____8257, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1, def1) ->
                                   let uu____8339 =
                                     destruct_app_pattern env top_level p1 in
                                   (attr_opt, uu____8339, def1)
                               | uu____8384 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1, uu____8422);
                                           FStar_Parser_AST.prange =
                                             uu____8423;_},
                                         t)
                                        ->
                                        if top_level
                                        then
                                          let uu____8471 =
                                            let uu____8492 =
                                              let uu____8497 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1 in
                                              FStar_Util.Inr uu____8497 in
                                            (uu____8492, [],
                                              (FStar_Pervasives_Native.Some t)) in
                                          (attr_opt, uu____8471, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1, uu____8588) ->
                                        if top_level
                                        then
                                          let uu____8623 =
                                            let uu____8644 =
                                              let uu____8649 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1 in
                                              FStar_Util.Inr uu____8649 in
                                            (uu____8644, [],
                                              FStar_Pervasives_Native.None) in
                                          (attr_opt, uu____8623, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____8739 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange)))) in
              let uu____8770 =
                FStar_List.fold_left
                  (fun uu____8843 ->
                     fun uu____8844 ->
                       match (uu____8843, uu____8844) with
                       | ((env1, fnames, rec_bindings),
                          (_attr_opt, (f, uu____8952, uu____8953),
                           uu____8954)) ->
                           let uu____9071 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____9097 =
                                   FStar_Syntax_DsEnv.push_bv env1 x in
                                 (match uu____9097 with
                                  | (env2, xx) ->
                                      let uu____9116 =
                                        let uu____9119 =
                                          FStar_Syntax_Syntax.mk_binder xx in
                                        uu____9119 :: rec_bindings in
                                      (env2, (FStar_Util.Inl xx), uu____9116))
                             | FStar_Util.Inr l ->
                                 let uu____9127 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.Delta_equational in
                                 (uu____9127, (FStar_Util.Inr l),
                                   rec_bindings) in
                           (match uu____9071 with
                            | (env2, lbname, rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs in
              match uu____8770 with
              | (env', fnames, rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames in
                  let rec_bindings1 = FStar_List.rev rec_bindings in
                  let desugar_one_def env1 lbname uu____9269 =
                    match uu____9269 with
                    | (attrs_opt, (uu____9305, args, result_t), def) ->
                        let args1 =
                          FStar_All.pipe_right args
                            (FStar_List.map replace_unit_pattern) in
                        let pos = def.FStar_Parser_AST.range in
                        let def1 =
                          match result_t with
                          | FStar_Pervasives_Native.None -> def
                          | FStar_Pervasives_Native.Some (t, tacopt) ->
                              let t1 =
                                let uu____9393 = is_comp_type env1 t in
                                if uu____9393
                                then
                                  ((let uu____9395 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x ->
                                              let uu____9405 =
                                                is_var_pattern x in
                                              Prims.op_Negation uu____9405)) in
                                    match uu____9395 with
                                    | FStar_Pervasives_Native.None -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____9408 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____9410 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid in
                                         FStar_Option.isSome uu____9410))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0"))) in
                                   if uu____9408
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t) in
                              let uu____9414 =
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed (def, t1, tacopt))
                                uu____9414 FStar_Parser_AST.Expr in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____9418 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level in
                        let body1 = desugar_term env1 def2 in
                        let lbname1 =
                          match lbname with
                          | FStar_Util.Inl x -> FStar_Util.Inl x
                          | FStar_Util.Inr l ->
                              let uu____9433 =
                                let uu____9434 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1 in
                                FStar_Syntax_Syntax.lid_as_fv l uu____9434
                                  FStar_Pervasives_Native.None in
                              FStar_Util.Inr uu____9433 in
                        let body2 =
                          if is_rec
                          then FStar_Syntax_Subst.close rec_bindings1 body1
                          else body1 in
                        let attrs =
                          match attrs_opt with
                          | FStar_Pervasives_Native.None -> []
                          | FStar_Pervasives_Native.Some l ->
                              FStar_List.map (desugar_term env1) l in
                        mk_lb
                          (attrs, lbname1, FStar_Syntax_Syntax.tun, body2,
                            pos) in
                  let lbs1 =
                    FStar_List.map2
                      (desugar_one_def (if is_rec then env' else env))
                      fnames1 funs in
                  let uu____9493 = desugar_term_aq env' body in
                  (match uu____9493 with
                   | (body1, aq) ->
                       let uu____9506 =
                         let uu____9509 =
                           let uu____9510 =
                             let uu____9523 =
                               FStar_Syntax_Subst.close rec_bindings1 body1 in
                             ((is_rec, lbs1), uu____9523) in
                           FStar_Syntax_Syntax.Tm_let uu____9510 in
                         FStar_All.pipe_left mk1 uu____9509 in
                       (uu____9506, aq)) in
            let ds_non_rec attrs_opt pat t1 t2 =
              let attrs =
                match attrs_opt with
                | FStar_Pervasives_Native.None -> []
                | FStar_Pervasives_Native.Some l ->
                    FStar_List.map (desugar_term env) l in
              let t11 = desugar_term env t1 in
              let is_mutable = qual = FStar_Parser_AST.Mutable in
              let t12 = if is_mutable then mk_ref_alloc t11 else t11 in
              let uu____9583 =
                desugar_binding_pat_maybe_top top_level env pat is_mutable in
              match uu____9583 with
              | (env1, binder, pat1) ->
                  let uu____9605 =
                    match binder with
                    | LetBinder (l, (t, _tacopt)) ->
                        let uu____9631 = desugar_term_aq env1 t2 in
                        (match uu____9631 with
                         | (body1, aq) ->
                             let fv =
                               let uu____9645 =
                                 FStar_Syntax_Util.incr_delta_qualifier t12 in
                               FStar_Syntax_Syntax.lid_as_fv l uu____9645
                                 FStar_Pervasives_Native.None in
                             let uu____9646 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t12,
                                            (t12.FStar_Syntax_Syntax.pos))]),
                                      body1)) in
                             (uu____9646, aq))
                    | LocalBinder (x, uu____9670) ->
                        let uu____9671 = desugar_term_aq env1 t2 in
                        (match uu____9671 with
                         | (body1, aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | {
                                   FStar_Syntax_Syntax.v =
                                     FStar_Syntax_Syntax.Pat_wild uu____9685;
                                   FStar_Syntax_Syntax.p = uu____9686;_}::[]
                                   -> body1
                               | uu____9691 ->
                                   let uu____9694 =
                                     let uu____9697 =
                                       let uu____9698 =
                                         let uu____9721 =
                                           FStar_Syntax_Syntax.bv_to_name x in
                                         let uu____9722 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1 in
                                         (uu____9721, uu____9722) in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____9698 in
                                     FStar_Syntax_Syntax.mk uu____9697 in
                                   uu____9694 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range in
                             let uu____9732 =
                               let uu____9735 =
                                 let uu____9736 =
                                   let uu____9749 =
                                     let uu____9750 =
                                       let uu____9751 =
                                         FStar_Syntax_Syntax.mk_binder x in
                                       [uu____9751] in
                                     FStar_Syntax_Subst.close uu____9750
                                       body2 in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t12,
                                           (t12.FStar_Syntax_Syntax.pos))]),
                                     uu____9749) in
                                 FStar_Syntax_Syntax.Tm_let uu____9736 in
                               FStar_All.pipe_left mk1 uu____9735 in
                             (uu____9732, aq)) in
                  (match uu____9605 with
                   | (tm, aq) ->
                       if is_mutable
                       then
                         let uu____9792 =
                           FStar_All.pipe_left mk1
                             (FStar_Syntax_Syntax.Tm_meta
                                (tm,
                                  (FStar_Syntax_Syntax.Meta_desugared
                                     FStar_Syntax_Syntax.Mutable_alloc))) in
                         (uu____9792, aq)
                       else (tm, aq)) in
            let uu____9804 = FStar_List.hd lbs in
            (match uu____9804 with
             | (attrs, (head_pat, defn)) ->
                 let uu____9848 = is_rec || (is_app_pattern head_pat) in
                 if uu____9848
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1, t2, t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun in
            let t_bool1 =
              let uu____9861 =
                let uu____9862 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.Delta_constant
                    FStar_Pervasives_Native.None in
                FStar_Syntax_Syntax.Tm_fvar uu____9862 in
              mk1 uu____9861 in
            let uu____9863 = desugar_term_aq env t1 in
            (match uu____9863 with
             | (t1', aq1) ->
                 let uu____9874 = desugar_term_aq env t2 in
                 (match uu____9874 with
                  | (t2', aq2) ->
                      let uu____9885 = desugar_term_aq env t3 in
                      (match uu____9885 with
                       | (t3', aq3) ->
                           let uu____9896 =
                             let uu____9899 =
                               let uu____9900 =
                                 let uu____9923 =
                                   FStar_Syntax_Util.ascribe t1'
                                     ((FStar_Util.Inl t_bool1),
                                       FStar_Pervasives_Native.None) in
                                 let uu____9944 =
                                   let uu____9959 =
                                     let uu____9972 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t2.FStar_Parser_AST.range in
                                     (uu____9972,
                                       FStar_Pervasives_Native.None, t2') in
                                   let uu____9983 =
                                     let uu____9998 =
                                       let uu____10011 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t3.FStar_Parser_AST.range in
                                       (uu____10011,
                                         FStar_Pervasives_Native.None, t3') in
                                     [uu____9998] in
                                   uu____9959 :: uu____9983 in
                                 (uu____9923, uu____9944) in
                               FStar_Syntax_Syntax.Tm_match uu____9900 in
                             mk1 uu____9899 in
                           (uu____9896, (join_aqs [aq1; aq2; aq3])))))
        | FStar_Parser_AST.TryWith (e, branches) ->
            let r = top.FStar_Parser_AST.range in
            let handler = FStar_Parser_AST.mk_function branches r r in
            let body =
              FStar_Parser_AST.mk_function
                [((FStar_Parser_AST.mk_pattern
                     (FStar_Parser_AST.PatConst FStar_Const.Const_unit) r),
                   FStar_Pervasives_Native.None, e)] r r in
            let a1 =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   ((FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Var FStar_Parser_Const.try_with_lid)
                       r top.FStar_Parser_AST.level), body,
                     FStar_Parser_AST.Nothing)) r top.FStar_Parser_AST.level in
            let a2 =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App (a1, handler, FStar_Parser_AST.Nothing))
                r top.FStar_Parser_AST.level in
            desugar_term_aq env a2
        | FStar_Parser_AST.Match (e, branches) ->
            let desugar_branch uu____10170 =
              match uu____10170 with
              | (pat, wopt, b) ->
                  let uu____10192 = desugar_match_pat env pat in
                  (match uu____10192 with
                   | (env1, pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____10217 = desugar_term env1 e1 in
                             FStar_Pervasives_Native.Some uu____10217 in
                       let uu____10218 = desugar_term_aq env1 b in
                       (match uu____10218 with
                        | (b1, aq) ->
                            let uu____10231 =
                              desugar_disjunctive_pattern pat1 wopt1 b1 in
                            (uu____10231, aq))) in
            let uu____10236 = desugar_term_aq env e in
            (match uu____10236 with
             | (e1, aq) ->
                 let uu____10247 =
                   let uu____10256 =
                     let uu____10267 = FStar_List.map desugar_branch branches in
                     FStar_All.pipe_right uu____10267 FStar_List.unzip in
                   FStar_All.pipe_right uu____10256
                     (fun uu____10331 ->
                        match uu____10331 with
                        | (x, y) -> ((FStar_List.flatten x), y)) in
                 (match uu____10247 with
                  | (brs, aqs) ->
                      let uu____10382 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs)) in
                      (uu____10382, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e, t, tac_opt) ->
            let annot =
              let uu____10415 = is_comp_type env t in
              if uu____10415
              then
                let uu____10422 = desugar_comp t.FStar_Parser_AST.range env t in
                FStar_Util.Inr uu____10422
              else
                (let uu____10428 = desugar_term env t in
                 FStar_Util.Inl uu____10428) in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env) in
            let uu____10434 = desugar_term_aq env e in
            (match uu____10434 with
             | (e1, aq) ->
                 let uu____10445 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_ascribed
                        (e1, (annot, tac_opt1), FStar_Pervasives_Native.None)) in
                 (uu____10445, aq))
        | FStar_Parser_AST.Record (uu____10474, []) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt, fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range in
            let user_ns =
              let uu____10515 = FStar_List.hd fields in
              match uu____10515 with | (f, uu____10527) -> f.FStar_Ident.ns in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____10569 ->
                        match uu____10569 with
                        | (g, uu____10575) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText)) in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f]) in
              match found with
              | FStar_Pervasives_Native.Some (uu____10581, e) -> (fn, e)
              | FStar_Pervasives_Native.None ->
                  (match xopt with
                   | FStar_Pervasives_Native.None ->
                       let uu____10595 =
                         let uu____10600 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____10600) in
                       FStar_Errors.raise_error uu____10595
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
                  let uu____10608 =
                    let uu____10619 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____10650 ->
                              match uu____10650 with
                              | (f, uu____10660) ->
                                  let uu____10661 =
                                    let uu____10662 =
                                      get_field FStar_Pervasives_Native.None
                                        f in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____10662 in
                                  (uu____10661, FStar_Parser_AST.Nothing))) in
                    (user_constrname, uu____10619) in
                  FStar_Parser_AST.Construct uu____10608
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range in
                  let xterm =
                    let uu____10680 =
                      let uu____10681 = FStar_Ident.lid_of_ids [x] in
                      FStar_Parser_AST.Var uu____10681 in
                    FStar_Parser_AST.mk_term uu____10680
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr in
                  let record1 =
                    let uu____10683 =
                      let uu____10696 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____10726 ->
                                match uu____10726 with
                                | (f, uu____10736) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f)) in
                      (FStar_Pervasives_Native.None, uu____10696) in
                    FStar_Parser_AST.Record uu____10683 in
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
            let uu____10796 = desugar_term_aq env recterm1 in
            (match uu____10796 with
             | (e, s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____10812;
                         FStar_Syntax_Syntax.vars = uu____10813;_},
                       args)
                      ->
                      let uu____10835 =
                        let uu____10838 =
                          let uu____10839 =
                            let uu____10854 =
                              let uu____10855 =
                                let uu____10858 =
                                  let uu____10859 =
                                    let uu____10866 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst) in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____10866) in
                                  FStar_Syntax_Syntax.Record_ctor uu____10859 in
                                FStar_Pervasives_Native.Some uu____10858 in
                              FStar_Syntax_Syntax.fvar
                                (FStar_Ident.set_lid_range
                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                   e.FStar_Syntax_Syntax.pos)
                                FStar_Syntax_Syntax.Delta_constant
                                uu____10855 in
                            (uu____10854, args) in
                          FStar_Syntax_Syntax.Tm_app uu____10839 in
                        FStar_All.pipe_left mk1 uu____10838 in
                      (uu____10835, s)
                  | uu____10895 -> (e, s)))
        | FStar_Parser_AST.Project (e, f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____10899 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f in
              match uu____10899 with
              | (constrname, is_rec) ->
                  let uu____10914 = desugar_term_aq env e in
                  (match uu____10914 with
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
                       let uu____10932 =
                         let uu____10935 =
                           let uu____10936 =
                             let uu____10951 =
                               FStar_Syntax_Syntax.fvar
                                 (FStar_Ident.set_lid_range projname
                                    (FStar_Ident.range_of_lid f))
                                 FStar_Syntax_Syntax.Delta_equational qual in
                             let uu____10952 =
                               let uu____10955 =
                                 FStar_Syntax_Syntax.as_arg e1 in
                               [uu____10955] in
                             (uu____10951, uu____10952) in
                           FStar_Syntax_Syntax.Tm_app uu____10936 in
                         FStar_All.pipe_left mk1 uu____10935 in
                       (uu____10932, s))))
        | FStar_Parser_AST.NamedTyp (uu____10962, e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e in
            let uu____10971 =
              let uu____10972 = FStar_Syntax_Subst.compress tm in
              uu____10972.FStar_Syntax_Syntax.n in
            (match uu____10971 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____10980 =
                   let uu___126_10983 =
                     let uu____10984 =
                       let uu____10985 = FStar_Syntax_Syntax.lid_of_fv fv in
                       FStar_Ident.string_of_lid uu____10985 in
                     FStar_Syntax_Util.exp_string uu____10984 in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___126_10983.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___126_10983.FStar_Syntax_Syntax.vars)
                   } in
                 (uu____10980, noaqs)
             | uu____10998 ->
                 let uu____10999 =
                   let uu____11004 =
                     let uu____11005 = FStar_Syntax_Print.term_to_string tm in
                     Prims.strcat "VQuote, expected an fvar, got: "
                       uu____11005 in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____11004) in
                 FStar_Errors.raise_error uu____10999
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e, FStar_Parser_AST.Static) ->
            let uu____11011 = desugar_term_aq env e in
            (match uu____11011 with
             | (tm, vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   } in
                 let uu____11023 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi)) in
                 (uu____11023, noaqs))
        | FStar_Parser_AST.Antiquote (b, e) ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun in
            let uu____11043 = FStar_Syntax_Syntax.bv_to_name bv in
            let uu____11044 =
              let uu____11053 =
                let uu____11060 = desugar_term env e in (bv, b, uu____11060) in
              [uu____11053] in
            (uu____11043, uu____11044)
        | FStar_Parser_AST.Quote (e, FStar_Parser_AST.Dynamic) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              } in
            let uu____11091 =
              let uu____11094 =
                let uu____11095 =
                  let uu____11102 = desugar_term env e in (uu____11102, qi) in
                FStar_Syntax_Syntax.Tm_quoted uu____11095 in
              FStar_All.pipe_left mk1 uu____11094 in
            (uu____11091, noaqs)
        | uu____11117 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____11118 = desugar_formula env top in (uu____11118, noaqs)
        | uu____11129 ->
            let uu____11130 =
              let uu____11135 =
                let uu____11136 = FStar_Parser_AST.term_to_string top in
                Prims.strcat "Unexpected term: " uu____11136 in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____11135) in
            FStar_Errors.raise_error uu____11130 top.FStar_Parser_AST.range
and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____11142 -> false
    | uu____11151 -> true
and (is_synth_by_tactic :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun e ->
    fun t ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (l, r, FStar_Parser_AST.Hash) ->
          is_synth_by_tactic e l
      | FStar_Parser_AST.Var lid ->
          let uu____11157 =
            FStar_Syntax_DsEnv.resolve_to_fully_qualified_name e lid in
          (match uu____11157 with
           | FStar_Pervasives_Native.Some lid1 ->
               FStar_Ident.lid_equals lid1 FStar_Parser_Const.synth_lid
           | FStar_Pervasives_Native.None -> false)
      | uu____11161 -> false
and (desugar_args :
  FStar_Syntax_DsEnv.env ->
    (FStar_Parser_AST.term, FStar_Parser_AST.imp)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      (FStar_Syntax_Syntax.term,
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun env ->
    fun args ->
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____11198 ->
              match uu____11198 with
              | (a, imp) ->
                  let uu____11211 = desugar_term env a in
                  arg_withimp_e imp uu____11211))
and (desugar_comp :
  FStar_Range.range ->
    FStar_Syntax_DsEnv.env ->
      FStar_Parser_AST.term ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun r ->
    fun env ->
      fun t ->
        let fail1 a err = FStar_Errors.raise_error err r in
        let is_requires uu____11237 =
          match uu____11237 with
          | (t1, uu____11243) ->
              let uu____11244 =
                let uu____11245 = unparen t1 in
                uu____11245.FStar_Parser_AST.tm in
              (match uu____11244 with
               | FStar_Parser_AST.Requires uu____11246 -> true
               | uu____11253 -> false) in
        let is_ensures uu____11261 =
          match uu____11261 with
          | (t1, uu____11267) ->
              let uu____11268 =
                let uu____11269 = unparen t1 in
                uu____11269.FStar_Parser_AST.tm in
              (match uu____11268 with
               | FStar_Parser_AST.Ensures uu____11270 -> true
               | uu____11277 -> false) in
        let is_app head1 uu____11288 =
          match uu____11288 with
          | (t1, uu____11294) ->
              let uu____11295 =
                let uu____11296 = unparen t1 in
                uu____11296.FStar_Parser_AST.tm in
              (match uu____11295 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____11298;
                      FStar_Parser_AST.level = uu____11299;_},
                    uu____11300, uu____11301)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____11302 -> false) in
        let is_smt_pat uu____11310 =
          match uu____11310 with
          | (t1, uu____11316) ->
              let uu____11317 =
                let uu____11318 = unparen t1 in
                uu____11318.FStar_Parser_AST.tm in
              (match uu____11317 with
               | FStar_Parser_AST.Construct
                   (cons1,
                    ({
                       FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                         (smtpat, uu____11321);
                       FStar_Parser_AST.range = uu____11322;
                       FStar_Parser_AST.level = uu____11323;_},
                     uu____11324)::uu____11325::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s -> smtpat.FStar_Ident.str = s)
                        ["SMTPat"; "SMTPatT"; "SMTPatOr"])
               | FStar_Parser_AST.Construct
                   (cons1,
                    ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var smtpat;
                       FStar_Parser_AST.range = uu____11364;
                       FStar_Parser_AST.level = uu____11365;_},
                     uu____11366)::uu____11367::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
               | uu____11392 -> false) in
        let is_decreases = is_app "decreases" in
        let pre_process_comp_typ t1 =
          let uu____11420 = head_and_args t1 in
          match uu____11420 with
          | (head1, args) ->
              (match head1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Name lemma when
                   (lemma.FStar_Ident.ident).FStar_Ident.idText = "Lemma" ->
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
                     ((FStar_Parser_AST.mk_term req t1.FStar_Parser_AST.range
                         FStar_Parser_AST.Type_level),
                       FStar_Parser_AST.Nothing) in
                   let thunk_ens_ ens =
                     let wildpat =
                       FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild
                         ens.FStar_Parser_AST.range in
                     FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Abs ([wildpat], ens))
                       ens.FStar_Parser_AST.range FStar_Parser_AST.Expr in
                   let thunk_ens uu____11514 =
                     match uu____11514 with
                     | (e, i) ->
                         let uu____11525 = thunk_ens_ e in (uu____11525, i) in
                   let fail_lemma uu____11535 =
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
                         (Prims.strcat
                            "Invalid arguments to 'Lemma'; expected one of the following:\n\t"
                            msg)) t1.FStar_Parser_AST.range in
                   let args1 =
                     match args with
                     | [] -> fail_lemma ()
                     | req::[] when is_requires req -> fail_lemma ()
                     | smtpat::[] when is_smt_pat smtpat -> fail_lemma ()
                     | dec::[] when is_decreases dec -> fail_lemma ()
                     | ens::[] ->
                         let uu____11615 =
                           let uu____11622 =
                             let uu____11629 = thunk_ens ens in
                             [uu____11629; nil_pat] in
                           req_true :: uu____11622 in
                         unit_tm :: uu____11615
                     | req::ens::[] when
                         (is_requires req) && (is_ensures ens) ->
                         let uu____11676 =
                           let uu____11683 =
                             let uu____11690 = thunk_ens ens in
                             [uu____11690; nil_pat] in
                           req :: uu____11683 in
                         unit_tm :: uu____11676
                     | ens::smtpat::[] when
                         (((let uu____11739 = is_requires ens in
                            Prims.op_Negation uu____11739) &&
                             (let uu____11741 = is_smt_pat ens in
                              Prims.op_Negation uu____11741))
                            &&
                            (let uu____11743 = is_decreases ens in
                             Prims.op_Negation uu____11743))
                           && (is_smt_pat smtpat)
                         ->
                         let uu____11744 =
                           let uu____11751 =
                             let uu____11758 = thunk_ens ens in
                             [uu____11758; smtpat] in
                           req_true :: uu____11751 in
                         unit_tm :: uu____11744
                     | ens::dec::[] when
                         (is_ensures ens) && (is_decreases dec) ->
                         let uu____11805 =
                           let uu____11812 =
                             let uu____11819 = thunk_ens ens in
                             [uu____11819; nil_pat; dec] in
                           req_true :: uu____11812 in
                         unit_tm :: uu____11805
                     | ens::dec::smtpat::[] when
                         ((is_ensures ens) && (is_decreases dec)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____11879 =
                           let uu____11886 =
                             let uu____11893 = thunk_ens ens in
                             [uu____11893; smtpat; dec] in
                           req_true :: uu____11886 in
                         unit_tm :: uu____11879
                     | req::ens::dec::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_decreases dec)
                         ->
                         let uu____11953 =
                           let uu____11960 =
                             let uu____11967 = thunk_ens ens in
                             [uu____11967; nil_pat; dec] in
                           req :: uu____11960 in
                         unit_tm :: uu____11953
                     | req::ens::smtpat::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____12027 =
                           let uu____12034 =
                             let uu____12041 = thunk_ens ens in
                             [uu____12041; smtpat] in
                           req :: uu____12034 in
                         unit_tm :: uu____12027
                     | req::ens::dec::smtpat::[] when
                         (((is_requires req) && (is_ensures ens)) &&
                            (is_smt_pat smtpat))
                           && (is_decreases dec)
                         ->
                         let uu____12106 =
                           let uu____12113 =
                             let uu____12120 = thunk_ens ens in
                             [uu____12120; dec; smtpat] in
                           req :: uu____12113 in
                         unit_tm :: uu____12106
                     | _other -> fail_lemma () in
                   let head_and_attributes =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) lemma in
                   (head_and_attributes, args1)
               | FStar_Parser_AST.Name l when
                   FStar_Syntax_DsEnv.is_effect_name env l ->
                   let uu____12182 =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) l in
                   (uu____12182, args)
               | FStar_Parser_AST.Name l when
                   (let uu____12210 = FStar_Syntax_DsEnv.current_module env in
                    FStar_Ident.lid_equals uu____12210
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Parser_Const.effect_Tot_lid
                        head1.FStar_Parser_AST.range), []), args)
               | FStar_Parser_AST.Name l when
                   (let uu____12228 = FStar_Syntax_DsEnv.current_module env in
                    FStar_Ident.lid_equals uu____12228
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Parser_Const.effect_GTot_lid
                        head1.FStar_Parser_AST.range), []), args)
               | FStar_Parser_AST.Name l when
                   (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                      ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                     || ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Parser_Const.effect_Tot_lid
                        head1.FStar_Parser_AST.range), []),
                     [(t1, FStar_Parser_AST.Nothing)])
               | uu____12266 ->
                   let default_effect =
                     let uu____12268 = FStar_Options.ml_ish () in
                     if uu____12268
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____12271 =
                           FStar_Options.warn_default_effects () in
                         if uu____12271
                         then
                           FStar_Errors.log_issue
                             head1.FStar_Parser_AST.range
                             (FStar_Errors.Warning_UseDefaultEffect,
                               "Using default effect Tot")
                         else ());
                        FStar_Parser_Const.effect_Tot_lid) in
                   (((FStar_Ident.set_lid_range default_effect
                        head1.FStar_Parser_AST.range), []),
                     [(t1, FStar_Parser_AST.Nothing)])) in
        let uu____12295 = pre_process_comp_typ t in
        match uu____12295 with
        | ((eff, cattributes), args) ->
            (Obj.magic
               (if (FStar_List.length args) = (Prims.parse_int "0")
                then
                  Obj.repr
                    (let uu____12344 =
                       let uu____12349 =
                         let uu____12350 =
                           FStar_Syntax_Print.lid_to_string eff in
                         FStar_Util.format1 "Not enough args to effect %s"
                           uu____12350 in
                       (FStar_Errors.Fatal_NotEnoughArgsToEffect,
                         uu____12349) in
                     fail1 () uu____12344)
                else Obj.repr ());
             (let is_universe uu____12359 =
                match uu____12359 with
                | (uu____12364, imp) -> imp = FStar_Parser_AST.UnivApp in
              let uu____12366 = FStar_Util.take is_universe args in
              match uu____12366 with
              | (universes, args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____12425 ->
                         match uu____12425 with
                         | (u, imp) -> desugar_universe u) universes in
                  let uu____12432 =
                    let uu____12447 = FStar_List.hd args1 in
                    let uu____12456 = FStar_List.tl args1 in
                    (uu____12447, uu____12456) in
                  (match uu____12432 with
                   | (result_arg, rest) ->
                       let result_typ =
                         desugar_typ env
                           (FStar_Pervasives_Native.fst result_arg) in
                       let rest1 = desugar_args env rest in
                       let uu____12511 =
                         let is_decrease uu____12547 =
                           match uu____12547 with
                           | (t1, uu____12557) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.pos = uu____12567;
                                       FStar_Syntax_Syntax.vars = uu____12568;_},
                                     uu____12569::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.decreases_lid
                                | uu____12600 -> false) in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease) in
                       (match uu____12511 with
                        | (dec, rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____12714 ->
                                      match uu____12714 with
                                      | (t1, uu____12724) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____12733,
                                                (arg, uu____12735)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____12764 -> failwith "impos"))) in
                            let no_additional_args =
                              let is_empty a l =
                                match l with
                                | [] -> true
                                | uu____12777 -> false in
                              (((is_empty () (Obj.magic decreases_clause)) &&
                                  (is_empty () (Obj.magic rest2)))
                                 && (is_empty () (Obj.magic cattributes)))
                                && (is_empty () (Obj.magic universes1)) in
                            if
                              no_additional_args &&
                                (FStar_Ident.lid_equals eff
                                   FStar_Parser_Const.effect_Tot_lid)
                            then FStar_Syntax_Syntax.mk_Total result_typ
                            else
                              if
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_GTot_lid)
                              then FStar_Syntax_Syntax.mk_GTotal result_typ
                              else
                                (let flags1 =
                                   if
                                     FStar_Ident.lid_equals eff
                                       FStar_Parser_Const.effect_Lemma_lid
                                   then [FStar_Syntax_Syntax.LEMMA]
                                   else
                                     if
                                       FStar_Ident.lid_equals eff
                                         FStar_Parser_Const.effect_Tot_lid
                                     then [FStar_Syntax_Syntax.TOTAL]
                                     else
                                       if
                                         FStar_Ident.lid_equals eff
                                           FStar_Parser_Const.effect_ML_lid
                                       then [FStar_Syntax_Syntax.MLEFFECT]
                                       else
                                         if
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_GTot_lid
                                         then
                                           [FStar_Syntax_Syntax.SOMETRIVIAL]
                                         else [] in
                                 let flags2 =
                                   FStar_List.append flags1 cattributes in
                                 let rest3 =
                                   if
                                     FStar_Ident.lid_equals eff
                                       FStar_Parser_Const.effect_Lemma_lid
                                   then
                                     match rest2 with
                                     | req::ens::(pat, aq)::[] ->
                                         let pat1 =
                                           match pat.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               when
                                               FStar_Syntax_Syntax.fv_eq_lid
                                                 fv
                                                 FStar_Parser_Const.nil_lid
                                               ->
                                               let nil =
                                                 FStar_Syntax_Syntax.mk_Tm_uinst
                                                   pat
                                                   [FStar_Syntax_Syntax.U_zero] in
                                               let pattern =
                                                 FStar_Syntax_Syntax.fvar
                                                   (FStar_Ident.set_lid_range
                                                      FStar_Parser_Const.pattern_lid
                                                      pat.FStar_Syntax_Syntax.pos)
                                                   FStar_Syntax_Syntax.Delta_constant
                                                   FStar_Pervasives_Native.None in
                                               FStar_Syntax_Syntax.mk_Tm_app
                                                 nil
                                                 [(pattern,
                                                    (FStar_Pervasives_Native.Some
                                                       FStar_Syntax_Syntax.imp_tag))]
                                                 FStar_Pervasives_Native.None
                                                 pat.FStar_Syntax_Syntax.pos
                                           | uu____12917 -> pat in
                                         let uu____12918 =
                                           let uu____12929 =
                                             let uu____12940 =
                                               let uu____12949 =
                                                 FStar_Syntax_Syntax.mk
                                                   (FStar_Syntax_Syntax.Tm_meta
                                                      (pat1,
                                                        (FStar_Syntax_Syntax.Meta_desugared
                                                           FStar_Syntax_Syntax.Meta_smt_pat)))
                                                   FStar_Pervasives_Native.None
                                                   pat1.FStar_Syntax_Syntax.pos in
                                               (uu____12949, aq) in
                                             [uu____12940] in
                                           ens :: uu____12929 in
                                         req :: uu____12918
                                     | uu____12990 -> rest2
                                   else rest2 in
                                 FStar_Syntax_Syntax.mk_Comp
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       universes1;
                                     FStar_Syntax_Syntax.effect_name = eff;
                                     FStar_Syntax_Syntax.result_typ =
                                       result_typ;
                                     FStar_Syntax_Syntax.effect_args = rest3;
                                     FStar_Syntax_Syntax.flags =
                                       (FStar_List.append flags2
                                          decreases_clause)
                                   })))))
and (desugar_formula :
  env_t -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term) =
  fun env ->
    fun f ->
      let connective s =
        match s with
        | "/\\" -> FStar_Pervasives_Native.Some FStar_Parser_Const.and_lid
        | "\\/" -> FStar_Pervasives_Native.Some FStar_Parser_Const.or_lid
        | "==>" -> FStar_Pervasives_Native.Some FStar_Parser_Const.imp_lid
        | "<==>" -> FStar_Pervasives_Native.Some FStar_Parser_Const.iff_lid
        | "~" -> FStar_Pervasives_Native.Some FStar_Parser_Const.not_lid
        | uu____13012 -> FStar_Pervasives_Native.None in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range in
      let setpos t =
        let uu___127_13029 = t in
        {
          FStar_Syntax_Syntax.n = (uu___127_13029.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___127_13029.FStar_Syntax_Syntax.vars)
        } in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___128_13063 = b in
             {
               FStar_Parser_AST.b = (uu___128_13063.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___128_13063.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___128_13063.FStar_Parser_AST.aqual)
             }) in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e ->
                       let uu____13122 = desugar_term env1 e in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____13122)))
            pats1 in
        match tk with
        | (FStar_Pervasives_Native.Some a, k) ->
            let uu____13135 = FStar_Syntax_DsEnv.push_bv env a in
            (match uu____13135 with
             | (env1, a1) ->
                 let a2 =
                   let uu___129_13145 = a1 in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___129_13145.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___129_13145.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   } in
                 let pats1 = desugar_pats env1 pats in
                 let body1 = desugar_formula env1 body in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____13167 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1))) in
                 let body3 =
                   let uu____13181 =
                     let uu____13184 =
                       let uu____13185 = FStar_Syntax_Syntax.mk_binder a2 in
                       [uu____13185] in
                     no_annot_abs uu____13184 body2 in
                   FStar_All.pipe_left setpos uu____13181 in
                 let uu____13190 =
                   let uu____13191 =
                     let uu____13206 =
                       FStar_Syntax_Syntax.fvar
                         (FStar_Ident.set_lid_range q
                            b.FStar_Parser_AST.brange)
                         (FStar_Syntax_Syntax.Delta_defined_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None in
                     let uu____13207 =
                       let uu____13210 = FStar_Syntax_Syntax.as_arg body3 in
                       [uu____13210] in
                     (uu____13206, uu____13207) in
                   FStar_Syntax_Syntax.Tm_app uu____13191 in
                 FStar_All.pipe_left mk1 uu____13190)
        | uu____13215 -> failwith "impossible" in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest in
            let body1 =
              let uu____13287 = q (rest, pats, body) in
              let uu____13294 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range in
              FStar_Parser_AST.mk_term uu____13287 uu____13294
                FStar_Parser_AST.Formula in
            let uu____13295 = q ([b], [], body1) in
            FStar_Parser_AST.mk_term uu____13295 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____13304 -> failwith "impossible" in
      let uu____13307 =
        let uu____13308 = unparen f in uu____13308.FStar_Parser_AST.tm in
      match uu____13307 with
      | FStar_Parser_AST.Labeled (f1, l, p) ->
          let f2 = desugar_formula env f1 in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([], uu____13315, uu____13316) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([], uu____13327, uu____13328) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3, pats, body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____13359 =
            push_quant (fun x -> FStar_Parser_AST.QForall x) binders pats
              body in
          desugar_formula env uu____13359
      | FStar_Parser_AST.QExists (_1::_2::_3, pats, body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____13395 =
            push_quant (fun x -> FStar_Parser_AST.QExists x) binders pats
              body in
          desugar_formula env uu____13395
      | FStar_Parser_AST.QForall (b::[], pats, body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[], pats, body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____13438 -> desugar_term env f
and (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env,
        (FStar_Syntax_Syntax.bv,
          FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2 Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun bs ->
      let uu____13443 =
        FStar_List.fold_left
          (fun uu____13479 ->
             fun b ->
               match uu____13479 with
               | (env1, out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___130_13531 = b in
                        {
                          FStar_Parser_AST.b =
                            (uu___130_13531.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___130_13531.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___130_13531.FStar_Parser_AST.aqual)
                        }) in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a, k) ->
                        let uu____13548 = FStar_Syntax_DsEnv.push_bv env1 a in
                        (match uu____13548 with
                         | (env2, a1) ->
                             let a2 =
                               let uu___131_13568 = a1 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___131_13568.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___131_13568.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               } in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____13585 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs in
      match uu____13443 with
      | (env1, tpars) -> (env1, (FStar_List.rev tpars))
and (desugar_binder :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Ident.ident FStar_Pervasives_Native.option,
        FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun b ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.TAnnotated (x, t) ->
          let uu____13672 = desugar_typ env t in
          ((FStar_Pervasives_Native.Some x), uu____13672)
      | FStar_Parser_AST.Annotated (x, t) ->
          let uu____13677 = desugar_typ env t in
          ((FStar_Pervasives_Native.Some x), uu____13677)
      | FStar_Parser_AST.TVariable x ->
          let uu____13681 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange in
          ((FStar_Pervasives_Native.Some x), uu____13681)
      | FStar_Parser_AST.NoName t ->
          let uu____13689 = desugar_typ env t in
          (FStar_Pervasives_Native.None, uu____13689)
      | FStar_Parser_AST.Variable x ->
          ((FStar_Pervasives_Native.Some x), FStar_Syntax_Syntax.tun)
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
               (fun uu___94_13722 ->
                  match uu___94_13722 with
                  | FStar_Syntax_Syntax.Abstract -> true
                  | FStar_Syntax_Syntax.Private -> true
                  | uu____13723 -> false)) in
        let quals2 q =
          let uu____13734 =
            (let uu____13737 = FStar_Syntax_DsEnv.iface env in
             Prims.op_Negation uu____13737) ||
              (FStar_Syntax_DsEnv.admitted_iface env) in
          if uu____13734
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1 in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d in
                let uu____13750 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d] in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng =
                    (FStar_Ident.range_of_lid disc_name);
                  FStar_Syntax_Syntax.sigquals = uu____13750;
                  FStar_Syntax_Syntax.sigmeta =
                    FStar_Syntax_Syntax.default_sigmeta;
                  FStar_Syntax_Syntax.sigattrs = []
                }))
let (mk_indexed_projector_names :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.fv_qual ->
      FStar_Syntax_DsEnv.env ->
        FStar_Ident.lid ->
          FStar_Syntax_Syntax.binder Prims.list ->
            FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun iquals ->
    fun fvq ->
      fun env ->
        fun lid ->
          fun fields ->
            let p = FStar_Ident.range_of_lid lid in
            let uu____13781 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i ->
                      fun uu____13811 ->
                        match uu____13811 with
                        | (x, uu____13819) ->
                            let uu____13820 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i in
                            (match uu____13820 with
                             | (field_name, uu____13828) ->
                                 let only_decl =
                                   ((let uu____13832 =
                                       FStar_Syntax_DsEnv.current_module env in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____13832)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____13834 =
                                        let uu____13835 =
                                          FStar_Syntax_DsEnv.current_module
                                            env in
                                        uu____13835.FStar_Ident.str in
                                      FStar_Options.dont_gen_projectors
                                        uu____13834) in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____13849 =
                                       FStar_List.filter
                                         (fun uu___95_13853 ->
                                            match uu___95_13853 with
                                            | FStar_Syntax_Syntax.Abstract ->
                                                false
                                            | uu____13854 -> true) q in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____13849
                                   else q in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___96_13867 ->
                                             match uu___96_13867 with
                                             | FStar_Syntax_Syntax.Abstract
                                                 -> true
                                             | FStar_Syntax_Syntax.Private ->
                                                 true
                                             | uu____13868 -> false)) in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1) in
                                 let decl =
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng =
                                       (FStar_Ident.range_of_lid field_name);
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   } in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____13876 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract) in
                                      if uu____13876
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          FStar_Syntax_Syntax.Delta_equational
                                      else
                                        FStar_Syntax_Syntax.Delta_equational in
                                    let lb =
                                      let uu____13881 =
                                        let uu____13886 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None in
                                        FStar_Util.Inr uu____13886 in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____13881;
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
                                      let uu____13890 =
                                        let uu____13891 =
                                          let uu____13898 =
                                            let uu____13901 =
                                              let uu____13902 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right in
                                              FStar_All.pipe_right
                                                uu____13902
                                                (fun fv ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                            [uu____13901] in
                                          ((false, [lb]), uu____13898) in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____13891 in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____13890;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      } in
                                    if no_decl then [impl] else [decl; impl])))) in
            FStar_All.pipe_right uu____13781 FStar_List.flatten
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
            (lid, uu____13946, t, uu____13948, n1, uu____13950) when
            Prims.op_Negation
              (FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid)
            ->
            let uu____13955 = FStar_Syntax_Util.arrow_formals t in
            (match uu____13955 with
             | (formals, uu____13971) ->
                 (match formals with
                  | [] -> []
                  | uu____13994 ->
                      let filter_records uu___97_14006 =
                        match uu___97_14006 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____14009, fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____14021 -> FStar_Pervasives_Native.None in
                      let fv_qual =
                        let uu____14023 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records in
                        match uu____14023 with
                        | FStar_Pervasives_Native.None ->
                            FStar_Syntax_Syntax.Data_ctor
                        | FStar_Pervasives_Native.Some q -> q in
                      let iquals1 =
                        if
                          FStar_List.contains FStar_Syntax_Syntax.Abstract
                            iquals
                        then FStar_Syntax_Syntax.Private :: iquals
                        else iquals in
                      let uu____14033 = FStar_Util.first_N n1 formals in
                      (match uu____14033 with
                       | (uu____14056, rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____14082 -> []
let (mk_typ_abbrev :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.typ ->
          FStar_Syntax_Syntax.term ->
            FStar_Ident.lident Prims.list ->
              FStar_Syntax_Syntax.qualifier Prims.list ->
                FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun lid ->
    fun uvs ->
      fun typars ->
        fun k ->
          fun t ->
            fun lids ->
              fun quals ->
                fun rng ->
                  let dd =
                    let uu____14132 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract) in
                    if uu____14132
                    then
                      let uu____14135 =
                        FStar_Syntax_Util.incr_delta_qualifier t in
                      FStar_Syntax_Syntax.Delta_abstract uu____14135
                    else FStar_Syntax_Util.incr_delta_qualifier t in
                  let lb =
                    let uu____14138 =
                      let uu____14143 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None in
                      FStar_Util.Inr uu____14143 in
                    let uu____14144 =
                      let uu____14147 = FStar_Syntax_Syntax.mk_Total k in
                      FStar_Syntax_Util.arrow typars uu____14147 in
                    let uu____14150 = no_annot_abs typars t in
                    {
                      FStar_Syntax_Syntax.lbname = uu____14138;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____14144;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____14150;
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
                    FStar_Syntax_Syntax.sigattrs = []
                  }
let rec (desugar_tycon :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Parser_AST.tycon Prims.list ->
          (env_t, FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun d ->
      fun quals ->
        fun tcs ->
          let rng = d.FStar_Parser_AST.drange in
          let tycon_id uu___98_14197 =
            match uu___98_14197 with
            | FStar_Parser_AST.TyconAbstract (id1, uu____14199, uu____14200)
                -> id1
            | FStar_Parser_AST.TyconAbbrev
                (id1, uu____14210, uu____14211, uu____14212) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1, uu____14222, uu____14223, uu____14224) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1, uu____14254, uu____14255, uu____14256) -> id1 in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x, uu____14298) ->
                let uu____14299 =
                  let uu____14300 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____14300 in
                FStar_Parser_AST.mk_term uu____14299 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____14302 =
                  let uu____14303 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____14303 in
                FStar_Parser_AST.mk_term uu____14302 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a, uu____14305) ->
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
              | uu____14328 -> FStar_Parser_AST.Nothing in
            FStar_List.fold_left
              (fun out ->
                 fun b ->
                   let uu____14334 =
                     let uu____14335 =
                       let uu____14342 = binder_to_term b in
                       (out, uu____14342, (imp_of_aqual b)) in
                     FStar_Parser_AST.App uu____14335 in
                   FStar_Parser_AST.mk_term uu____14334
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders in
          let tycon_record_as_variant uu___99_14352 =
            match uu___99_14352 with
            | FStar_Parser_AST.TyconRecord (id1, parms, kopt, fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange)) in
                let mfields =
                  FStar_List.map
                    (fun uu____14407 ->
                       match uu____14407 with
                       | (x, t, uu____14418) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated
                                ((FStar_Syntax_Util.mangle_field_name x), t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields in
                let result =
                  let uu____14424 =
                    let uu____14425 =
                      let uu____14426 = FStar_Ident.lid_of_ids [id1] in
                      FStar_Parser_AST.Var uu____14426 in
                    FStar_Parser_AST.mk_term uu____14425
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                  apply_binders uu____14424 parms in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                let uu____14430 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____14457 ->
                          match uu____14457 with
                          | (x, uu____14467, uu____14468) ->
                              FStar_Syntax_Util.unmangle_field_name x)) in
                ((FStar_Parser_AST.TyconVariant
                    (id1, parms, kopt,
                      [(constrName, (FStar_Pervasives_Native.Some constrTyp),
                         FStar_Pervasives_Native.None, false)])),
                  uu____14430)
            | uu____14521 -> failwith "impossible" in
          let desugar_abstract_tc quals1 _env mutuals uu___100_14552 =
            match uu___100_14552 with
            | FStar_Parser_AST.TyconAbstract (id1, binders, kopt) ->
                let uu____14576 = typars_of_binders _env binders in
                (match uu____14576 with
                 | (_env', typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k in
                     let tconstr =
                       let uu____14622 =
                         let uu____14623 =
                           let uu____14624 = FStar_Ident.lid_of_ids [id1] in
                           FStar_Parser_AST.Var uu____14624 in
                         FStar_Parser_AST.mk_term uu____14623
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level in
                       apply_binders uu____14622 binders in
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
                         FStar_Syntax_Syntax.sigattrs = []
                       } in
                     let _env1 =
                       FStar_Syntax_DsEnv.push_top_level_rec_binding _env id1
                         FStar_Syntax_Syntax.Delta_constant in
                     let _env2 =
                       FStar_Syntax_DsEnv.push_top_level_rec_binding _env'
                         id1 FStar_Syntax_Syntax.Delta_constant in
                     (_env1, _env2, se, tconstr))
            | uu____14637 -> failwith "Unexpected tycon" in
          let push_tparams env1 bs =
            let uu____14681 =
              FStar_List.fold_left
                (fun uu____14721 ->
                   fun uu____14722 ->
                     match (uu____14721, uu____14722) with
                     | ((env2, tps), (x, imp)) ->
                         let uu____14813 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname in
                         (match uu____14813 with
                          | (env3, y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs in
            match uu____14681 with
            | (env2, bs1) -> (env2, (FStar_List.rev bs1)) in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1, bs, kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None ->
                    let uu____14926 = tm_type_z id1.FStar_Ident.idRange in
                    FStar_Pervasives_Native.Some uu____14926
                | uu____14927 -> kopt in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1) in
              let uu____14935 = desugar_abstract_tc quals env [] tc in
              (match uu____14935 with
               | (uu____14948, uu____14949, se, uu____14951) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l, uu____14954, typars, k, [], []) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____14971 =
                                 let uu____14972 = FStar_Options.ml_ish () in
                                 Prims.op_Negation uu____14972 in
                               if uu____14971
                               then
                                 let uu____14973 =
                                   let uu____14978 =
                                     let uu____14979 =
                                       FStar_Syntax_Print.lid_to_string l in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____14979 in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____14978) in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____14973
                               else ());
                              FStar_Syntax_Syntax.Assumption
                              ::
                              FStar_Syntax_Syntax.New
                              ::
                              quals1) in
                         let t =
                           match typars with
                           | [] -> k
                           | uu____14986 ->
                               let uu____14987 =
                                 let uu____14990 =
                                   let uu____14991 =
                                     let uu____15004 =
                                       FStar_Syntax_Syntax.mk_Total k in
                                     (typars, uu____15004) in
                                   FStar_Syntax_Syntax.Tm_arrow uu____14991 in
                                 FStar_Syntax_Syntax.mk uu____14990 in
                               uu____14987 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng in
                         let uu___132_15008 = se in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___132_15008.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___132_15008.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___132_15008.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____15011 -> failwith "Impossible" in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1 in
                   let env2 =
                     let uu____15014 = FStar_Syntax_DsEnv.qualify env1 id1 in
                     FStar_Syntax_DsEnv.push_doc env1 uu____15014
                       d.FStar_Parser_AST.doc in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1, binders, kopt, t))::[] ->
              let uu____15029 = typars_of_binders env binders in
              (match uu____15029 with
               | (env', typars) ->
                   let k =
                     match kopt with
                     | FStar_Pervasives_Native.None ->
                         let uu____15065 =
                           FStar_Util.for_some
                             (fun uu___101_15067 ->
                                match uu___101_15067 with
                                | FStar_Syntax_Syntax.Effect -> true
                                | uu____15068 -> false) quals in
                         if uu____15065
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Util.ktype
                     | FStar_Pervasives_Native.Some k -> desugar_term env' k in
                   let t0 = t in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1 in
                   let se =
                     let uu____15074 =
                       FStar_All.pipe_right quals
                         (FStar_List.contains FStar_Syntax_Syntax.Effect) in
                     if uu____15074
                     then
                       let uu____15077 =
                         let uu____15084 =
                           let uu____15085 = unparen t in
                           uu____15085.FStar_Parser_AST.tm in
                         match uu____15084 with
                         | FStar_Parser_AST.Construct (head1, args) ->
                             let uu____15106 =
                               match FStar_List.rev args with
                               | (last_arg, uu____15136)::args_rev ->
                                   let uu____15148 =
                                     let uu____15149 = unparen last_arg in
                                     uu____15149.FStar_Parser_AST.tm in
                                   (match uu____15148 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____15177 -> ([], args))
                               | uu____15186 -> ([], args) in
                             (match uu____15106 with
                              | (cattributes, args1) ->
                                  let uu____15225 =
                                    desugar_attributes env cattributes in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____15225))
                         | uu____15236 -> (t, []) in
                       match uu____15077 with
                       | (t1, cattributes) ->
                           let c =
                             desugar_comp t1.FStar_Parser_AST.range env' t1 in
                           let typars1 =
                             FStar_Syntax_Subst.close_binders typars in
                           let c1 = FStar_Syntax_Subst.close_comp typars1 c in
                           let quals1 =
                             FStar_All.pipe_right quals
                               (FStar_List.filter
                                  (fun uu___102_15258 ->
                                     match uu___102_15258 with
                                     | FStar_Syntax_Syntax.Effect -> false
                                     | uu____15259 -> true)) in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_effect_abbrev
                                  (qlid, [], typars1, c1,
                                    (FStar_List.append cattributes
                                       (FStar_Syntax_Util.comp_flags c1))));
                             FStar_Syntax_Syntax.sigrng = rng;
                             FStar_Syntax_Syntax.sigquals = quals1;
                             FStar_Syntax_Syntax.sigmeta =
                               FStar_Syntax_Syntax.default_sigmeta;
                             FStar_Syntax_Syntax.sigattrs = []
                           }
                     else
                       (let t1 = desugar_typ env' t in
                        mk_typ_abbrev qlid [] typars k t1 [qlid] quals rng) in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se in
                   let env2 =
                     FStar_Syntax_DsEnv.push_doc env1 qlid
                       d.FStar_Parser_AST.doc in
                   (env2, [se]))
          | (FStar_Parser_AST.TyconRecord uu____15270)::[] ->
              let trec = FStar_List.hd tcs in
              let uu____15294 = tycon_record_as_variant trec in
              (match uu____15294 with
               | (t, fs) ->
                   let uu____15311 =
                     let uu____15314 =
                       let uu____15315 =
                         let uu____15324 =
                           let uu____15327 =
                             FStar_Syntax_DsEnv.current_module env in
                           FStar_Ident.ids_of_lid uu____15327 in
                         (uu____15324, fs) in
                       FStar_Syntax_Syntax.RecordType uu____15315 in
                     uu____15314 :: quals in
                   desugar_tycon env d uu____15311 [t])
          | uu____15332::uu____15333 ->
              let env0 = env in
              let mutuals =
                FStar_List.map
                  (fun x ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs in
              let rec collect_tcs quals1 et tc =
                let uu____15494 = et in
                match uu____15494 with
                | (env1, tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____15719 ->
                         let trec = tc in
                         let uu____15743 = tycon_record_as_variant trec in
                         (match uu____15743 with
                          | (t, fs) ->
                              let uu____15802 =
                                let uu____15805 =
                                  let uu____15806 =
                                    let uu____15815 =
                                      let uu____15818 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1 in
                                      FStar_Ident.ids_of_lid uu____15818 in
                                    (uu____15815, fs) in
                                  FStar_Syntax_Syntax.RecordType uu____15806 in
                                uu____15805 :: quals1 in
                              collect_tcs uu____15802 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1, binders, kopt, constructors) ->
                         let uu____15905 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt)) in
                         (match uu____15905 with
                          | (env2, uu____15965, se, tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1, binders, kopt, t)
                         ->
                         let uu____16114 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt)) in
                         (match uu____16114 with
                          | (env2, uu____16174, se, tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____16299 ->
                         failwith "Unrecognized mutual type definition") in
              let uu____16346 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs in
              (match uu____16346 with
               | (env1, tcs1) ->
                   let tcs2 = FStar_List.rev tcs1 in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___104_16857 ->
                             match uu___104_16857 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1, uvs, tpars, k, uu____16924,
                                       uu____16925);
                                    FStar_Syntax_Syntax.sigrng = uu____16926;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____16927;
                                    FStar_Syntax_Syntax.sigmeta = uu____16928;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____16929;_},
                                  binders, t, quals1)
                                 ->
                                 let t1 =
                                   let uu____16990 =
                                     typars_of_binders env1 binders in
                                   match uu____16990 with
                                   | (env2, tpars1) ->
                                       let uu____17021 =
                                         push_tparams env2 tpars1 in
                                       (match uu____17021 with
                                        | (env_tps, tpars2) ->
                                            let t1 = desugar_typ env_tps t in
                                            let tpars3 =
                                              FStar_Syntax_Subst.close_binders
                                                tpars2 in
                                            FStar_Syntax_Subst.close tpars3
                                              t1) in
                                 let uu____17054 =
                                   let uu____17075 =
                                     mk_typ_abbrev id1 uvs tpars k t1 
                                       [id1] quals1 rng in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____17075) in
                                 [uu____17054]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname, univs1, tpars, k, mutuals1,
                                       uu____17143);
                                    FStar_Syntax_Syntax.sigrng = uu____17144;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____17146;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____17147;_},
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
                                 let uu____17243 = push_tparams env1 tpars in
                                 (match uu____17243 with
                                  | (env_tps, tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____17320 ->
                                             match uu____17320 with
                                             | (x, uu____17334) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps in
                                      let tot_tconstr = mk_tot tconstr in
                                      let uu____17342 =
                                        let uu____17371 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____17485 ->
                                                  match uu____17485 with
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
                                                        let uu____17541 =
                                                          close env_tps t in
                                                        desugar_term env_tps
                                                          uu____17541 in
                                                      let name =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env1 id1 in
                                                      let quals2 =
                                                        FStar_All.pipe_right
                                                          tname_quals
                                                          (FStar_List.collect
                                                             (fun
                                                                uu___103_17552
                                                                ->
                                                                match uu___103_17552
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____17564
                                                                    -> [])) in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars in
                                                      let uu____17572 =
                                                        let uu____17593 =
                                                          let uu____17594 =
                                                            let uu____17595 =
                                                              let uu____17610
                                                                =
                                                                let uu____17613
                                                                  =
                                                                  let uu____17616
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____17616 in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____17613 in
                                                              (name, univs1,
                                                                uu____17610,
                                                                tname, ntps,
                                                                mutuals1) in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____17595 in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____17594;
                                                            FStar_Syntax_Syntax.sigrng
                                                              = rng;
                                                            FStar_Syntax_Syntax.sigquals
                                                              = quals2;
                                                            FStar_Syntax_Syntax.sigmeta
                                                              =
                                                              FStar_Syntax_Syntax.default_sigmeta;
                                                            FStar_Syntax_Syntax.sigattrs
                                                              = []
                                                          } in
                                                        ((name, doc1), tps,
                                                          uu____17593) in
                                                      (name, uu____17572))) in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____17371 in
                                      (match uu____17342 with
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
                                                 []
                                             })
                                           :: constrs1))
                             | uu____17855 -> failwith "impossible")) in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____17987 ->
                             match uu____17987 with
                             | (name_doc, uu____18015, uu____18016) ->
                                 name_doc)) in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____18096 ->
                             match uu____18096 with
                             | (uu____18117, uu____18118, se) -> se)) in
                   let uu____18148 =
                     let uu____18155 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____18155 rng in
                   (match uu____18148 with
                    | (bundle, abbrevs) ->
                        let env2 = FStar_Syntax_DsEnv.push_sigelt env0 bundle in
                        let env3 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env2 abbrevs in
                        let data_ops =
                          FStar_All.pipe_right docs_tps_sigelts
                            (FStar_List.collect
                               (fun uu____18221 ->
                                  match uu____18221 with
                                  | (uu____18244, tps, se) ->
                                      mk_data_projector_names quals env3 se)) in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname, uu____18295, tps, k,
                                       uu____18298, constrs)
                                      when
                                      (FStar_List.length constrs) >
                                        (Prims.parse_int "1")
                                      ->
                                      let quals1 =
                                        se.FStar_Syntax_Syntax.sigquals in
                                      let quals2 =
                                        if
                                          FStar_List.contains
                                            FStar_Syntax_Syntax.Abstract
                                            quals1
                                        then FStar_Syntax_Syntax.Private ::
                                          quals1
                                        else quals1 in
                                      mk_data_discriminators quals2 env3
                                        constrs
                                  | uu____18317 -> [])) in
                        let ops = FStar_List.append discs data_ops in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc ->
                               fun uu____18334 ->
                                 match uu____18334 with
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
      (FStar_Syntax_DsEnv.env, FStar_Syntax_Syntax.binder Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun binders ->
      let uu____18369 =
        FStar_List.fold_left
          (fun uu____18392 ->
             fun b ->
               match uu____18392 with
               | (env1, binders1) ->
                   let uu____18412 = desugar_binder env1 b in
                   (match uu____18412 with
                    | (FStar_Pervasives_Native.Some a, k) ->
                        let uu____18429 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k) in
                        (match uu____18429 with
                         | (binder, env2) -> (env2, (binder :: binders1)))
                    | uu____18446 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders in
      match uu____18369 with
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
          let uu____18491 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___105_18496 ->
                    match uu___105_18496 with
                    | FStar_Syntax_Syntax.Reflectable uu____18497 -> true
                    | uu____18498 -> false)) in
          if uu____18491
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident in
            let reflect_lid =
              FStar_All.pipe_right (FStar_Ident.id_of_text "reflect")
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
                FStar_Syntax_Syntax.sigattrs = []
              } in
            FStar_Syntax_DsEnv.push_sigelt env refl_decl
          else env
let rec (desugar_effect :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.decl ->
      FStar_Parser_AST.qualifiers ->
        FStar_Ident.ident ->
          FStar_Parser_AST.binder Prims.list ->
            FStar_Parser_AST.term ->
              FStar_Parser_AST.decl Prims.list ->
                FStar_Parser_AST.term Prims.list ->
                  (FStar_Syntax_DsEnv.env,
                    FStar_Syntax_Syntax.sigelt Prims.list)
                    FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun d ->
      fun quals ->
        fun eff_name ->
          fun eff_binders ->
            fun eff_typ ->
              fun eff_decls ->
                fun attrs ->
                  let env0 = env in
                  let monad_env =
                    FStar_Syntax_DsEnv.enter_monad_scope env eff_name in
                  let uu____18606 = desugar_binders monad_env eff_binders in
                  match uu____18606 with
                  | (env1, binders) ->
                      let eff_t = desugar_term env1 eff_typ in
                      let for_free =
                        let uu____18627 =
                          let uu____18628 =
                            let uu____18635 =
                              FStar_Syntax_Util.arrow_formals eff_t in
                            FStar_Pervasives_Native.fst uu____18635 in
                          FStar_List.length uu____18628 in
                        uu____18627 = (Prims.parse_int "1") in
                      let mandatory_members =
                        let rr_members = ["repr"; "return"; "bind"] in
                        if for_free
                        then rr_members
                        else
                          FStar_List.append rr_members
                            ["return_wp";
                            "bind_wp";
                            "if_then_else";
                            "ite_wp";
                            "stronger";
                            "close_wp";
                            "assert_p";
                            "assume_p";
                            "null_wp";
                            "trivial"] in
                      let name_of_eff_decl decl =
                        match decl.FStar_Parser_AST.d with
                        | FStar_Parser_AST.Tycon
                            (uu____18677,
                             (FStar_Parser_AST.TyconAbbrev
                              (name, uu____18679, uu____18680, uu____18681),
                              uu____18682)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____18715 ->
                            failwith "Malformed effect member declaration." in
                      let uu____18716 =
                        FStar_List.partition
                          (fun decl ->
                             let uu____18728 = name_of_eff_decl decl in
                             FStar_List.mem uu____18728 mandatory_members)
                          eff_decls in
                      (match uu____18716 with
                       | (mandatory_members_decls, actions) ->
                           let uu____18745 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____18774 ->
                                     fun decl ->
                                       match uu____18774 with
                                       | (env2, out) ->
                                           let uu____18794 =
                                             desugar_decl env2 decl in
                                           (match uu____18794 with
                                            | (env3, ses) ->
                                                let uu____18807 =
                                                  let uu____18810 =
                                                    FStar_List.hd ses in
                                                  uu____18810 :: out in
                                                (env3, uu____18807)))
                                  (env1, [])) in
                           (match uu____18745 with
                            | (env2, decls) ->
                                let binders1 =
                                  FStar_Syntax_Subst.close_binders binders in
                                let actions_docs =
                                  FStar_All.pipe_right actions
                                    (FStar_List.map
                                       (fun d1 ->
                                          match d1.FStar_Parser_AST.d with
                                          | FStar_Parser_AST.Tycon
                                              (uu____18878,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name, action_params,
                                                 uu____18881,
                                                 {
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.Construct
                                                     (uu____18882,
                                                      (def, uu____18884)::
                                                      (cps_type, uu____18886)::[]);
                                                   FStar_Parser_AST.range =
                                                     uu____18887;
                                                   FStar_Parser_AST.level =
                                                     uu____18888;_}),
                                                doc1)::[])
                                              when Prims.op_Negation for_free
                                              ->
                                              let uu____18940 =
                                                desugar_binders env2
                                                  action_params in
                                              (match uu____18940 with
                                               | (env3, action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1 in
                                                   let uu____18960 =
                                                     let uu____18961 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name in
                                                     let uu____18962 =
                                                       let uu____18963 =
                                                         desugar_term env3
                                                           def in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____18963 in
                                                     let uu____18968 =
                                                       let uu____18969 =
                                                         desugar_typ env3
                                                           cps_type in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____18969 in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____18961;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____18962;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____18968
                                                     } in
                                                   (uu____18960, doc1))
                                          | FStar_Parser_AST.Tycon
                                              (uu____18976,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name, action_params,
                                                 uu____18979, defn),
                                                doc1)::[])
                                              when for_free ->
                                              let uu____19014 =
                                                desugar_binders env2
                                                  action_params in
                                              (match uu____19014 with
                                               | (env3, action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1 in
                                                   let uu____19034 =
                                                     let uu____19035 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name in
                                                     let uu____19036 =
                                                       let uu____19037 =
                                                         desugar_term env3
                                                           defn in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____19037 in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____19035;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____19036;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     } in
                                                   (uu____19034, doc1))
                                          | uu____19044 ->
                                              FStar_Errors.raise_error
                                                (FStar_Errors.Fatal_MalformedActionDeclaration,
                                                  "Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples).")
                                                d1.FStar_Parser_AST.drange)) in
                                let actions1 =
                                  FStar_List.map FStar_Pervasives_Native.fst
                                    actions_docs in
                                let eff_t1 =
                                  FStar_Syntax_Subst.close binders1 eff_t in
                                let lookup1 s =
                                  let l =
                                    FStar_Syntax_DsEnv.qualify env2
                                      (FStar_Ident.mk_ident
                                         (s, (d.FStar_Parser_AST.drange))) in
                                  let uu____19074 =
                                    let uu____19075 =
                                      FStar_Syntax_DsEnv.fail_or env2
                                        (FStar_Syntax_DsEnv.try_lookup_definition
                                           env2) l in
                                    FStar_All.pipe_left
                                      (FStar_Syntax_Subst.close binders1)
                                      uu____19075 in
                                  ([], uu____19074) in
                                let mname =
                                  FStar_Syntax_DsEnv.qualify env0 eff_name in
                                let qualifiers =
                                  FStar_List.collect
                                    (trans_qual d.FStar_Parser_AST.drange
                                       (FStar_Pervasives_Native.Some mname))
                                    quals in
                                let se =
                                  if for_free
                                  then
                                    let dummy_tscheme =
                                      let uu____19092 =
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange in
                                      ([], uu____19092) in
                                    let uu____19099 =
                                      let uu____19100 =
                                        let uu____19101 =
                                          let uu____19102 = lookup1 "repr" in
                                          FStar_Pervasives_Native.snd
                                            uu____19102 in
                                        let uu____19111 = lookup1 "return" in
                                        let uu____19112 = lookup1 "bind" in
                                        let uu____19113 =
                                          FStar_List.map (desugar_term env2)
                                            attrs in
                                        {
                                          FStar_Syntax_Syntax.cattributes =
                                            [];
                                          FStar_Syntax_Syntax.mname = mname;
                                          FStar_Syntax_Syntax.univs = [];
                                          FStar_Syntax_Syntax.binders =
                                            binders1;
                                          FStar_Syntax_Syntax.signature =
                                            eff_t1;
                                          FStar_Syntax_Syntax.ret_wp =
                                            dummy_tscheme;
                                          FStar_Syntax_Syntax.bind_wp =
                                            dummy_tscheme;
                                          FStar_Syntax_Syntax.if_then_else =
                                            dummy_tscheme;
                                          FStar_Syntax_Syntax.ite_wp =
                                            dummy_tscheme;
                                          FStar_Syntax_Syntax.stronger =
                                            dummy_tscheme;
                                          FStar_Syntax_Syntax.close_wp =
                                            dummy_tscheme;
                                          FStar_Syntax_Syntax.assert_p =
                                            dummy_tscheme;
                                          FStar_Syntax_Syntax.assume_p =
                                            dummy_tscheme;
                                          FStar_Syntax_Syntax.null_wp =
                                            dummy_tscheme;
                                          FStar_Syntax_Syntax.trivial =
                                            dummy_tscheme;
                                          FStar_Syntax_Syntax.repr =
                                            uu____19101;
                                          FStar_Syntax_Syntax.return_repr =
                                            uu____19111;
                                          FStar_Syntax_Syntax.bind_repr =
                                            uu____19112;
                                          FStar_Syntax_Syntax.actions =
                                            actions1;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            uu____19113
                                        } in
                                      FStar_Syntax_Syntax.Sig_new_effect_for_free
                                        uu____19100 in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____19099;
                                      FStar_Syntax_Syntax.sigrng =
                                        (d.FStar_Parser_AST.drange);
                                      FStar_Syntax_Syntax.sigquals =
                                        qualifiers;
                                      FStar_Syntax_Syntax.sigmeta =
                                        FStar_Syntax_Syntax.default_sigmeta;
                                      FStar_Syntax_Syntax.sigattrs = []
                                    }
                                  else
                                    (let rr =
                                       FStar_Util.for_some
                                         (fun uu___106_19119 ->
                                            match uu___106_19119 with
                                            | FStar_Syntax_Syntax.Reifiable
                                                -> true
                                            | FStar_Syntax_Syntax.Reflectable
                                                uu____19120 -> true
                                            | uu____19121 -> false)
                                         qualifiers in
                                     let un_ts =
                                       ([], FStar_Syntax_Syntax.tun) in
                                     let uu____19131 =
                                       let uu____19132 =
                                         let uu____19133 =
                                           lookup1 "return_wp" in
                                         let uu____19134 = lookup1 "bind_wp" in
                                         let uu____19135 =
                                           lookup1 "if_then_else" in
                                         let uu____19136 = lookup1 "ite_wp" in
                                         let uu____19137 = lookup1 "stronger" in
                                         let uu____19138 = lookup1 "close_wp" in
                                         let uu____19139 = lookup1 "assert_p" in
                                         let uu____19140 = lookup1 "assume_p" in
                                         let uu____19141 = lookup1 "null_wp" in
                                         let uu____19142 = lookup1 "trivial" in
                                         let uu____19143 =
                                           if rr
                                           then
                                             let uu____19144 = lookup1 "repr" in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.snd
                                               uu____19144
                                           else FStar_Syntax_Syntax.tun in
                                         let uu____19160 =
                                           if rr
                                           then lookup1 "return"
                                           else un_ts in
                                         let uu____19162 =
                                           if rr
                                           then lookup1 "bind"
                                           else un_ts in
                                         let uu____19164 =
                                           FStar_List.map (desugar_term env2)
                                             attrs in
                                         {
                                           FStar_Syntax_Syntax.cattributes =
                                             [];
                                           FStar_Syntax_Syntax.mname = mname;
                                           FStar_Syntax_Syntax.univs = [];
                                           FStar_Syntax_Syntax.binders =
                                             binders1;
                                           FStar_Syntax_Syntax.signature =
                                             eff_t1;
                                           FStar_Syntax_Syntax.ret_wp =
                                             uu____19133;
                                           FStar_Syntax_Syntax.bind_wp =
                                             uu____19134;
                                           FStar_Syntax_Syntax.if_then_else =
                                             uu____19135;
                                           FStar_Syntax_Syntax.ite_wp =
                                             uu____19136;
                                           FStar_Syntax_Syntax.stronger =
                                             uu____19137;
                                           FStar_Syntax_Syntax.close_wp =
                                             uu____19138;
                                           FStar_Syntax_Syntax.assert_p =
                                             uu____19139;
                                           FStar_Syntax_Syntax.assume_p =
                                             uu____19140;
                                           FStar_Syntax_Syntax.null_wp =
                                             uu____19141;
                                           FStar_Syntax_Syntax.trivial =
                                             uu____19142;
                                           FStar_Syntax_Syntax.repr =
                                             uu____19143;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____19160;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____19162;
                                           FStar_Syntax_Syntax.actions =
                                             actions1;
                                           FStar_Syntax_Syntax.eff_attrs =
                                             uu____19164
                                         } in
                                       FStar_Syntax_Syntax.Sig_new_effect
                                         uu____19132 in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         uu____19131;
                                       FStar_Syntax_Syntax.sigrng =
                                         (d.FStar_Parser_AST.drange);
                                       FStar_Syntax_Syntax.sigquals =
                                         qualifiers;
                                       FStar_Syntax_Syntax.sigmeta =
                                         FStar_Syntax_Syntax.default_sigmeta;
                                       FStar_Syntax_Syntax.sigattrs = []
                                     }) in
                                let env3 =
                                  FStar_Syntax_DsEnv.push_sigelt env0 se in
                                let env4 =
                                  FStar_Syntax_DsEnv.push_doc env3 mname
                                    d.FStar_Parser_AST.doc in
                                let env5 =
                                  FStar_All.pipe_right actions_docs
                                    (FStar_List.fold_left
                                       (fun env5 ->
                                          fun uu____19190 ->
                                            match uu____19190 with
                                            | (a, doc1) ->
                                                let env6 =
                                                  let uu____19204 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____19204 in
                                                FStar_Syntax_DsEnv.push_doc
                                                  env6
                                                  a.FStar_Syntax_Syntax.action_name
                                                  doc1) env4) in
                                let env6 =
                                  push_reflect_effect env5 qualifiers mname
                                    d.FStar_Parser_AST.drange in
                                let env7 =
                                  FStar_Syntax_DsEnv.push_doc env6 mname
                                    d.FStar_Parser_AST.doc in
                                (env7, [se])))
and (desugar_redefine_effect :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.decl ->
      (FStar_Ident.lident FStar_Pervasives_Native.option ->
         FStar_Parser_AST.qualifier ->
           FStar_Syntax_Syntax.qualifier Prims.list)
        ->
        FStar_Parser_AST.qualifier Prims.list ->
          FStar_Ident.ident ->
            FStar_Parser_AST.binder Prims.list ->
              FStar_Parser_AST.term ->
                (FStar_Syntax_DsEnv.env,
                  FStar_Syntax_Syntax.sigelt Prims.list)
                  FStar_Pervasives_Native.tuple2)
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
                let uu____19230 = desugar_binders env1 eff_binders in
                match uu____19230 with
                | (env2, binders) ->
                    let uu____19249 =
                      let uu____19268 = head_and_args defn in
                      match uu____19268 with
                      | (head1, args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____19313 ->
                                let uu____19314 =
                                  let uu____19319 =
                                    let uu____19320 =
                                      let uu____19321 =
                                        FStar_Parser_AST.term_to_string head1 in
                                      Prims.strcat uu____19321 " not found" in
                                    Prims.strcat "Effect " uu____19320 in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____19319) in
                                FStar_Errors.raise_error uu____19314
                                  d.FStar_Parser_AST.drange in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid in
                          let uu____19323 =
                            match FStar_List.rev args with
                            | (last_arg, uu____19353)::args_rev ->
                                let uu____19365 =
                                  let uu____19366 = unparen last_arg in
                                  uu____19366.FStar_Parser_AST.tm in
                                (match uu____19365 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____19394 -> ([], args))
                            | uu____19403 -> ([], args) in
                          (match uu____19323 with
                           | (cattributes, args1) ->
                               let uu____19454 = desugar_args env2 args1 in
                               let uu____19463 =
                                 desugar_attributes env2 cattributes in
                               (lid, ed, uu____19454, uu____19463)) in
                    (match uu____19249 with
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
                          (let uu____19519 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit in
                           match uu____19519 with
                           | (ed_binders, uu____19533, ed_binders_opening) ->
                               let sub1 uu____19544 =
                                 match uu____19544 with
                                 | (us, x) ->
                                     let x1 =
                                       let uu____19558 =
                                         FStar_Syntax_Subst.shift_subst
                                           (FStar_List.length us)
                                           ed_binders_opening in
                                       FStar_Syntax_Subst.subst uu____19558 x in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args in
                                     let uu____19562 =
                                       let uu____19563 =
                                         FStar_Syntax_Subst.subst s x1 in
                                       (us, uu____19563) in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____19562 in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name in
                               let ed1 =
                                 let uu____19568 =
                                   let uu____19569 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature)) in
                                   FStar_Pervasives_Native.snd uu____19569 in
                                 let uu____19580 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp in
                                 let uu____19581 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp in
                                 let uu____19582 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else in
                                 let uu____19583 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp in
                                 let uu____19584 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger in
                                 let uu____19585 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp in
                                 let uu____19586 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p in
                                 let uu____19587 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p in
                                 let uu____19588 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp in
                                 let uu____19589 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial in
                                 let uu____19590 =
                                   let uu____19591 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr)) in
                                   FStar_Pervasives_Native.snd uu____19591 in
                                 let uu____19602 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr in
                                 let uu____19603 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr in
                                 let uu____19604 =
                                   FStar_List.map
                                     (fun action ->
                                        let uu____19612 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name in
                                        let uu____19613 =
                                          let uu____19614 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn)) in
                                          FStar_Pervasives_Native.snd
                                            uu____19614 in
                                        let uu____19625 =
                                          let uu____19626 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ)) in
                                          FStar_Pervasives_Native.snd
                                            uu____19626 in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____19612;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____19613;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____19625
                                        }) ed.FStar_Syntax_Syntax.actions in
                                 {
                                   FStar_Syntax_Syntax.cattributes =
                                     cattributes;
                                   FStar_Syntax_Syntax.mname = mname;
                                   FStar_Syntax_Syntax.univs =
                                     (ed.FStar_Syntax_Syntax.univs);
                                   FStar_Syntax_Syntax.binders = binders1;
                                   FStar_Syntax_Syntax.signature =
                                     uu____19568;
                                   FStar_Syntax_Syntax.ret_wp = uu____19580;
                                   FStar_Syntax_Syntax.bind_wp = uu____19581;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____19582;
                                   FStar_Syntax_Syntax.ite_wp = uu____19583;
                                   FStar_Syntax_Syntax.stronger = uu____19584;
                                   FStar_Syntax_Syntax.close_wp = uu____19585;
                                   FStar_Syntax_Syntax.assert_p = uu____19586;
                                   FStar_Syntax_Syntax.assume_p = uu____19587;
                                   FStar_Syntax_Syntax.null_wp = uu____19588;
                                   FStar_Syntax_Syntax.trivial = uu____19589;
                                   FStar_Syntax_Syntax.repr = uu____19590;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____19602;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____19603;
                                   FStar_Syntax_Syntax.actions = uu____19604;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 } in
                               let se =
                                 let for_free =
                                   let uu____19639 =
                                     let uu____19640 =
                                       let uu____19647 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature in
                                       FStar_Pervasives_Native.fst
                                         uu____19647 in
                                     FStar_List.length uu____19640 in
                                   uu____19639 = (Prims.parse_int "1") in
                                 let uu____19676 =
                                   let uu____19679 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname) in
                                   FStar_List.collect uu____19679 quals in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (if for_free
                                      then
                                        FStar_Syntax_Syntax.Sig_new_effect_for_free
                                          ed1
                                      else
                                        FStar_Syntax_Syntax.Sig_new_effect
                                          ed1);
                                   FStar_Syntax_Syntax.sigrng =
                                     (d.FStar_Parser_AST.drange);
                                   FStar_Syntax_Syntax.sigquals = uu____19676;
                                   FStar_Syntax_Syntax.sigmeta =
                                     FStar_Syntax_Syntax.default_sigmeta;
                                   FStar_Syntax_Syntax.sigattrs = []
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
                                             let uu____19701 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____19701 in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4) in
                               let env6 =
                                 let uu____19703 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable) in
                                 if uu____19703
                                 then
                                   let reflect_lid =
                                     FStar_All.pipe_right
                                       (FStar_Ident.id_of_text "reflect")
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
                                       FStar_Syntax_Syntax.sigattrs = []
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
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun d ->
    let uu____19718 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc in
    match uu____19718 with
    | (text, kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.strcat "  " (Prims.strcat s "\n") in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____19769 ->
              let uu____19770 =
                let uu____19771 =
                  FStar_Parser_ToDocument.signature_to_document d in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____19771 in
              Prims.strcat "\n  " uu____19770
          | uu____19772 -> "" in
        let other =
          FStar_List.filter_map
            (fun uu____19785 ->
               match uu____19785 with
               | (k, v1) ->
                   if (k <> "summary") && (k <> "type")
                   then
                     FStar_Pervasives_Native.Some
                       (Prims.strcat k (Prims.strcat ": " v1))
                   else FStar_Pervasives_Native.None) kv in
        let other1 =
          if other <> []
          then Prims.strcat (FStar_String.concat "\n" other) "\n"
          else "" in
        let str =
          Prims.strcat summary (Prims.strcat pp (Prims.strcat other1 text)) in
        let fv =
          let uu____19803 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment" in
          FStar_Syntax_Syntax.fvar uu____19803
            FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
        let arg = FStar_Syntax_Util.exp_string str in
        let uu____19805 =
          let uu____19814 = FStar_Syntax_Syntax.as_arg arg in [uu____19814] in
        FStar_Syntax_Util.mk_app fv uu____19805
and (desugar_decl :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t, FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun d ->
      let uu____19821 = desugar_decl_noattrs env d in
      match uu____19821 with
      | (env1, sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs in
          let attrs1 = FStar_List.map (desugar_term env1) attrs in
          let attrs2 =
            let uu____19841 = mk_comment_attr d in uu____19841 :: attrs1 in
          let s =
            FStar_List.fold_left
              (fun s ->
                 fun a ->
                   let uu____19852 =
                     let uu____19853 = FStar_Syntax_Print.term_to_string a in
                     Prims.strcat "; " uu____19853 in
                   Prims.strcat s uu____19852) "" attrs2 in
          let uu____19854 =
            FStar_List.map
              (fun sigelt ->
                 let uu___133_19860 = sigelt in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___133_19860.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___133_19860.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___133_19860.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___133_19860.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs = attrs2
                 }) sigelts in
          (env1, uu____19854)
and (desugar_decl_noattrs :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t, FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun d ->
      let trans_qual1 = trans_qual d.FStar_Parser_AST.drange in
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Pragma p ->
          let se =
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_pragma (trans_pragma p));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = [];
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            } in
          (if p = FStar_Parser_AST.LightOff
           then FStar_Options.set_ml_ish ()
           else ();
           (env, [se]))
      | FStar_Parser_AST.Fsdoc uu____19888 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x, l) ->
          let uu____19904 = FStar_Syntax_DsEnv.push_module_abbrev env x l in
          (uu____19904, [])
      | FStar_Parser_AST.Tycon (is_effect, tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals in
          let tcs1 =
            FStar_List.map
              (fun uu____19943 ->
                 match uu____19943 with | (x, uu____19951) -> x) tcs in
          let uu____19956 =
            FStar_List.collect (trans_qual1 FStar_Pervasives_Native.None)
              quals in
          desugar_tycon env d uu____19956 tcs1
      | FStar_Parser_AST.TopLevelLet (isrec, lets) ->
          let quals = d.FStar_Parser_AST.quals in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____19978;
                    FStar_Parser_AST.prange = uu____19979;_},
                  uu____19980)::[] -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____19989;
                    FStar_Parser_AST.prange = uu____19990;_},
                  uu____19991)::[] -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____20006;
                         FStar_Parser_AST.prange = uu____20007;_},
                       uu____20008);
                    FStar_Parser_AST.prange = uu____20009;_},
                  uu____20010)::[] -> false
               | (p, uu____20038)::[] ->
                   let uu____20047 = is_app_pattern p in
                   Prims.op_Negation uu____20047
               | uu____20048 -> false) in
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
            let uu____20121 = desugar_term_maybe_top true env as_inner_let in
            (match uu____20121 with
             | (ds_lets, aq) ->
                 (check_no_aq aq;
                  (let uu____20133 =
                     let uu____20134 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets in
                     uu____20134.FStar_Syntax_Syntax.n in
                   match uu____20133 with
                   | FStar_Syntax_Syntax.Tm_let (lbs, uu____20142) ->
                       let fvs =
                         FStar_All.pipe_right
                           (FStar_Pervasives_Native.snd lbs)
                           (FStar_List.map
                              (fun lb ->
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname)) in
                       let quals1 =
                         match quals with
                         | uu____20175::uu____20176 ->
                             FStar_List.collect
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____20179 ->
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.collect
                                  (fun uu___107_20194 ->
                                     match uu___107_20194 with
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inl uu____20197;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____20198;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____20199;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____20200;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____20201;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____20202;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____20203;_}
                                         -> []
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____20215;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____20216;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____20217;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____20218;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____20219;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____20220;_}
                                         ->
                                         FStar_Syntax_DsEnv.lookup_letbinding_quals
                                           env
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                       let lbs1 =
                         let uu____20238 =
                           FStar_All.pipe_right quals1
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract) in
                         if uu____20238
                         then
                           let uu____20247 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname in
                                     let uu___134_20261 = lb in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___135_20263 = fv in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___135_20263.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___135_20263.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___134_20261.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___134_20261.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___134_20261.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___134_20261.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___134_20261.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___134_20261.FStar_Syntax_Syntax.lbpos)
                                     })) in
                           ((FStar_Pervasives_Native.fst lbs), uu____20247)
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
                           FStar_Syntax_Syntax.sigquals = quals1;
                           FStar_Syntax_Syntax.sigmeta =
                             FStar_Syntax_Syntax.default_sigmeta;
                           FStar_Syntax_Syntax.sigattrs = attrs
                         } in
                       let env1 = FStar_Syntax_DsEnv.push_sigelt env s in
                       let env2 =
                         FStar_List.fold_left
                           (fun env2 ->
                              fun id1 ->
                                FStar_Syntax_DsEnv.push_doc env2 id1
                                  d.FStar_Parser_AST.doc) env1 names1 in
                       (env2, [s])
                   | uu____20298 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____20304 =
               match lets with
               | (pat, body)::[] -> (pat, body)
               | uu____20323 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets" in
             match uu____20304 with
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
                       let uu___136_20359 = pat1 in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___136_20359.FStar_Parser_AST.prange)
                       }
                   | uu____20366 -> var_pat in
                 let main_let =
                   desugar_decl env
                     (let uu___137_20373 = d in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___137_20373.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___137_20373.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___137_20373.FStar_Parser_AST.attrs)
                      }) in
                 let build_projection uu____20405 id1 =
                   match uu____20405 with
                   | (env1, ses) ->
                       let main =
                         let uu____20426 =
                           let uu____20427 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name] in
                           FStar_Parser_AST.Var uu____20427 in
                         FStar_Parser_AST.mk_term uu____20426
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
                       let uu____20477 = desugar_decl env1 id_decl in
                       (match uu____20477 with
                        | (env2, ses') ->
                            (env2, (FStar_List.append ses ses'))) in
                 let bvs =
                   let uu____20495 = gather_pattern_bound_vars pat in
                   FStar_All.pipe_right uu____20495 FStar_Util.set_elements in
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
              FStar_Syntax_Syntax.sigattrs = []
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
               FStar_Syntax_Syntax.sigattrs = []
             }])
      | FStar_Parser_AST.Val (id1, t) ->
          let quals = d.FStar_Parser_AST.quals in
          let t1 =
            let uu____20526 = close_fun env t in desugar_term env uu____20526 in
          let quals1 =
            let uu____20530 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env) in
            if uu____20530
            then FStar_Parser_AST.Assumption :: quals
            else quals in
          let lid = FStar_Syntax_DsEnv.qualify env id1 in
          let se =
            let uu____20536 =
              FStar_List.collect (trans_qual1 FStar_Pervasives_Native.None)
                quals1 in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____20536;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            } in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se in
          let env2 =
            FStar_Syntax_DsEnv.push_doc env1 lid d.FStar_Parser_AST.doc in
          (env2, [se])
      | FStar_Parser_AST.Exception (id1, FStar_Pervasives_Native.None) ->
          let uu____20548 =
            FStar_Syntax_DsEnv.fail_or env
              (FStar_Syntax_DsEnv.try_lookup_lid env)
              FStar_Parser_Const.exn_lid in
          (match uu____20548 with
           | (t, uu____20562) ->
               let l = FStar_Syntax_DsEnv.qualify env id1 in
               let qual = [FStar_Syntax_Syntax.ExceptionConstructor] in
               let se =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_datacon
                        (l, [], t, FStar_Parser_Const.exn_lid,
                          (Prims.parse_int "0"),
                          [FStar_Parser_Const.exn_lid]));
                   FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                   FStar_Syntax_Syntax.sigquals = qual;
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 } in
               let se' =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_bundle ([se], [l]));
                   FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                   FStar_Syntax_Syntax.sigquals = qual;
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 } in
               let env1 = FStar_Syntax_DsEnv.push_sigelt env se' in
               let env2 =
                 FStar_Syntax_DsEnv.push_doc env1 l d.FStar_Parser_AST.doc in
               let data_ops = mk_data_projector_names [] env2 se in
               let discs = mk_data_discriminators [] env2 [l] in
               let env3 =
                 FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt env2
                   (FStar_List.append discs data_ops) in
               (env3, (FStar_List.append (se' :: discs) data_ops)))
      | FStar_Parser_AST.Exception (id1, FStar_Pervasives_Native.Some term)
          ->
          let t = desugar_term env term in
          let t1 =
            let uu____20596 =
              let uu____20603 = FStar_Syntax_Syntax.null_binder t in
              [uu____20603] in
            let uu____20604 =
              let uu____20607 =
                let uu____20608 =
                  FStar_Syntax_DsEnv.fail_or env
                    (FStar_Syntax_DsEnv.try_lookup_lid env)
                    FStar_Parser_Const.exn_lid in
                FStar_Pervasives_Native.fst uu____20608 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____20607 in
            FStar_Syntax_Util.arrow uu____20596 uu____20604 in
          let l = FStar_Syntax_DsEnv.qualify env id1 in
          let qual = [FStar_Syntax_Syntax.ExceptionConstructor] in
          let se =
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_datacon
                   (l, [], t1, FStar_Parser_Const.exn_lid,
                     (Prims.parse_int "0"), [FStar_Parser_Const.exn_lid]));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = qual;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            } in
          let se' =
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_bundle ([se], [l]));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = qual;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
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
          desugar_effect env d quals eff_name eff_binders eff_typ eff_decls
            attrs
      | FStar_Parser_AST.SubEffect l ->
          let lookup1 l1 =
            let uu____20671 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1 in
            match uu____20671 with
            | FStar_Pervasives_Native.None ->
                let uu____20674 =
                  let uu____20679 =
                    let uu____20680 =
                      let uu____20681 = FStar_Syntax_Print.lid_to_string l1 in
                      Prims.strcat uu____20681 " not found" in
                    Prims.strcat "Effect name " uu____20680 in
                  (FStar_Errors.Fatal_EffectNotFound, uu____20679) in
                FStar_Errors.raise_error uu____20674
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2 in
          let src = lookup1 l.FStar_Parser_AST.msource in
          let dst = lookup1 l.FStar_Parser_AST.mdest in
          let uu____20685 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____20727 =
                  let uu____20736 =
                    let uu____20743 = desugar_term env t in ([], uu____20743) in
                  FStar_Pervasives_Native.Some uu____20736 in
                (uu____20727, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp, t) ->
                let uu____20776 =
                  let uu____20785 =
                    let uu____20792 = desugar_term env wp in
                    ([], uu____20792) in
                  FStar_Pervasives_Native.Some uu____20785 in
                let uu____20801 =
                  let uu____20810 =
                    let uu____20817 = desugar_term env t in ([], uu____20817) in
                  FStar_Pervasives_Native.Some uu____20810 in
                (uu____20776, uu____20801)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____20843 =
                  let uu____20852 =
                    let uu____20859 = desugar_term env t in ([], uu____20859) in
                  FStar_Pervasives_Native.Some uu____20852 in
                (FStar_Pervasives_Native.None, uu____20843) in
          (match uu____20685 with
           | (lift_wp, lift) ->
               let se =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_sub_effect
                        {
                          FStar_Syntax_Syntax.source = src;
                          FStar_Syntax_Syntax.target = dst;
                          FStar_Syntax_Syntax.lift_wp = lift_wp;
                          FStar_Syntax_Syntax.lift = lift
                        });
                   FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                   FStar_Syntax_Syntax.sigquals = [];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 } in
               (env, [se]))
      | FStar_Parser_AST.Splice t ->
          let t1 = desugar_term env t in
          let se =
            {
              FStar_Syntax_Syntax.sigel = (FStar_Syntax_Syntax.Sig_splice t1);
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = [];
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            } in
          (env, [se])
let (desugar_decls :
  env_t ->
    FStar_Parser_AST.decl Prims.list ->
      (env_t, FStar_Syntax_Syntax.sigelt Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun decls ->
      let uu____20952 =
        FStar_List.fold_left
          (fun uu____20972 ->
             fun d ->
               match uu____20972 with
               | (env1, sigelts) ->
                   let uu____20992 = desugar_decl env1 d in
                   (match uu____20992 with
                    | (env2, se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls in
      match uu____20952 with
      | (env1, sigelts) ->
          let rec forward acc uu___109_21033 =
            match uu___109_21033 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ uu____21047,
                    FStar_Syntax_Syntax.Sig_let uu____21048) ->
                     let uu____21061 =
                       let uu____21064 =
                         let uu___138_21065 = se2 in
                         let uu____21066 =
                           let uu____21069 =
                             FStar_List.filter
                               (fun uu___108_21083 ->
                                  match uu___108_21083 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____21087;
                                           FStar_Syntax_Syntax.vars =
                                             uu____21088;_},
                                         uu____21089);
                                      FStar_Syntax_Syntax.pos = uu____21090;
                                      FStar_Syntax_Syntax.vars = uu____21091;_}
                                      when
                                      let uu____21114 =
                                        let uu____21115 =
                                          FStar_Syntax_Syntax.lid_of_fv fv in
                                        FStar_Ident.string_of_lid uu____21115 in
                                      uu____21114 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____21116 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs in
                           FStar_List.append uu____21069
                             se2.FStar_Syntax_Syntax.sigattrs in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___138_21065.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___138_21065.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___138_21065.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___138_21065.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____21066
                         } in
                       uu____21064 :: se1 :: acc in
                     forward uu____21061 sigelts1
                 | uu____21121 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1 in
          let uu____21129 = forward [] sigelts in (env1, uu____21129)
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
        (env_t, FStar_Syntax_Syntax.modul, Prims.bool)
          FStar_Pervasives_Native.tuple3)
  =
  fun curmod ->
    fun env ->
      fun m ->
        let env1 =
          match (curmod, m) with
          | (FStar_Pervasives_Native.None, uu____21180) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____21184;
               FStar_Syntax_Syntax.exports = uu____21185;
               FStar_Syntax_Syntax.is_interface = uu____21186;_},
             FStar_Parser_AST.Module (current_lid, uu____21188)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod, uu____21196) ->
              let uu____21199 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod in
              FStar_Pervasives_Native.fst uu____21199 in
        let uu____21204 =
          match m with
          | FStar_Parser_AST.Interface (mname, decls, admitted) ->
              let uu____21240 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii in
              (uu____21240, mname, decls, true)
          | FStar_Parser_AST.Module (mname, decls) ->
              let uu____21257 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii in
              (uu____21257, mname, decls, false) in
        match uu____21204 with
        | ((env2, pop_when_done), mname, decls, intf) ->
            let uu____21287 = desugar_decls env2 decls in
            (match uu____21287 with
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
    env_t ->
      FStar_Parser_AST.modul ->
        (env_t, FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2)
  =
  fun curmod ->
    fun env ->
      fun m ->
        let m1 =
          let uu____21341 =
            (FStar_Options.interactive ()) &&
              (let uu____21343 =
                 let uu____21344 =
                   let uu____21345 = FStar_Options.file_list () in
                   FStar_List.hd uu____21345 in
                 FStar_Util.get_file_extension uu____21344 in
               FStar_List.mem uu____21343 ["fsti"; "fsi"]) in
          if uu____21341 then as_interface m else m in
        let uu____21349 = desugar_modul_common curmod env m1 in
        match uu____21349 with
        | (x, y, pop_when_done) ->
            (if pop_when_done
             then (let uu____21364 = FStar_Syntax_DsEnv.pop () in ())
             else ();
             (x, y))
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul ->
      (env_t, FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun m ->
      let uu____21380 =
        desugar_modul_common FStar_Pervasives_Native.None env m in
      match uu____21380 with
      | (env1, modul, pop_when_done) ->
          let uu____21394 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul in
          (match uu____21394 with
           | (env2, modul1) ->
               ((let uu____21406 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str in
                 if uu____21406
                 then
                   let uu____21407 =
                     FStar_Syntax_Print.modul_to_string modul1 in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____21407
                 else ());
                (let uu____21409 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2 in
                 (uu____21409, modul1))))
let (ast_modul_to_modul :
  FStar_Parser_AST.modul ->
    FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul ->
    fun env ->
      let uu____21423 = desugar_modul env modul in
      match uu____21423 with | (env1, modul1) -> (modul1, env1)
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls ->
    fun env ->
      let uu____21450 = desugar_decls env decls in
      match uu____21450 with | (env1, sigelts) -> (sigelts, env1)
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul ->
    fun a_modul ->
      fun env ->
        let uu____21488 = desugar_partial_modul modul env a_modul in
        match uu____21488 with | (env1, modul1) -> (modul1, env1)
let (add_modul_to_env :
  FStar_Syntax_Syntax.modul ->
    FStar_Syntax_DsEnv.module_inclusion_info ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        Prims.unit FStar_Syntax_DsEnv.withenv)
  =
  fun m ->
    fun mii ->
      fun erase_univs ->
        fun en ->
          let erase_univs_ed ed =
            let erase_binders bs =
              match bs with
              | [] -> []
              | uu____21562 ->
                  let t =
                    let uu____21570 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange in
                    erase_univs uu____21570 in
                  let uu____21579 =
                    let uu____21580 = FStar_Syntax_Subst.compress t in
                    uu____21580.FStar_Syntax_Syntax.n in
                  (match uu____21579 with
                   | FStar_Syntax_Syntax.Tm_abs
                       (bs1, uu____21590, uu____21591) -> bs1
                   | uu____21612 -> failwith "Impossible") in
            let uu____21619 =
              let uu____21626 = erase_binders ed.FStar_Syntax_Syntax.binders in
              FStar_Syntax_Subst.open_term' uu____21626
                FStar_Syntax_Syntax.t_unit in
            match uu____21619 with
            | (binders, uu____21628, binders_opening) ->
                let erase_term t =
                  let uu____21634 =
                    let uu____21635 =
                      FStar_Syntax_Subst.subst binders_opening t in
                    erase_univs uu____21635 in
                  FStar_Syntax_Subst.close binders uu____21634 in
                let erase_tscheme uu____21651 =
                  match uu____21651 with
                  | (us, t) ->
                      let t1 =
                        let uu____21671 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening in
                        FStar_Syntax_Subst.subst uu____21671 t in
                      let uu____21674 =
                        let uu____21675 = erase_univs t1 in
                        FStar_Syntax_Subst.close binders uu____21675 in
                      ([], uu____21674) in
                let erase_action action =
                  let opening =
                    FStar_Syntax_Subst.shift_subst
                      (FStar_List.length
                         action.FStar_Syntax_Syntax.action_univs)
                      binders_opening in
                  let erased_action_params =
                    match action.FStar_Syntax_Syntax.action_params with
                    | [] -> []
                    | uu____21704 ->
                        let bs =
                          let uu____21712 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params in
                          FStar_All.pipe_left erase_binders uu____21712 in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange in
                        let uu____21742 =
                          let uu____21743 =
                            let uu____21746 =
                              FStar_Syntax_Subst.close binders t in
                            FStar_Syntax_Subst.compress uu____21746 in
                          uu____21743.FStar_Syntax_Syntax.n in
                        (match uu____21742 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1, uu____21754, uu____21755) -> bs1
                         | uu____21776 -> failwith "Impossible") in
                  let erase_term1 t =
                    let uu____21787 =
                      let uu____21788 = FStar_Syntax_Subst.subst opening t in
                      erase_univs uu____21788 in
                    FStar_Syntax_Subst.close binders uu____21787 in
                  let uu___139_21789 = action in
                  let uu____21790 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn in
                  let uu____21791 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___139_21789.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___139_21789.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____21790;
                    FStar_Syntax_Syntax.action_typ = uu____21791
                  } in
                let uu___140_21792 = ed in
                let uu____21793 = FStar_Syntax_Subst.close_binders binders in
                let uu____21794 = erase_term ed.FStar_Syntax_Syntax.signature in
                let uu____21795 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                let uu____21796 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                let uu____21797 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                let uu____21798 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                let uu____21799 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger in
                let uu____21800 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp in
                let uu____21801 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p in
                let uu____21802 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p in
                let uu____21803 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp in
                let uu____21804 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial in
                let uu____21805 = erase_term ed.FStar_Syntax_Syntax.repr in
                let uu____21806 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr in
                let uu____21807 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                let uu____21808 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___140_21792.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___140_21792.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____21793;
                  FStar_Syntax_Syntax.signature = uu____21794;
                  FStar_Syntax_Syntax.ret_wp = uu____21795;
                  FStar_Syntax_Syntax.bind_wp = uu____21796;
                  FStar_Syntax_Syntax.if_then_else = uu____21797;
                  FStar_Syntax_Syntax.ite_wp = uu____21798;
                  FStar_Syntax_Syntax.stronger = uu____21799;
                  FStar_Syntax_Syntax.close_wp = uu____21800;
                  FStar_Syntax_Syntax.assert_p = uu____21801;
                  FStar_Syntax_Syntax.assume_p = uu____21802;
                  FStar_Syntax_Syntax.null_wp = uu____21803;
                  FStar_Syntax_Syntax.trivial = uu____21804;
                  FStar_Syntax_Syntax.repr = uu____21805;
                  FStar_Syntax_Syntax.return_repr = uu____21806;
                  FStar_Syntax_Syntax.bind_repr = uu____21807;
                  FStar_Syntax_Syntax.actions = uu____21808;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___140_21792.FStar_Syntax_Syntax.eff_attrs)
                } in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___141_21820 = se in
                  let uu____21821 =
                    let uu____21822 = erase_univs_ed ed in
                    FStar_Syntax_Syntax.Sig_new_effect uu____21822 in
                  {
                    FStar_Syntax_Syntax.sigel = uu____21821;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___141_21820.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___141_21820.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___141_21820.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___141_21820.FStar_Syntax_Syntax.sigattrs)
                  } in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se' in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___142_21826 = se in
                  let uu____21827 =
                    let uu____21828 = erase_univs_ed ed in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____21828 in
                  {
                    FStar_Syntax_Syntax.sigel = uu____21827;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___142_21826.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___142_21826.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___142_21826.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___142_21826.FStar_Syntax_Syntax.sigattrs)
                  } in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se' in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____21830 -> FStar_Syntax_DsEnv.push_sigelt env se in
          let uu____21831 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii in
          match uu____21831 with
          | (en1, pop_when_done) ->
              let en2 =
                let uu____21843 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name in
                FStar_List.fold_left push_sigelt1 uu____21843
                  m.FStar_Syntax_Syntax.exports in
              let env = FStar_Syntax_DsEnv.finish en2 m in
              let uu____21845 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env in
              ((), uu____21845)