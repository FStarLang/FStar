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
  fun uu___85_66 ->
    match uu___85_66 with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit) ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality) ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
    | uu____71 -> FStar_Pervasives_Native.None
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
        | uu____98 ->
            let uu____99 =
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
            [uu____99]
let (trans_pragma : FStar_Parser_AST.pragma -> FStar_Syntax_Syntax.pragma) =
  fun uu___86_106 ->
    match uu___86_106 with
    | FStar_Parser_AST.SetOptions s -> FStar_Syntax_Syntax.SetOptions s
    | FStar_Parser_AST.ResetOptions sopt ->
        FStar_Syntax_Syntax.ResetOptions sopt
    | FStar_Parser_AST.LightOff -> FStar_Syntax_Syntax.LightOff
let (as_imp :
  FStar_Parser_AST.imp ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
  =
  fun uu___87_117 ->
    match uu___87_117 with
    | FStar_Parser_AST.Hash ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | uu____120 -> FStar_Pervasives_Native.None
let arg_withimp_e :
  'Auu____127 .
    FStar_Parser_AST.imp ->
      'Auu____127 ->
        ('Auu____127,
          FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2
  = fun imp -> fun t -> (t, (as_imp imp))
let arg_withimp_t :
  'Auu____152 .
    FStar_Parser_AST.imp ->
      'Auu____152 ->
        ('Auu____152,
          FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2
  =
  fun imp ->
    fun t ->
      match imp with
      | FStar_Parser_AST.Hash ->
          (t, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag))
      | uu____171 -> (t, FStar_Pervasives_Native.None)
let (contains_binder : FStar_Parser_AST.binder Prims.list -> Prims.bool) =
  fun binders ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____188 -> true
            | uu____193 -> false))
let rec (unparen : FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun t ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____200 -> t
let (tm_type_z : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r ->
    let uu____206 =
      let uu____207 = FStar_Ident.lid_of_path ["Type0"] r in
      FStar_Parser_AST.Name uu____207 in
    FStar_Parser_AST.mk_term uu____206 r FStar_Parser_AST.Kind
let (tm_type : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r ->
    let uu____213 =
      let uu____214 = FStar_Ident.lid_of_path ["Type"] r in
      FStar_Parser_AST.Name uu____214 in
    FStar_Parser_AST.mk_term uu____213 r FStar_Parser_AST.Kind
let rec (is_comp_type :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun env ->
    fun t ->
      let uu____225 =
        let uu____226 = unparen t in uu____226.FStar_Parser_AST.tm in
      match uu____225 with
      | FStar_Parser_AST.Name l ->
          let uu____228 = FStar_Syntax_DsEnv.try_lookup_effect_name env l in
          FStar_All.pipe_right uu____228 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l, uu____234) ->
          let uu____247 = FStar_Syntax_DsEnv.try_lookup_effect_name env l in
          FStar_All.pipe_right uu____247 FStar_Option.isSome
      | FStar_Parser_AST.App (head1, uu____253, uu____254) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1, uu____257, uu____258) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____263, t1) -> is_comp_type env t1
      | uu____265 -> false
let (unit_ty : FStar_Parser_AST.term) =
  FStar_Parser_AST.mk_term
    (FStar_Parser_AST.Name FStar_Parser_Const.unit_lid)
    FStar_Range.dummyRange FStar_Parser_AST.Type_level
let (compile_op_lid :
  Prims.int -> Prims.string -> FStar_Range.range -> FStar_Ident.lident) =
  fun n1 ->
    fun s ->
      fun r ->
        let uu____281 =
          let uu____284 =
            let uu____285 =
              let uu____290 = FStar_Parser_AST.compile_op n1 s r in
              (uu____290, r) in
            FStar_Ident.mk_ident uu____285 in
          [uu____284] in
        FStar_All.pipe_right uu____281 FStar_Ident.lid_of_ids
let op_as_term :
  'Auu____303 .
    FStar_Syntax_DsEnv.env ->
      Prims.int ->
        'Auu____303 ->
          FStar_Ident.ident ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env ->
    fun arity ->
      fun rng ->
        fun op ->
          let r l dd =
            let uu____339 =
              let uu____340 =
                let uu____341 =
                  FStar_Ident.set_lid_range l op.FStar_Ident.idRange in
                FStar_Syntax_Syntax.lid_as_fv uu____341 dd
                  FStar_Pervasives_Native.None in
              FStar_All.pipe_right uu____340 FStar_Syntax_Syntax.fv_to_tm in
            FStar_Pervasives_Native.Some uu____339 in
          let fallback uu____349 =
            let uu____350 = FStar_Ident.text_of_id op in
            match uu____350 with
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
                let uu____353 = FStar_Options.ml_ish () in
                if uu____353
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
            | uu____357 -> FStar_Pervasives_Native.None in
          let uu____358 =
            let uu____365 =
              compile_op_lid arity op.FStar_Ident.idText
                op.FStar_Ident.idRange in
            FStar_Syntax_DsEnv.try_lookup_lid env uu____365 in
          match uu____358 with
          | FStar_Pervasives_Native.Some t ->
              FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst t)
          | uu____377 -> fallback ()
let (sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list)
  =
  fun ftv ->
    let uu____395 =
      FStar_Util.remove_dups
        (fun x -> fun y -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x ->
            fun y ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____395
let rec (free_type_vars_b :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Syntax_DsEnv.env, FStar_Ident.ident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun binder ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____442 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____446 = FStar_Syntax_DsEnv.push_bv env x in
          (match uu____446 with | (env1, uu____458) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____461, term) ->
          let uu____463 = free_type_vars env term in (env, uu____463)
      | FStar_Parser_AST.TAnnotated (id1, uu____469) ->
          let uu____470 = FStar_Syntax_DsEnv.push_bv env id1 in
          (match uu____470 with | (env1, uu____482) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____486 = free_type_vars env t in (env, uu____486)
and (free_type_vars :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list)
  =
  fun env ->
    fun t ->
      let uu____493 =
        let uu____494 = unparen t in uu____494.FStar_Parser_AST.tm in
      match uu____493 with
      | FStar_Parser_AST.Labeled uu____497 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____507 = FStar_Syntax_DsEnv.try_lookup_id env a in
          (match uu____507 with
           | FStar_Pervasives_Native.None -> [a]
           | uu____520 -> [])
      | FStar_Parser_AST.Wild -> []
      | FStar_Parser_AST.Const uu____527 -> []
      | FStar_Parser_AST.Uvar uu____528 -> []
      | FStar_Parser_AST.Var uu____529 -> []
      | FStar_Parser_AST.Projector uu____530 -> []
      | FStar_Parser_AST.Discrim uu____535 -> []
      | FStar_Parser_AST.Name uu____536 -> []
      | FStar_Parser_AST.Requires (t1, uu____538) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1, uu____544) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____549, t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1, t', tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None -> []
             | FStar_Pervasives_Native.Some t2 -> [t2]) in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____567, ts) ->
          FStar_List.collect
            (fun uu____588 ->
               match uu____588 with
               | (t1, uu____596) -> free_type_vars env t1) ts
      | FStar_Parser_AST.Op (uu____597, ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1, t2, uu____605) ->
          let uu____606 = free_type_vars env t1 in
          let uu____609 = free_type_vars env t2 in
          FStar_List.append uu____606 uu____609
      | FStar_Parser_AST.Refine (b, t1) ->
          let uu____614 = free_type_vars_b env b in
          (match uu____614 with
           | (env1, f) ->
               let uu____629 = free_type_vars env1 t1 in
               FStar_List.append f uu____629)
      | FStar_Parser_AST.Product (binders, body) ->
          let uu____638 =
            FStar_List.fold_left
              (fun uu____658 ->
                 fun binder ->
                   match uu____658 with
                   | (env1, free) ->
                       let uu____678 = free_type_vars_b env1 binder in
                       (match uu____678 with
                        | (env2, f) -> (env2, (FStar_List.append f free))))
              (env, []) binders in
          (match uu____638 with
           | (env1, free) ->
               let uu____709 = free_type_vars env1 body in
               FStar_List.append free uu____709)
      | FStar_Parser_AST.Sum (binders, body) ->
          let uu____718 =
            FStar_List.fold_left
              (fun uu____738 ->
                 fun binder ->
                   match uu____738 with
                   | (env1, free) ->
                       let uu____758 = free_type_vars_b env1 binder in
                       (match uu____758 with
                        | (env2, f) -> (env2, (FStar_List.append f free))))
              (env, []) binders in
          (match uu____718 with
           | (env1, free) ->
               let uu____789 = free_type_vars env1 body in
               FStar_List.append free uu____789)
      | FStar_Parser_AST.Project (t1, uu____793) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.Abs uu____797 -> []
      | FStar_Parser_AST.Let uu____804 -> []
      | FStar_Parser_AST.LetOpen uu____825 -> []
      | FStar_Parser_AST.If uu____830 -> []
      | FStar_Parser_AST.QForall uu____837 -> []
      | FStar_Parser_AST.QExists uu____850 -> []
      | FStar_Parser_AST.Record uu____863 -> []
      | FStar_Parser_AST.Match uu____876 -> []
      | FStar_Parser_AST.TryWith uu____891 -> []
      | FStar_Parser_AST.Bind uu____906 -> []
      | FStar_Parser_AST.Quote uu____913 -> []
      | FStar_Parser_AST.VQuote uu____918 -> []
      | FStar_Parser_AST.Antiquote uu____919 -> []
      | FStar_Parser_AST.Seq uu____924 -> []
let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term,
      (FStar_Parser_AST.term, FStar_Parser_AST.imp)
        FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun t ->
    let rec aux args t1 =
      let uu____977 =
        let uu____978 = unparen t1 in uu____978.FStar_Parser_AST.tm in
      match uu____977 with
      | FStar_Parser_AST.App (t2, arg, imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l, args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____1020 -> (t1, args) in
    aux [] t
let (close :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env ->
    fun t ->
      let ftv =
        let uu____1044 = free_type_vars env t in
        FStar_All.pipe_left sort_ftv uu____1044 in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x ->
                   let uu____1062 =
                     let uu____1063 =
                       let uu____1068 = tm_type x.FStar_Ident.idRange in
                       (x, uu____1068) in
                     FStar_Parser_AST.TAnnotated uu____1063 in
                   FStar_Parser_AST.mk_binder uu____1062
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
        let uu____1085 = free_type_vars env t in
        FStar_All.pipe_left sort_ftv uu____1085 in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x ->
                   let uu____1103 =
                     let uu____1104 =
                       let uu____1109 = tm_type x.FStar_Ident.idRange in
                       (x, uu____1109) in
                     FStar_Parser_AST.TAnnotated uu____1104 in
                   FStar_Parser_AST.mk_binder uu____1103
                     x.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit))) in
         let t1 =
           let uu____1111 =
             let uu____1112 = unparen t in uu____1112.FStar_Parser_AST.tm in
           match uu____1111 with
           | FStar_Parser_AST.Product uu____1113 -> t
           | uu____1120 ->
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
      | uu____1156 -> (bs, t)
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild -> true
    | FStar_Parser_AST.PatTvar (uu____1164, uu____1165) -> true
    | FStar_Parser_AST.PatVar (uu____1170, uu____1171) -> true
    | FStar_Parser_AST.PatAscribed (p1, uu____1177) -> is_var_pattern p1
    | uu____1190 -> false
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1, uu____1197) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____1210;
           FStar_Parser_AST.prange = uu____1211;_},
         uu____1212)
        -> true
    | uu____1223 -> false
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
    | uu____1237 -> p
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
            let uu____1307 = destruct_app_pattern env is_top_level1 p1 in
            (match uu____1307 with
             | (name, args, uu____1350) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1, uu____1400);
               FStar_Parser_AST.prange = uu____1401;_},
             args)
            when is_top_level1 ->
            let uu____1411 =
              let uu____1416 = FStar_Syntax_DsEnv.qualify env id1 in
              FStar_Util.Inr uu____1416 in
            (uu____1411, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1, uu____1438);
               FStar_Parser_AST.prange = uu____1439;_},
             args)
            -> ((FStar_Util.Inl id1), args, FStar_Pervasives_Native.None)
        | uu____1469 -> failwith "Not an app pattern"
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
      | FStar_Parser_AST.PatConst uu____1519 -> acc
      | FStar_Parser_AST.PatVar
          (uu____1520, FStar_Pervasives_Native.Some
           (FStar_Parser_AST.Implicit))
          -> acc
      | FStar_Parser_AST.PatName uu____1523 -> acc
      | FStar_Parser_AST.PatTvar uu____1524 -> acc
      | FStar_Parser_AST.PatOp uu____1531 -> acc
      | FStar_Parser_AST.PatApp (phead, pats) ->
          gather_pattern_bound_vars_from_list (phead :: pats)
      | FStar_Parser_AST.PatVar (x, uu____1539) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatTuple (pats, uu____1548) ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu____1563 =
            FStar_List.map FStar_Pervasives_Native.snd guarded_pats in
          gather_pattern_bound_vars_from_list uu____1563
      | FStar_Parser_AST.PatAscribed (pat, uu____1571) ->
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
    match projectee with | LocalBinder _0 -> true | uu____1633 -> false
let (__proj__LocalBinder__item___0 :
  bnd ->
    (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2)
  = fun projectee -> match projectee with | LocalBinder _0 -> _0
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee ->
    match projectee with | LetBinder _0 -> true | uu____1669 -> false
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
  fun uu___88_1715 ->
    match uu___88_1715 with
    | LocalBinder (a, aq) -> (a, aq)
    | uu____1722 -> failwith "Impossible"
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
      fun uu___89_1753 ->
        match uu___89_1753 with
        | (FStar_Pervasives_Native.None, k) ->
            let uu____1769 = FStar_Syntax_Syntax.null_binder k in
            (uu____1769, env)
        | (FStar_Pervasives_Native.Some a, k) ->
            let uu____1774 = FStar_Syntax_DsEnv.push_bv env a in
            (match uu____1774 with
             | (env1, a1) ->
                 (((let uu___112_1794 = a1 in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___112_1794.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___112_1794.FStar_Syntax_Syntax.index);
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
  fun uu____1823 ->
    match uu____1823 with
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
      let uu____1897 =
        let uu____1912 =
          let uu____1913 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
          FStar_Syntax_Syntax.fv_to_tm uu____1913 in
        let uu____1914 =
          let uu____1923 =
            let uu____1930 = FStar_Syntax_Syntax.as_implicit false in
            (tm, uu____1930) in
          [uu____1923] in
        (uu____1912, uu____1914) in
      FStar_Syntax_Syntax.Tm_app uu____1897 in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm ->
    let tm' =
      let uu____1965 =
        let uu____1980 =
          let uu____1981 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
          FStar_Syntax_Syntax.fv_to_tm uu____1981 in
        let uu____1982 =
          let uu____1991 =
            let uu____1998 = FStar_Syntax_Syntax.as_implicit false in
            (tm, uu____1998) in
          [uu____1991] in
        (uu____1980, uu____1982) in
      FStar_Syntax_Syntax.Tm_app uu____1965 in
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
          let uu____2047 =
            let uu____2062 =
              let uu____2063 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None in
              FStar_Syntax_Syntax.fv_to_tm uu____2063 in
            let uu____2064 =
              let uu____2073 =
                let uu____2080 = FStar_Syntax_Syntax.as_implicit false in
                (t1, uu____2080) in
              let uu____2083 =
                let uu____2092 =
                  let uu____2099 = FStar_Syntax_Syntax.as_implicit false in
                  (t2, uu____2099) in
                [uu____2092] in
              uu____2073 :: uu____2083 in
            (uu____2062, uu____2064) in
          FStar_Syntax_Syntax.Tm_app uu____2047 in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___90_2132 ->
    match uu___90_2132 with
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
    | uu____2133 -> false
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u ->
    fun n1 ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____2145 = sum_to_universe u (n1 - (Prims.parse_int "1")) in
         FStar_Syntax_Syntax.U_succ uu____2145)
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1 -> sum_to_universe FStar_Syntax_Syntax.U_zero n1
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int, FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t ->
    let uu____2164 =
      let uu____2165 = unparen t in uu____2165.FStar_Parser_AST.tm in
    match uu____2164 with
    | FStar_Parser_AST.Wild ->
        let uu____2170 =
          let uu____2171 = FStar_Syntax_Unionfind.univ_fresh () in
          FStar_Syntax_Syntax.U_unif uu____2171 in
        FStar_Util.Inr uu____2170
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr, uu____2182)) ->
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
             let uu____2247 = sum_to_universe u n1 in
             FStar_Util.Inr uu____2247
         | (FStar_Util.Inr u, FStar_Util.Inl n1) ->
             let uu____2258 = sum_to_universe u n1 in
             FStar_Util.Inr uu____2258
         | (FStar_Util.Inr u11, FStar_Util.Inr u21) ->
             let uu____2269 =
               let uu____2274 =
                 let uu____2275 = FStar_Parser_AST.term_to_string t in
                 Prims.strcat
                   "This universe might contain a sum of two universe variables "
                   uu____2275 in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____2274) in
             FStar_Errors.raise_error uu____2269 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____2280 ->
        let rec aux t1 univargs =
          let uu____2314 =
            let uu____2315 = unparen t1 in uu____2315.FStar_Parser_AST.tm in
          match uu____2314 with
          | FStar_Parser_AST.App (t2, targ, uu____2322) ->
              let uarg = desugar_maybe_non_constant_universe targ in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___91_2345 ->
                     match uu___91_2345 with
                     | FStar_Util.Inr uu____2350 -> true
                     | uu____2351 -> false) univargs
              then
                let uu____2356 =
                  let uu____2357 =
                    FStar_List.map
                      (fun uu___92_2366 ->
                         match uu___92_2366 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs in
                  FStar_Syntax_Syntax.U_max uu____2357 in
                FStar_Util.Inr uu____2356
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___93_2383 ->
                        match uu___93_2383 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____2389 -> failwith "impossible")
                     univargs in
                 let uu____2390 =
                   FStar_List.fold_left
                     (fun m -> fun n1 -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs in
                 FStar_Util.Inl uu____2390)
          | uu____2396 ->
              let uu____2397 =
                let uu____2402 =
                  let uu____2403 =
                    let uu____2404 = FStar_Parser_AST.term_to_string t1 in
                    Prims.strcat uu____2404 " in universe context" in
                  Prims.strcat "Unexpected term " uu____2403 in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____2402) in
              FStar_Errors.raise_error uu____2397 t1.FStar_Parser_AST.range in
        aux t []
    | uu____2413 ->
        let uu____2414 =
          let uu____2419 =
            let uu____2420 =
              let uu____2421 = FStar_Parser_AST.term_to_string t in
              Prims.strcat uu____2421 " in universe context" in
            Prims.strcat "Unexpected term " uu____2420 in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____2419) in
        FStar_Errors.raise_error uu____2414 t.FStar_Parser_AST.range
let rec (desugar_universe :
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
    | (bv, b, e)::uu____2454 ->
        let uu____2477 =
          let uu____2482 =
            let uu____2483 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format2 "Unexpected antiquotation: %s(%s)"
              (if b then "`@" else "`#") uu____2483 in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____2482) in
        FStar_Errors.raise_error uu____2477 e.FStar_Syntax_Syntax.pos
let check_fields :
  'Auu____2493 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident, 'Auu____2493) FStar_Pervasives_Native.tuple2
        Prims.list -> FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env ->
    fun fields ->
      fun rg ->
        let uu____2521 = FStar_List.hd fields in
        match uu____2521 with
        | (f, uu____2531) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f in
              let check_field uu____2543 =
                match uu____2543 with
                | (f', uu____2549) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____2551 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record in
                      if uu____2551
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
              (let uu____2555 = FStar_List.tl fields in
               FStar_List.iter check_field uu____2555);
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
            | FStar_Syntax_Syntax.Pat_dot_term uu____2910 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_wild uu____2917 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_constant uu____2918 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_var x ->
                FStar_Util.set_add x FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_cons (uu____2920, pats1) ->
                let aux out uu____2958 =
                  match uu____2958 with
                  | (p2, uu____2970) ->
                      let intersection =
                        let uu____2978 = pat_vars p2 in
                        FStar_Util.set_intersect uu____2978 out in
                      let uu____2981 = FStar_Util.set_is_empty intersection in
                      if uu____2981
                      then
                        let uu____2984 = pat_vars p2 in
                        FStar_Util.set_union out uu____2984
                      else
                        (let duplicate_bv =
                           let uu____2989 =
                             FStar_Util.set_elements intersection in
                           FStar_List.hd uu____2989 in
                         let uu____2992 =
                           let uu____2997 =
                             FStar_Util.format1
                               "Non-linear patterns are not permitted. %s appears more than once in this pattern."
                               (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
                           (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                             uu____2997) in
                         FStar_Errors.raise_error uu____2992 r) in
                FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1 in
          match pats with
          | [] -> ()
          | p1::[] ->
              let uu____3017 = pat_vars p1 in
              FStar_All.pipe_right uu____3017 (fun a239 -> ())
          | p1::ps ->
              let pvars = pat_vars p1 in
              let aux p2 =
                let uu____3039 =
                  let uu____3040 = pat_vars p2 in
                  FStar_Util.set_eq pvars uu____3040 in
                if uu____3039
                then ()
                else
                  (let nonlinear_vars =
                     let uu____3047 = pat_vars p2 in
                     FStar_Util.set_symmetric_difference pvars uu____3047 in
                   let first_nonlinear_var =
                     let uu____3051 = FStar_Util.set_elements nonlinear_vars in
                     FStar_List.hd uu____3051 in
                   let uu____3054 =
                     let uu____3059 =
                       FStar_Util.format1
                         "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                         (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
                     (FStar_Errors.Fatal_IncoherentPatterns, uu____3059) in
                   FStar_Errors.raise_error uu____3054 r) in
              FStar_List.iter aux ps in
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false, uu____3063) -> ()
         | (true, FStar_Parser_AST.PatVar uu____3064) -> ()
         | (true, uu____3071) ->
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_LetMutableForVariablesOnly,
                 "let-mutable is for variables only")
               p.FStar_Parser_AST.prange);
        (let resolvex l e x =
           let uu____3094 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText)) in
           match uu____3094 with
           | FStar_Pervasives_Native.Some y -> (l, e, y)
           | uu____3108 ->
               let uu____3111 =
                 if is_mut
                 then FStar_Syntax_DsEnv.push_bv_mutable e x
                 else FStar_Syntax_DsEnv.push_bv e x in
               (match uu____3111 with | (e1, x1) -> ((x1 :: l), e1, x1)) in
         let rec aux' top loc env1 p1 =
           let pos q =
             FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange in
           let pos_r r q = FStar_Syntax_Syntax.withinfo q r in
           let orig = p1 in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr uu____3223 -> failwith "impossible"
           | FStar_Parser_AST.PatOp op ->
               let uu____3239 =
                 let uu____3240 =
                   let uu____3241 =
                     let uu____3248 =
                       let uu____3249 =
                         let uu____3254 =
                           FStar_Parser_AST.compile_op (Prims.parse_int "0")
                             op.FStar_Ident.idText op.FStar_Ident.idRange in
                         (uu____3254, (op.FStar_Ident.idRange)) in
                       FStar_Ident.mk_ident uu____3249 in
                     (uu____3248, FStar_Pervasives_Native.None) in
                   FStar_Parser_AST.PatVar uu____3241 in
                 {
                   FStar_Parser_AST.pat = uu____3240;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 } in
               aux loc env1 uu____3239
           | FStar_Parser_AST.PatAscribed (p2, (t, tacopt)) ->
               ((match tacopt with
                 | FStar_Pervasives_Native.None -> ()
                 | FStar_Pervasives_Native.Some uu____3271 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                         "Type ascriptions within patterns are cannot be associated with a tactic")
                       orig.FStar_Parser_AST.prange);
                (let uu____3272 = aux loc env1 p2 in
                 match uu____3272 with
                 | (loc1, env', binder, p3, imp) ->
                     let annot_pat_var p4 t1 =
                       match p4.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let uu___113_3330 = p4 in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var
                                  (let uu___114_3335 = x in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___114_3335.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___114_3335.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }));
                             FStar_Syntax_Syntax.p =
                               (uu___113_3330.FStar_Syntax_Syntax.p)
                           }
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let uu___115_3337 = p4 in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild
                                  (let uu___116_3342 = x in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___116_3342.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___116_3342.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }));
                             FStar_Syntax_Syntax.p =
                               (uu___115_3337.FStar_Syntax_Syntax.p)
                           }
                       | uu____3343 when top -> p4
                       | uu____3344 ->
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                               "Type ascriptions within patterns are only allowed on variables")
                             orig.FStar_Parser_AST.prange in
                     let uu____3347 =
                       match binder with
                       | LetBinder uu____3360 -> failwith "impossible"
                       | LocalBinder (x, aq) ->
                           let t1 =
                             let uu____3380 = close_fun env1 t in
                             desugar_term env1 uu____3380 in
                           (if
                              (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                               with
                               | FStar_Syntax_Syntax.Tm_unknown -> false
                               | uu____3382 -> true)
                            then
                              (let uu____3383 =
                                 let uu____3388 =
                                   let uu____3389 =
                                     FStar_Syntax_Print.bv_to_string x in
                                   let uu____3390 =
                                     FStar_Syntax_Print.term_to_string
                                       x.FStar_Syntax_Syntax.sort in
                                   let uu____3391 =
                                     FStar_Syntax_Print.term_to_string t1 in
                                   FStar_Util.format3
                                     "Multiple ascriptions for %s in pattern, type %s was shadowed by %s\n"
                                     uu____3389 uu____3390 uu____3391 in
                                 (FStar_Errors.Warning_MultipleAscriptions,
                                   uu____3388) in
                               FStar_Errors.log_issue
                                 orig.FStar_Parser_AST.prange uu____3383)
                            else ();
                            (let uu____3393 = annot_pat_var p3 t1 in
                             (uu____3393,
                               (LocalBinder
                                  ((let uu___117_3399 = x in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___117_3399.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___117_3399.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    }), aq))))) in
                     (match uu____3347 with
                      | (p4, binder1) -> (loc1, env', binder1, p4, imp))))
           | FStar_Parser_AST.PatWild ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____3421 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x) in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____3421, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____3432 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c) in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____3432, false)
           | FStar_Parser_AST.PatTvar (x, aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit) in
               let aq1 = trans_aqual aq in
               let uu____3453 = resolvex loc env1 x in
               (match uu____3453 with
                | (loc1, env2, xbv) ->
                    let uu____3475 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv) in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____3475, imp))
           | FStar_Parser_AST.PatVar (x, aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit) in
               let aq1 = trans_aqual aq in
               let uu____3496 = resolvex loc env1 x in
               (match uu____3496 with
                | (loc1, env2, xbv) ->
                    let uu____3518 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv) in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____3518, imp))
           | FStar_Parser_AST.PatName l ->
               let l1 =
                 FStar_Syntax_DsEnv.fail_or env1
                   (FStar_Syntax_DsEnv.try_lookup_datacon env1) l in
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun in
               let uu____3530 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, [])) in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____3530, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____3554;_},
                args)
               ->
               let uu____3560 =
                 FStar_List.fold_right
                   (fun arg ->
                      fun uu____3601 ->
                        match uu____3601 with
                        | (loc1, env2, args1) ->
                            let uu____3649 = aux loc1 env2 arg in
                            (match uu____3649 with
                             | (loc2, env3, uu____3678, arg1, imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, []) in
               (match uu____3560 with
                | (loc1, env2, args1) ->
                    let l1 =
                      FStar_Syntax_DsEnv.fail_or env2
                        (FStar_Syntax_DsEnv.try_lookup_datacon env2) l in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun in
                    let uu____3748 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1)) in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)),
                      uu____3748, false))
           | FStar_Parser_AST.PatApp uu____3765 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                 p1.FStar_Parser_AST.prange
           | FStar_Parser_AST.PatList pats ->
               let uu____3787 =
                 FStar_List.fold_right
                   (fun pat ->
                      fun uu____3820 ->
                        match uu____3820 with
                        | (loc1, env2, pats1) ->
                            let uu____3852 = aux loc1 env2 pat in
                            (match uu____3852 with
                             | (loc2, env3, uu____3877, pat1, uu____3879) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, []) in
               (match uu____3787 with
                | (loc1, env2, pats1) ->
                    let pat =
                      let uu____3922 =
                        let uu____3925 =
                          let uu____3932 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange in
                          pos_r uu____3932 in
                        let uu____3933 =
                          let uu____3934 =
                            let uu____3947 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Parser_Const.nil_lid
                                FStar_Syntax_Syntax.Delta_constant
                                (FStar_Pervasives_Native.Some
                                   FStar_Syntax_Syntax.Data_ctor) in
                            (uu____3947, []) in
                          FStar_Syntax_Syntax.Pat_cons uu____3934 in
                        FStar_All.pipe_left uu____3925 uu____3933 in
                      FStar_List.fold_right
                        (fun hd1 ->
                           fun tl1 ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p in
                             let uu____3979 =
                               let uu____3980 =
                                 let uu____3993 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.cons_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Data_ctor) in
                                 (uu____3993, [(hd1, false); (tl1, false)]) in
                               FStar_Syntax_Syntax.Pat_cons uu____3980 in
                             FStar_All.pipe_left (pos_r r) uu____3979) pats1
                        uu____3922 in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)), pat,
                      false))
           | FStar_Parser_AST.PatTuple (args, dep1) ->
               let uu____4037 =
                 FStar_List.fold_left
                   (fun uu____4077 ->
                      fun p2 ->
                        match uu____4077 with
                        | (loc1, env2, pats) ->
                            let uu____4126 = aux loc1 env2 p2 in
                            (match uu____4126 with
                             | (loc2, env3, uu____4155, pat, uu____4157) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args in
               (match uu____4037 with
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
                    let uu____4252 =
                      FStar_Syntax_DsEnv.fail_or env2
                        (FStar_Syntax_DsEnv.try_lookup_lid env2) l in
                    (match uu____4252 with
                     | (constr, uu____4274) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____4277 -> failwith "impossible" in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (FStar_Pervasives_Native.Some
                                (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun in
                         let uu____4279 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2)) in
                         (loc1, env2,
                           (LocalBinder (x, FStar_Pervasives_Native.None)),
                           uu____4279, false)))
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
                      (fun uu____4350 ->
                         match uu____4350 with
                         | (f, p2) -> ((f.FStar_Ident.ident), p2))) in
               let args =
                 FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                   (FStar_List.map
                      (fun uu____4380 ->
                         match uu____4380 with
                         | (f, uu____4386) ->
                             let uu____4387 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____4413 ->
                                       match uu____4413 with
                                       | (g, uu____4419) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText)) in
                             (match uu____4387 with
                              | FStar_Pervasives_Native.None ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
                              | FStar_Pervasives_Native.Some (uu____4424, p2)
                                  -> p2))) in
               let app =
                 let uu____4431 =
                   let uu____4432 =
                     let uu____4439 =
                       let uu____4440 =
                         let uu____4441 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                                [record.FStar_Syntax_DsEnv.constrname]) in
                         FStar_Parser_AST.PatName uu____4441 in
                       FStar_Parser_AST.mk_pattern uu____4440
                         p1.FStar_Parser_AST.prange in
                     (uu____4439, args) in
                   FStar_Parser_AST.PatApp uu____4432 in
                 FStar_Parser_AST.mk_pattern uu____4431
                   p1.FStar_Parser_AST.prange in
               let uu____4444 = aux loc env1 app in
               (match uu____4444 with
                | (env2, e, b, p2, uu____4473) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv, args1) ->
                          let uu____4501 =
                            let uu____4502 =
                              let uu____4515 =
                                let uu___118_4516 = fv in
                                let uu____4517 =
                                  let uu____4520 =
                                    let uu____4521 =
                                      let uu____4528 =
                                        FStar_All.pipe_right
                                          record.FStar_Syntax_DsEnv.fields
                                          (FStar_List.map
                                             FStar_Pervasives_Native.fst) in
                                      ((record.FStar_Syntax_DsEnv.typename),
                                        uu____4528) in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____4521 in
                                  FStar_Pervasives_Native.Some uu____4520 in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___118_4516.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___118_4516.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____4517
                                } in
                              (uu____4515, args1) in
                            FStar_Syntax_Syntax.Pat_cons uu____4502 in
                          FStar_All.pipe_left pos uu____4501
                      | uu____4555 -> p2 in
                    (env2, e, b, p3, false))
         and aux loc env1 p1 = aux' false loc env1 p1 in
         let aux_maybe_or env1 p1 =
           let loc = [] in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____4609 = aux' true loc env1 p2 in
               (match uu____4609 with
                | (loc1, env2, var, p3, uu____4636) ->
                    let uu____4641 =
                      FStar_List.fold_left
                        (fun uu____4673 ->
                           fun p4 ->
                             match uu____4673 with
                             | (loc2, env3, ps1) ->
                                 let uu____4706 = aux' true loc2 env3 p4 in
                                 (match uu____4706 with
                                  | (loc3, env4, uu____4731, p5, uu____4733)
                                      -> (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps in
                    (match uu____4641 with
                     | (loc2, env3, ps1) ->
                         let pats = p3 :: (FStar_List.rev ps1) in
                         (env3, var, pats)))
           | uu____4784 ->
               let uu____4785 = aux' true loc env1 p1 in
               (match uu____4785 with
                | (loc1, env2, vars, pat, b) -> (env2, vars, [pat])) in
         let uu____4825 = aux_maybe_or env p in
         match uu____4825 with
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
            let uu____4886 =
              let uu____4887 =
                let uu____4898 = FStar_Syntax_DsEnv.qualify env x in
                (uu____4898,
                  (FStar_Syntax_Syntax.tun, FStar_Pervasives_Native.None)) in
              LetBinder uu____4887 in
            (env, uu____4886, []) in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____4926 =
                  let uu____4927 =
                    let uu____4932 =
                      FStar_Parser_AST.compile_op (Prims.parse_int "0")
                        x.FStar_Ident.idText x.FStar_Ident.idRange in
                    (uu____4932, (x.FStar_Ident.idRange)) in
                  FStar_Ident.mk_ident uu____4927 in
                mklet uu____4926
            | FStar_Parser_AST.PatVar (x, uu____4934) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x, uu____4940);
                   FStar_Parser_AST.prange = uu____4941;_},
                 (t, tacopt))
                ->
                let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env) in
                let uu____4961 =
                  let uu____4962 =
                    let uu____4973 = FStar_Syntax_DsEnv.qualify env x in
                    let uu____4974 =
                      let uu____4981 = desugar_term env t in
                      (uu____4981, tacopt1) in
                    (uu____4973, uu____4974) in
                  LetBinder uu____4962 in
                (env, uu____4961, [])
            | uu____4992 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_UnexpectedPattern,
                    "Unexpected pattern at the top-level")
                  p.FStar_Parser_AST.prange
          else
            (let uu____5002 = desugar_data_pat env p is_mut in
             match uu____5002 with
             | (env1, binder, p1) ->
                 let p2 =
                   match p1 with
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                         uu____5031;
                       FStar_Syntax_Syntax.p = uu____5032;_}::[] -> []
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                         uu____5037;
                       FStar_Syntax_Syntax.p = uu____5038;_}::[] -> []
                   | uu____5043 -> p1 in
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
  fun uu____5050 ->
    fun env ->
      fun pat ->
        let uu____5053 = desugar_data_pat env pat false in
        match uu____5053 with | (env1, uu____5069, pat1) -> (env1, pat1)
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
      let uu____5088 = desugar_term_aq env e in
      match uu____5088 with | (t, aq) -> (check_no_aq aq; t)
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
      let uu____5105 = desugar_typ_aq env e in
      match uu____5105 with | (t, aq) -> (check_no_aq aq; t)
and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness, FStar_Const.width)
        FStar_Pervasives_Native.tuple2 ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun repr ->
      fun uu____5115 ->
        fun range ->
          match uu____5115 with
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
              ((let uu____5125 =
                  let uu____5126 =
                    FStar_Const.within_bounds repr signedness width in
                  Prims.op_Negation uu____5126 in
                if uu____5125
                then
                  let uu____5127 =
                    let uu____5132 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm in
                    (FStar_Errors.Error_OutOfRange, uu____5132) in
                  FStar_Errors.log_issue range uu____5127
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
                  let uu____5137 = FStar_Ident.path_of_text intro_nm in
                  FStar_Ident.lid_of_path uu____5137 range in
                let lid1 =
                  let uu____5141 = FStar_Syntax_DsEnv.try_lookup_lid env lid in
                  match uu____5141 with
                  | FStar_Pervasives_Native.Some (intro_term, uu____5151) ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____5160 =
                               FStar_Ident.path_of_text private_intro_nm in
                             FStar_Ident.lid_of_path uu____5160 range in
                           let private_fv =
                             let uu____5162 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____5162 fv.FStar_Syntax_Syntax.fv_qual in
                           let uu___119_5163 = intro_term in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___119_5163.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___119_5163.FStar_Syntax_Syntax.vars)
                           }
                       | uu____5164 ->
                           failwith
                             (Prims.strcat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None ->
                      let uu____5171 =
                        let uu____5176 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____5176) in
                      FStar_Errors.raise_error uu____5171 range in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range in
                let uu____5192 =
                  let uu____5199 =
                    let uu____5200 =
                      let uu____5215 =
                        let uu____5224 =
                          let uu____5231 =
                            FStar_Syntax_Syntax.as_implicit false in
                          (repr1, uu____5231) in
                        [uu____5224] in
                      (lid1, uu____5215) in
                    FStar_Syntax_Syntax.Tm_app uu____5200 in
                  FStar_Syntax_Syntax.mk uu____5199 in
                uu____5192 FStar_Pervasives_Native.None range))
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
            let uu____5270 =
              FStar_Syntax_DsEnv.fail_or env
                ((if resolve
                  then FStar_Syntax_DsEnv.try_lookup_lid_with_attributes
                  else
                    FStar_Syntax_DsEnv.try_lookup_lid_with_attributes_no_resolve)
                   env) l in
            match uu____5270 with
            | (tm, mut, attrs) ->
                let warn_if_deprecated attrs1 =
                  FStar_List.iter
                    (fun a ->
                       match a.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_app
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____5319;
                              FStar_Syntax_Syntax.vars = uu____5320;_},
                            args)
                           when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____5343 =
                               FStar_Syntax_Print.term_to_string tm in
                             Prims.strcat uu____5343 " is deprecated" in
                           let msg1 =
                             if
                               (FStar_List.length args) >
                                 (Prims.parse_int "0")
                             then
                               let uu____5351 =
                                 let uu____5352 =
                                   let uu____5355 = FStar_List.hd args in
                                   FStar_Pervasives_Native.fst uu____5355 in
                                 uu____5352.FStar_Syntax_Syntax.n in
                               match uu____5351 with
                               | FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_string (s, uu____5371))
                                   when
                                   Prims.op_Negation
                                     ((FStar_Util.trim_string s) = "")
                                   ->
                                   Prims.strcat msg
                                     (Prims.strcat ", use "
                                        (Prims.strcat s " instead"))
                               | uu____5372 -> msg
                             else msg in
                           let uu____5374 = FStar_Ident.range_of_lid l in
                           FStar_Errors.log_issue uu____5374
                             (FStar_Errors.Warning_DeprecatedDefinition,
                               msg1)
                       | FStar_Syntax_Syntax.Tm_fvar fv when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____5377 =
                               FStar_Syntax_Print.term_to_string tm in
                             Prims.strcat uu____5377 " is deprecated" in
                           let uu____5378 = FStar_Ident.range_of_lid l in
                           FStar_Errors.log_issue uu____5378
                             (FStar_Errors.Warning_DeprecatedDefinition, msg)
                       | uu____5379 -> ()) attrs1 in
                (warn_if_deprecated attrs;
                 (let tm1 = setpos tm in
                  if mut
                  then
                    let uu____5384 =
                      let uu____5385 =
                        let uu____5392 = mk_ref_read tm1 in
                        (uu____5392,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Mutable_rval)) in
                      FStar_Syntax_Syntax.Tm_meta uu____5385 in
                    FStar_All.pipe_left mk1 uu____5384
                  else tm1))
and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun env ->
    fun cattributes ->
      let desugar_attribute t =
        let uu____5410 =
          let uu____5411 = unparen t in uu____5411.FStar_Parser_AST.tm in
        match uu____5410 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____5412; FStar_Ident.ident = uu____5413;
              FStar_Ident.nsstr = uu____5414; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____5417 ->
            let uu____5418 =
              let uu____5423 =
                let uu____5424 = FStar_Parser_AST.term_to_string t in
                Prims.strcat "Unknown attribute " uu____5424 in
              (FStar_Errors.Fatal_UnknownAttribute, uu____5423) in
            FStar_Errors.raise_error uu____5418 t.FStar_Parser_AST.range in
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
          let uu___120_5519 = e in
          {
            FStar_Syntax_Syntax.n = (uu___120_5519.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___120_5519.FStar_Syntax_Syntax.vars)
          } in
        let uu____5522 =
          let uu____5523 = unparen top in uu____5523.FStar_Parser_AST.tm in
        match uu____5522 with
        | FStar_Parser_AST.Wild -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____5540 ->
            let uu____5547 = desugar_formula env top in (uu____5547, noaqs)
        | FStar_Parser_AST.Requires (t, lopt) ->
            let uu____5564 = desugar_formula env t in (uu____5564, noaqs)
        | FStar_Parser_AST.Ensures (t, lopt) ->
            let uu____5581 = desugar_formula env t in (uu____5581, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i, FStar_Pervasives_Native.Some size)) ->
            let uu____5615 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range in
            (uu____5615, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____5627 = mk1 (FStar_Syntax_Syntax.Tm_constant c) in
            (uu____5627, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_}, args)
            ->
            let e =
              let uu____5649 =
                let uu____5650 =
                  let uu____5657 = FStar_Ident.mk_ident ("==", r) in
                  (uu____5657, args) in
                FStar_Parser_AST.Op uu____5650 in
              FStar_Parser_AST.mk_term uu____5649 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level in
            let uu____5660 =
              let uu____5661 =
                let uu____5662 =
                  let uu____5669 = FStar_Ident.mk_ident ("~", r) in
                  (uu____5669, [e]) in
                FStar_Parser_AST.Op uu____5662 in
              FStar_Parser_AST.mk_term uu____5661 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level in
            desugar_term_aq env uu____5660
        | FStar_Parser_AST.Op (op_star, uu____5673::uu____5674::[]) when
            (let uu____5679 = FStar_Ident.text_of_id op_star in
             uu____5679 = "*") &&
              (let uu____5681 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star in
               FStar_All.pipe_right uu____5681 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____5696;_},
                   t1::t2::[])
                  ->
                  let uu____5701 = flatten1 t1 in
                  FStar_List.append uu____5701 [t2]
              | uu____5704 -> [t] in
            let uu____5705 =
              let uu____5714 =
                let uu____5721 =
                  let uu____5724 = unparen top in flatten1 uu____5724 in
                FStar_All.pipe_right uu____5721
                  (FStar_List.map
                     (fun t ->
                        let uu____5743 = desugar_typ_aq env t in
                        match uu____5743 with
                        | (t', aq) ->
                            let uu____5754 = FStar_Syntax_Syntax.as_arg t' in
                            (uu____5754, aq))) in
              FStar_All.pipe_right uu____5714 FStar_List.unzip in
            (match uu____5705 with
             | (targs, aqs) ->
                 let uu____5783 =
                   let uu____5788 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____5788 in
                 (match uu____5783 with
                  | (tup, uu____5798) ->
                      let uu____5799 =
                        mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs)) in
                      (uu____5799, (join_aqs aqs))))
        | FStar_Parser_AST.Tvar a ->
            let uu____5817 =
              let uu____5820 =
                let uu____5823 =
                  FStar_Syntax_DsEnv.fail_or2
                    (FStar_Syntax_DsEnv.try_lookup_id env) a in
                FStar_Pervasives_Native.fst uu____5823 in
              FStar_All.pipe_left setpos uu____5820 in
            (uu____5817, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____5849 =
              let uu____5854 =
                let uu____5855 =
                  let uu____5856 = FStar_Ident.text_of_id u in
                  Prims.strcat uu____5856 " in non-universe context" in
                Prims.strcat "Unexpected universe variable " uu____5855 in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____5854) in
            FStar_Errors.raise_error uu____5849 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s, args) ->
            let uu____5867 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s in
            (match uu____5867 with
             | FStar_Pervasives_Native.None ->
                 let uu____5874 =
                   let uu____5879 =
                     let uu____5880 = FStar_Ident.text_of_id s in
                     Prims.strcat "Unexpected or unbound operator: "
                       uu____5880 in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____5879) in
                 FStar_Errors.raise_error uu____5874
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let uu____5890 =
                     let uu____5905 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t ->
                               let uu____5947 = desugar_term_aq env t in
                               match uu____5947 with
                               | (t', s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1))) in
                     FStar_All.pipe_right uu____5905 FStar_List.unzip in
                   (match uu____5890 with
                    | (args1, aqs) ->
                        let uu____6030 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1)) in
                        (uu____6030, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1, (a, uu____6066)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____6081 =
              let uu___121_6082 = top in
              let uu____6083 =
                let uu____6084 =
                  let uu____6091 =
                    let uu___122_6092 = top in
                    let uu____6093 =
                      let uu____6094 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____6094 in
                    {
                      FStar_Parser_AST.tm = uu____6093;
                      FStar_Parser_AST.range =
                        (uu___122_6092.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___122_6092.FStar_Parser_AST.level)
                    } in
                  (uu____6091, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____6084 in
              {
                FStar_Parser_AST.tm = uu____6083;
                FStar_Parser_AST.range =
                  (uu___121_6082.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___121_6082.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____6081
        | FStar_Parser_AST.Construct (n1, (a, uu____6097)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____6113 =
                let uu___123_6114 = top in
                let uu____6115 =
                  let uu____6116 =
                    let uu____6123 =
                      let uu___124_6124 = top in
                      let uu____6125 =
                        let uu____6126 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range in
                        FStar_Parser_AST.Var uu____6126 in
                      {
                        FStar_Parser_AST.tm = uu____6125;
                        FStar_Parser_AST.range =
                          (uu___124_6124.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___124_6124.FStar_Parser_AST.level)
                      } in
                    (uu____6123, a, FStar_Parser_AST.Nothing) in
                  FStar_Parser_AST.App uu____6116 in
                {
                  FStar_Parser_AST.tm = uu____6115;
                  FStar_Parser_AST.range =
                    (uu___123_6114.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___123_6114.FStar_Parser_AST.level)
                } in
              desugar_term_maybe_top top_level env uu____6113))
        | FStar_Parser_AST.Construct (n1, (a, uu____6129)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____6144 =
              let uu___125_6145 = top in
              let uu____6146 =
                let uu____6147 =
                  let uu____6154 =
                    let uu___126_6155 = top in
                    let uu____6156 =
                      let uu____6157 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range in
                      FStar_Parser_AST.Var uu____6157 in
                    {
                      FStar_Parser_AST.tm = uu____6156;
                      FStar_Parser_AST.range =
                        (uu___126_6155.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___126_6155.FStar_Parser_AST.level)
                    } in
                  (uu____6154, a, FStar_Parser_AST.Nothing) in
                FStar_Parser_AST.App uu____6147 in
              {
                FStar_Parser_AST.tm = uu____6146;
                FStar_Parser_AST.range =
                  (uu___125_6145.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___125_6145.FStar_Parser_AST.level)
              } in
            desugar_term_maybe_top top_level env uu____6144
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____6158; FStar_Ident.ident = uu____6159;
              FStar_Ident.nsstr = uu____6160; FStar_Ident.str = "Type0";_}
            ->
            let uu____6163 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero) in
            (uu____6163, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____6178; FStar_Ident.ident = uu____6179;
              FStar_Ident.nsstr = uu____6180; FStar_Ident.str = "Type";_}
            ->
            let uu____6183 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown) in
            (uu____6183, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____6198; FStar_Ident.ident = uu____6199;
               FStar_Ident.nsstr = uu____6200; FStar_Ident.str = "Type";_},
             (t, FStar_Parser_AST.UnivApp)::[])
            ->
            let uu____6218 =
              let uu____6221 =
                let uu____6222 = desugar_universe t in
                FStar_Syntax_Syntax.Tm_type uu____6222 in
              mk1 uu____6221 in
            (uu____6218, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____6235; FStar_Ident.ident = uu____6236;
              FStar_Ident.nsstr = uu____6237; FStar_Ident.str = "Effect";_}
            ->
            let uu____6240 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect) in
            (uu____6240, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____6255; FStar_Ident.ident = uu____6256;
              FStar_Ident.nsstr = uu____6257; FStar_Ident.str = "True";_}
            ->
            let uu____6260 =
              let uu____6261 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range in
              FStar_Syntax_Syntax.fvar uu____6261
                FStar_Syntax_Syntax.Delta_constant
                FStar_Pervasives_Native.None in
            (uu____6260, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____6272; FStar_Ident.ident = uu____6273;
              FStar_Ident.nsstr = uu____6274; FStar_Ident.str = "False";_}
            ->
            let uu____6277 =
              let uu____6278 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range in
              FStar_Syntax_Syntax.fvar uu____6278
                FStar_Syntax_Syntax.Delta_constant
                FStar_Pervasives_Native.None in
            (uu____6277, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,
             { FStar_Ident.idText = txt; FStar_Ident.idRange = uu____6291;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____6293 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name in
              match uu____6293 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt in
                  let uu____6302 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_defined_at_level
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None in
                  (uu____6302, noaqs)
              | FStar_Pervasives_Native.None ->
                  let uu____6313 =
                    let uu____6314 = FStar_Ident.text_of_lid eff_name in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____6314 txt in
                  failwith uu____6313))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____6321 = desugar_name mk1 setpos env true l in
              (uu____6321, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____6334 = desugar_name mk1 setpos env true l in
              (uu____6334, noaqs)))
        | FStar_Parser_AST.Projector (l, i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____6355 = FStar_Syntax_DsEnv.try_lookup_datacon env l in
                match uu____6355 with
                | FStar_Pervasives_Native.Some uu____6364 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None ->
                    let uu____6369 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l in
                    (match uu____6369 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____6383 -> FStar_Pervasives_Native.None) in
              match name with
              | FStar_Pervasives_Native.Some (resolve, new_name) ->
                  let uu____6400 =
                    let uu____6401 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i in
                    desugar_name mk1 setpos env resolve uu____6401 in
                  (uu____6400, noaqs)
              | uu____6412 ->
                  let uu____6419 =
                    let uu____6424 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str in
                    (FStar_Errors.Fatal_EffectNotFound, uu____6424) in
                  FStar_Errors.raise_error uu____6419
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____6431 = FStar_Syntax_DsEnv.try_lookup_datacon env lid in
              match uu____6431 with
              | FStar_Pervasives_Native.None ->
                  let uu____6438 =
                    let uu____6443 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____6443) in
                  FStar_Errors.raise_error uu____6438
                    top.FStar_Parser_AST.range
              | uu____6448 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid in
                  let uu____6452 = desugar_name mk1 setpos env true lid' in
                  (uu____6452, noaqs)))
        | FStar_Parser_AST.Construct (l, args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____6478 = FStar_Syntax_DsEnv.try_lookup_datacon env l in
              match uu____6478 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1) in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____6509 ->
                       let uu____6516 =
                         FStar_Util.take
                           (fun uu____6540 ->
                              match uu____6540 with
                              | (uu____6545, imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args in
                       (match uu____6516 with
                        | (universes, args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes in
                            let uu____6590 =
                              let uu____6605 =
                                FStar_List.map
                                  (fun uu____6638 ->
                                     match uu____6638 with
                                     | (t, imp) ->
                                         let uu____6655 =
                                           desugar_term_aq env t in
                                         (match uu____6655 with
                                          | (te, aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1 in
                              FStar_All.pipe_right uu____6605
                                FStar_List.unzip in
                            (match uu____6590 with
                             | (args2, aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1)) in
                                 let uu____6748 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2)) in
                                 (uu____6748, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None ->
                  let err =
                    let uu____6778 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l in
                    match uu____6778 with
                    | FStar_Pervasives_Native.None ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.strcat "Constructor "
                             (Prims.strcat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____6785 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.strcat "Effect "
                             (Prims.strcat l.FStar_Ident.str
                                " used at an unexpected position"))) in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders, t) ->
            let uu____6796 =
              FStar_List.fold_left
                (fun uu____6841 ->
                   fun b ->
                     match uu____6841 with
                     | (env1, tparams, typs) ->
                         let uu____6898 = desugar_binder env1 b in
                         (match uu____6898 with
                          | (xopt, t1) ->
                              let uu____6927 =
                                match xopt with
                                | FStar_Pervasives_Native.None ->
                                    let uu____6936 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun in
                                    (env1, uu____6936)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x in
                              (match uu____6927 with
                               | (env2, x) ->
                                   let uu____6956 =
                                     let uu____6959 =
                                       let uu____6962 =
                                         let uu____6963 =
                                           no_annot_abs tparams t1 in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____6963 in
                                       [uu____6962] in
                                     FStar_List.append typs uu____6959 in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___127_6989 = x in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___127_6989.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___127_6989.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____6956)))) (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      FStar_Pervasives_Native.None]) in
            (match uu____6796 with
             | (env1, uu____7017, targs) ->
                 let uu____7039 =
                   let uu____7044 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____7044 in
                 (match uu____7039 with
                  | (tup, uu____7054) ->
                      let uu____7055 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_app (tup, targs)) in
                      (uu____7055, noaqs)))
        | FStar_Parser_AST.Product (binders, t) ->
            let uu____7080 = uncurry binders t in
            (match uu____7080 with
             | (bs, t1) ->
                 let rec aux env1 bs1 uu___94_7122 =
                   match uu___94_7122 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1 in
                       let uu____7136 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod in
                       FStar_All.pipe_left setpos uu____7136
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1 in
                       let uu____7158 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb in
                       (match uu____7158 with
                        | (b, env2) -> aux env2 (b :: bs1) tl1) in
                 let uu____7167 = aux env [] bs in (uu____7167, noaqs))
        | FStar_Parser_AST.Refine (b, f) ->
            let uu____7188 = desugar_binder env b in
            (match uu____7188 with
             | (FStar_Pervasives_Native.None, uu____7199) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____7213 =
                   as_binder env FStar_Pervasives_Native.None b1 in
                 (match uu____7213 with
                  | (x, env1) ->
                      let f1 = desugar_formula env1 f in
                      let t =
                        let uu____7228 =
                          FStar_Syntax_Util.refine
                            (FStar_Pervasives_Native.fst x) f1 in
                        FStar_All.pipe_left setpos uu____7228 in
                      (t, noaqs)))
        | FStar_Parser_AST.Abs (binders, body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern) in
            let uu____7260 =
              FStar_List.fold_left
                (fun uu____7280 ->
                   fun pat ->
                     match uu____7280 with
                     | (env1, ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed
                              (uu____7306, (t, FStar_Pervasives_Native.None))
                              ->
                              let uu____7316 =
                                let uu____7319 = free_type_vars env1 t in
                                FStar_List.append uu____7319 ftvs in
                              (env1, uu____7316)
                          | FStar_Parser_AST.PatAscribed
                              (uu____7324,
                               (t, FStar_Pervasives_Native.Some tac))
                              ->
                              let uu____7335 =
                                let uu____7338 = free_type_vars env1 t in
                                let uu____7341 =
                                  let uu____7344 = free_type_vars env1 tac in
                                  FStar_List.append uu____7344 ftvs in
                                FStar_List.append uu____7338 uu____7341 in
                              (env1, uu____7335)
                          | uu____7349 -> (env1, ftvs))) (env, []) binders1 in
            (match uu____7260 with
             | (uu____7358, ftv) ->
                 let ftv1 = sort_ftv ftv in
                 let binders2 =
                   let uu____7370 =
                     FStar_All.pipe_right ftv1
                       (FStar_List.map
                          (fun a ->
                             FStar_Parser_AST.mk_pattern
                               (FStar_Parser_AST.PatTvar
                                  (a,
                                    (FStar_Pervasives_Native.Some
                                       FStar_Parser_AST.Implicit)))
                               top.FStar_Parser_AST.range)) in
                   FStar_List.append uu____7370 binders1 in
                 let rec aux env1 bs sc_pat_opt uu___95_7423 =
                   match uu___95_7423 with
                   | [] ->
                       let uu____7446 = desugar_term_aq env1 body in
                       (match uu____7446 with
                        | (body1, aq) ->
                            let body2 =
                              match sc_pat_opt with
                              | FStar_Pervasives_Native.Some (sc, pat) ->
                                  let body2 =
                                    let uu____7477 =
                                      let uu____7478 =
                                        FStar_Syntax_Syntax.pat_bvs pat in
                                      FStar_All.pipe_right uu____7478
                                        (FStar_List.map
                                           FStar_Syntax_Syntax.mk_binder) in
                                    FStar_Syntax_Subst.close uu____7477 body1 in
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_match
                                       (sc,
                                         [(pat, FStar_Pervasives_Native.None,
                                            body2)]))
                                    FStar_Pervasives_Native.None
                                    body2.FStar_Syntax_Syntax.pos
                              | FStar_Pervasives_Native.None -> body1 in
                            let uu____7531 =
                              let uu____7534 =
                                no_annot_abs (FStar_List.rev bs) body2 in
                              setpos uu____7534 in
                            (uu____7531, aq))
                   | p::rest ->
                       let uu____7547 = desugar_binding_pat env1 p in
                       (match uu____7547 with
                        | (env2, b, pat) ->
                            let pat1 =
                              match pat with
                              | [] -> FStar_Pervasives_Native.None
                              | p1::[] -> FStar_Pervasives_Native.Some p1
                              | uu____7575 ->
                                  FStar_Errors.raise_error
                                    (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                      "Disjunctive patterns are not supported in abstractions")
                                    p.FStar_Parser_AST.prange in
                            let uu____7580 =
                              match b with
                              | LetBinder uu____7613 -> failwith "Impossible"
                              | LocalBinder (x, aq) ->
                                  let sc_pat_opt1 =
                                    match (pat1, sc_pat_opt) with
                                    | (FStar_Pervasives_Native.None,
                                       uu____7669) -> sc_pat_opt
                                    | (FStar_Pervasives_Native.Some p1,
                                       FStar_Pervasives_Native.None) ->
                                        let uu____7705 =
                                          let uu____7710 =
                                            FStar_Syntax_Syntax.bv_to_name x in
                                          (uu____7710, p1) in
                                        FStar_Pervasives_Native.Some
                                          uu____7705
                                    | (FStar_Pervasives_Native.Some p1,
                                       FStar_Pervasives_Native.Some (sc, p'))
                                        ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____7746, uu____7747) ->
                                             let tup2 =
                                               let uu____7749 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____7749
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor) in
                                             let sc1 =
                                               let uu____7753 =
                                                 let uu____7760 =
                                                   let uu____7761 =
                                                     let uu____7776 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2) in
                                                     let uu____7779 =
                                                       let uu____7782 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc in
                                                       let uu____7783 =
                                                         let uu____7786 =
                                                           let uu____7787 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____7787 in
                                                         [uu____7786] in
                                                       uu____7782 ::
                                                         uu____7783 in
                                                     (uu____7776, uu____7779) in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____7761 in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____7760 in
                                               uu____7753
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Parser_AST.range in
                                             let p2 =
                                               let uu____7798 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p1, false)]))
                                                 uu____7798 in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____7829, args),
                                            FStar_Syntax_Syntax.Pat_cons
                                            (uu____7831, pats)) ->
                                             let tupn =
                                               let uu____7870 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____7870
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor) in
                                             let sc1 =
                                               let uu____7880 =
                                                 let uu____7881 =
                                                   let uu____7896 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn) in
                                                   let uu____7899 =
                                                     let uu____7908 =
                                                       let uu____7917 =
                                                         let uu____7918 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____7918 in
                                                       [uu____7917] in
                                                     FStar_List.append args
                                                       uu____7908 in
                                                   (uu____7896, uu____7899) in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____7881 in
                                               mk1 uu____7880 in
                                             let p2 =
                                               let uu____7938 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p1, false)])))
                                                 uu____7938 in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | uu____7973 ->
                                             failwith "Impossible") in
                                  ((x, aq), sc_pat_opt1) in
                            (match uu____7580 with
                             | (b1, sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest)) in
                 aux env [] FStar_Pervasives_Native.None binders2)
        | FStar_Parser_AST.App
            (uu____8044, uu____8045, FStar_Parser_AST.UnivApp) ->
            let rec aux universes e =
              let uu____8067 =
                let uu____8068 = unparen e in uu____8068.FStar_Parser_AST.tm in
              match uu____8067 with
              | FStar_Parser_AST.App (e1, t, FStar_Parser_AST.UnivApp) ->
                  let univ_arg = desugar_universe t in
                  aux (univ_arg :: universes) e1
              | uu____8078 ->
                  let uu____8079 = desugar_term_aq env e in
                  (match uu____8079 with
                   | (head1, aq) ->
                       let uu____8092 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes)) in
                       (uu____8092, aq)) in
            aux [] top
        | FStar_Parser_AST.App uu____8099 ->
            let rec aux args aqs e =
              let uu____8158 =
                let uu____8159 = unparen e in uu____8159.FStar_Parser_AST.tm in
              match uu____8158 with
              | FStar_Parser_AST.App (e1, t, imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____8179 = desugar_term_aq env t in
                  (match uu____8179 with
                   | (t1, aq) ->
                       let arg = arg_withimp_e imp t1 in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____8215 ->
                  let uu____8216 = desugar_term_aq env e in
                  (match uu____8216 with
                   | (head1, aq) ->
                       let uu____8239 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args)) in
                       (uu____8239, (join_aqs (aq :: aqs)))) in
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
            let uu____8279 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range in
            desugar_term_aq env uu____8279
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
            let uu____8331 = desugar_term_aq env t in
            (match uu____8331 with
             | (tm, s) ->
                 let uu____8342 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence))) in
                 (uu____8342, s))
        | FStar_Parser_AST.LetOpen (lid, e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid in
            let uu____8350 =
              let uu____8363 = FStar_Syntax_DsEnv.expect_typ env1 in
              if uu____8363 then desugar_typ_aq else desugar_term_aq in
            uu____8350 env1 e
        | FStar_Parser_AST.Let (qual, lbs, body) ->
            let is_rec = qual = FStar_Parser_AST.Rec in
            let ds_let_rec_or_app uu____8418 =
              let bindings = lbs in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____8561 ->
                        match uu____8561 with
                        | (attr_opt, (p, def)) ->
                            let uu____8619 = is_app_pattern p in
                            if uu____8619
                            then
                              let uu____8650 =
                                destruct_app_pattern env top_level p in
                              (attr_opt, uu____8650, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1, def1) ->
                                   let uu____8732 =
                                     destruct_app_pattern env top_level p1 in
                                   (attr_opt, uu____8732, def1)
                               | uu____8777 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1, uu____8815);
                                           FStar_Parser_AST.prange =
                                             uu____8816;_},
                                         t)
                                        ->
                                        if top_level
                                        then
                                          let uu____8864 =
                                            let uu____8885 =
                                              let uu____8890 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1 in
                                              FStar_Util.Inr uu____8890 in
                                            (uu____8885, [],
                                              (FStar_Pervasives_Native.Some t)) in
                                          (attr_opt, uu____8864, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1, uu____8981) ->
                                        if top_level
                                        then
                                          let uu____9016 =
                                            let uu____9037 =
                                              let uu____9042 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1 in
                                              FStar_Util.Inr uu____9042 in
                                            (uu____9037, [],
                                              FStar_Pervasives_Native.None) in
                                          (attr_opt, uu____9016, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____9132 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange)))) in
              let uu____9163 =
                FStar_List.fold_left
                  (fun uu____9236 ->
                     fun uu____9237 ->
                       match (uu____9236, uu____9237) with
                       | ((env1, fnames, rec_bindings),
                          (_attr_opt, (f, uu____9345, uu____9346),
                           uu____9347)) ->
                           let uu____9464 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____9490 =
                                   FStar_Syntax_DsEnv.push_bv env1 x in
                                 (match uu____9490 with
                                  | (env2, xx) ->
                                      let uu____9509 =
                                        let uu____9512 =
                                          FStar_Syntax_Syntax.mk_binder xx in
                                        uu____9512 :: rec_bindings in
                                      (env2, (FStar_Util.Inl xx), uu____9509))
                             | FStar_Util.Inr l ->
                                 let uu____9520 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.Delta_equational in
                                 (uu____9520, (FStar_Util.Inr l),
                                   rec_bindings) in
                           (match uu____9464 with
                            | (env2, lbname, rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs in
              match uu____9163 with
              | (env', fnames, rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames in
                  let rec_bindings1 = FStar_List.rev rec_bindings in
                  let desugar_one_def env1 lbname uu____9668 =
                    match uu____9668 with
                    | (attrs_opt, (uu____9704, args, result_t), def) ->
                        let args1 =
                          FStar_All.pipe_right args
                            (FStar_List.map replace_unit_pattern) in
                        let pos = def.FStar_Parser_AST.range in
                        let def1 =
                          match result_t with
                          | FStar_Pervasives_Native.None -> def
                          | FStar_Pervasives_Native.Some (t, tacopt) ->
                              let t1 =
                                let uu____9792 = is_comp_type env1 t in
                                if uu____9792
                                then
                                  ((let uu____9794 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x ->
                                              let uu____9804 =
                                                is_var_pattern x in
                                              Prims.op_Negation uu____9804)) in
                                    match uu____9794 with
                                    | FStar_Pervasives_Native.None -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____9807 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____9809 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid in
                                         FStar_Option.isSome uu____9809))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0"))) in
                                   if uu____9807
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t) in
                              let uu____9813 =
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed (def, t1, tacopt))
                                uu____9813 FStar_Parser_AST.Expr in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____9817 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level in
                        let body1 = desugar_term env1 def2 in
                        let lbname1 =
                          match lbname with
                          | FStar_Util.Inl x -> FStar_Util.Inl x
                          | FStar_Util.Inr l ->
                              let uu____9832 =
                                let uu____9833 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1 in
                                FStar_Syntax_Syntax.lid_as_fv l uu____9833
                                  FStar_Pervasives_Native.None in
                              FStar_Util.Inr uu____9832 in
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
                  let uu____9892 = desugar_term_aq env' body in
                  (match uu____9892 with
                   | (body1, aq) ->
                       let uu____9905 =
                         let uu____9908 =
                           let uu____9909 =
                             let uu____9922 =
                               FStar_Syntax_Subst.close rec_bindings1 body1 in
                             ((is_rec, lbs1), uu____9922) in
                           FStar_Syntax_Syntax.Tm_let uu____9909 in
                         FStar_All.pipe_left mk1 uu____9908 in
                       (uu____9905, aq)) in
            let ds_non_rec attrs_opt pat t1 t2 =
              let attrs =
                match attrs_opt with
                | FStar_Pervasives_Native.None -> []
                | FStar_Pervasives_Native.Some l ->
                    FStar_List.map (desugar_term env) l in
              let t11 = desugar_term env t1 in
              let is_mutable = qual = FStar_Parser_AST.Mutable in
              let t12 = if is_mutable then mk_ref_alloc t11 else t11 in
              let uu____9990 =
                desugar_binding_pat_maybe_top top_level env pat is_mutable in
              match uu____9990 with
              | (env1, binder, pat1) ->
                  let uu____10012 =
                    match binder with
                    | LetBinder (l, (t, _tacopt)) ->
                        let uu____10038 = desugar_term_aq env1 t2 in
                        (match uu____10038 with
                         | (body1, aq) ->
                             let fv =
                               let uu____10052 =
                                 FStar_Syntax_Util.incr_delta_qualifier t12 in
                               FStar_Syntax_Syntax.lid_as_fv l uu____10052
                                 FStar_Pervasives_Native.None in
                             let uu____10053 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t12,
                                            (t12.FStar_Syntax_Syntax.pos))]),
                                      body1)) in
                             (uu____10053, aq))
                    | LocalBinder (x, uu____10077) ->
                        let uu____10078 = desugar_term_aq env1 t2 in
                        (match uu____10078 with
                         | (body1, aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | {
                                   FStar_Syntax_Syntax.v =
                                     FStar_Syntax_Syntax.Pat_wild uu____10092;
                                   FStar_Syntax_Syntax.p = uu____10093;_}::[]
                                   -> body1
                               | uu____10098 ->
                                   let uu____10101 =
                                     let uu____10108 =
                                       let uu____10109 =
                                         let uu____10132 =
                                           FStar_Syntax_Syntax.bv_to_name x in
                                         let uu____10133 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1 in
                                         (uu____10132, uu____10133) in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____10109 in
                                     FStar_Syntax_Syntax.mk uu____10108 in
                                   uu____10101 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range in
                             let uu____10143 =
                               let uu____10146 =
                                 let uu____10147 =
                                   let uu____10160 =
                                     let uu____10161 =
                                       let uu____10162 =
                                         FStar_Syntax_Syntax.mk_binder x in
                                       [uu____10162] in
                                     FStar_Syntax_Subst.close uu____10161
                                       body2 in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t12,
                                           (t12.FStar_Syntax_Syntax.pos))]),
                                     uu____10160) in
                                 FStar_Syntax_Syntax.Tm_let uu____10147 in
                               FStar_All.pipe_left mk1 uu____10146 in
                             (uu____10143, aq)) in
                  (match uu____10012 with
                   | (tm, aq) ->
                       if is_mutable
                       then
                         let uu____10203 =
                           FStar_All.pipe_left mk1
                             (FStar_Syntax_Syntax.Tm_meta
                                (tm,
                                  (FStar_Syntax_Syntax.Meta_desugared
                                     FStar_Syntax_Syntax.Mutable_alloc))) in
                         (uu____10203, aq)
                       else (tm, aq)) in
            let uu____10215 = FStar_List.hd lbs in
            (match uu____10215 with
             | (attrs, (head_pat, defn)) ->
                 let uu____10259 = is_rec || (is_app_pattern head_pat) in
                 if uu____10259
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1, t2, t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun in
            let t_bool1 =
              let uu____10272 =
                let uu____10273 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.Delta_constant
                    FStar_Pervasives_Native.None in
                FStar_Syntax_Syntax.Tm_fvar uu____10273 in
              mk1 uu____10272 in
            let uu____10274 = desugar_term_aq env t1 in
            (match uu____10274 with
             | (t1', aq1) ->
                 let uu____10285 = desugar_term_aq env t2 in
                 (match uu____10285 with
                  | (t2', aq2) ->
                      let uu____10296 = desugar_term_aq env t3 in
                      (match uu____10296 with
                       | (t3', aq3) ->
                           let uu____10307 =
                             let uu____10310 =
                               let uu____10311 =
                                 let uu____10334 =
                                   FStar_Syntax_Util.ascribe t1'
                                     ((FStar_Util.Inl t_bool1),
                                       FStar_Pervasives_Native.None) in
                                 let uu____10355 =
                                   let uu____10370 =
                                     let uu____10383 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t2.FStar_Parser_AST.range in
                                     (uu____10383,
                                       FStar_Pervasives_Native.None, t2') in
                                   let uu____10394 =
                                     let uu____10409 =
                                       let uu____10422 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t3.FStar_Parser_AST.range in
                                       (uu____10422,
                                         FStar_Pervasives_Native.None, t3') in
                                     [uu____10409] in
                                   uu____10370 :: uu____10394 in
                                 (uu____10334, uu____10355) in
                               FStar_Syntax_Syntax.Tm_match uu____10311 in
                             mk1 uu____10310 in
                           (uu____10307, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____10583 =
              match uu____10583 with
              | (pat, wopt, b) ->
                  let uu____10605 = desugar_match_pat env pat in
                  (match uu____10605 with
                   | (env1, pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____10630 = desugar_term env1 e1 in
                             FStar_Pervasives_Native.Some uu____10630 in
                       let uu____10631 = desugar_term_aq env1 b in
                       (match uu____10631 with
                        | (b1, aq) ->
                            let uu____10644 =
                              desugar_disjunctive_pattern pat1 wopt1 b1 in
                            (uu____10644, aq))) in
            let uu____10649 = desugar_term_aq env e in
            (match uu____10649 with
             | (e1, aq) ->
                 let uu____10660 =
                   let uu____10669 =
                     let uu____10680 = FStar_List.map desugar_branch branches in
                     FStar_All.pipe_right uu____10680 FStar_List.unzip in
                   FStar_All.pipe_right uu____10669
                     (fun uu____10744 ->
                        match uu____10744 with
                        | (x, y) -> ((FStar_List.flatten x), y)) in
                 (match uu____10660 with
                  | (brs, aqs) ->
                      let uu____10795 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs)) in
                      (uu____10795, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e, t, tac_opt) ->
            let annot =
              let uu____10828 = is_comp_type env t in
              if uu____10828
              then
                let uu____10835 = desugar_comp t.FStar_Parser_AST.range env t in
                FStar_Util.Inr uu____10835
              else
                (let uu____10841 = desugar_term env t in
                 FStar_Util.Inl uu____10841) in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env) in
            let uu____10847 = desugar_term_aq env e in
            (match uu____10847 with
             | (e1, aq) ->
                 let uu____10858 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_ascribed
                        (e1, (annot, tac_opt1), FStar_Pervasives_Native.None)) in
                 (uu____10858, aq))
        | FStar_Parser_AST.Record (uu____10887, []) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt, fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range in
            let user_ns =
              let uu____10928 = FStar_List.hd fields in
              match uu____10928 with | (f, uu____10940) -> f.FStar_Ident.ns in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____10986 ->
                        match uu____10986 with
                        | (g, uu____10992) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText)) in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f]) in
              match found with
              | FStar_Pervasives_Native.Some (uu____10998, e) -> (fn, e)
              | FStar_Pervasives_Native.None ->
                  (match xopt with
                   | FStar_Pervasives_Native.None ->
                       let uu____11012 =
                         let uu____11017 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____11017) in
                       FStar_Errors.raise_error uu____11012
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
                  let uu____11025 =
                    let uu____11036 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____11067 ->
                              match uu____11067 with
                              | (f, uu____11077) ->
                                  let uu____11078 =
                                    let uu____11079 =
                                      get_field FStar_Pervasives_Native.None
                                        f in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____11079 in
                                  (uu____11078, FStar_Parser_AST.Nothing))) in
                    (user_constrname, uu____11036) in
                  FStar_Parser_AST.Construct uu____11025
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range in
                  let xterm =
                    let uu____11097 =
                      let uu____11098 = FStar_Ident.lid_of_ids [x] in
                      FStar_Parser_AST.Var uu____11098 in
                    FStar_Parser_AST.mk_term uu____11097
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr in
                  let record1 =
                    let uu____11100 =
                      let uu____11113 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____11143 ->
                                match uu____11143 with
                                | (f, uu____11153) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f)) in
                      (FStar_Pervasives_Native.None, uu____11113) in
                    FStar_Parser_AST.Record uu____11100 in
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
            let uu____11213 = desugar_term_aq env recterm1 in
            (match uu____11213 with
             | (e, s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____11229;
                         FStar_Syntax_Syntax.vars = uu____11230;_},
                       args)
                      ->
                      let uu____11252 =
                        let uu____11255 =
                          let uu____11256 =
                            let uu____11271 =
                              let uu____11272 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos in
                              let uu____11273 =
                                let uu____11276 =
                                  let uu____11277 =
                                    let uu____11284 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst) in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____11284) in
                                  FStar_Syntax_Syntax.Record_ctor uu____11277 in
                                FStar_Pervasives_Native.Some uu____11276 in
                              FStar_Syntax_Syntax.fvar uu____11272
                                FStar_Syntax_Syntax.Delta_constant
                                uu____11273 in
                            (uu____11271, args) in
                          FStar_Syntax_Syntax.Tm_app uu____11256 in
                        FStar_All.pipe_left mk1 uu____11255 in
                      (uu____11252, s)
                  | uu____11313 -> (e, s)))
        | FStar_Parser_AST.Project (e, f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____11317 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f in
              match uu____11317 with
              | (constrname, is_rec) ->
                  let uu____11332 = desugar_term_aq env e in
                  (match uu____11332 with
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
                       let uu____11350 =
                         let uu____11353 =
                           let uu____11354 =
                             let uu____11369 =
                               let uu____11370 =
                                 let uu____11371 = FStar_Ident.range_of_lid f in
                                 FStar_Ident.set_lid_range projname
                                   uu____11371 in
                               FStar_Syntax_Syntax.fvar uu____11370
                                 FStar_Syntax_Syntax.Delta_equational qual in
                             let uu____11372 =
                               let uu____11375 =
                                 FStar_Syntax_Syntax.as_arg e1 in
                               [uu____11375] in
                             (uu____11369, uu____11372) in
                           FStar_Syntax_Syntax.Tm_app uu____11354 in
                         FStar_All.pipe_left mk1 uu____11353 in
                       (uu____11350, s))))
        | FStar_Parser_AST.NamedTyp (uu____11382, e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e in
            let uu____11391 =
              let uu____11392 = FStar_Syntax_Subst.compress tm in
              uu____11392.FStar_Syntax_Syntax.n in
            (match uu____11391 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____11400 =
                   let uu___128_11403 =
                     let uu____11404 =
                       let uu____11405 = FStar_Syntax_Syntax.lid_of_fv fv in
                       FStar_Ident.string_of_lid uu____11405 in
                     FStar_Syntax_Util.exp_string uu____11404 in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___128_11403.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___128_11403.FStar_Syntax_Syntax.vars)
                   } in
                 (uu____11400, noaqs)
             | uu____11418 ->
                 let uu____11419 =
                   let uu____11424 =
                     let uu____11425 = FStar_Syntax_Print.term_to_string tm in
                     Prims.strcat "VQuote, expected an fvar, got: "
                       uu____11425 in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____11424) in
                 FStar_Errors.raise_error uu____11419
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e, FStar_Parser_AST.Static) ->
            let uu____11431 = desugar_term_aq env e in
            (match uu____11431 with
             | (tm, vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   } in
                 let uu____11443 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi)) in
                 (uu____11443, noaqs))
        | FStar_Parser_AST.Antiquote (b, e) ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun in
            let uu____11463 = FStar_Syntax_Syntax.bv_to_name bv in
            let uu____11464 =
              let uu____11473 =
                let uu____11480 = desugar_term env e in (bv, b, uu____11480) in
              [uu____11473] in
            (uu____11463, uu____11464)
        | FStar_Parser_AST.Quote (e, FStar_Parser_AST.Dynamic) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              } in
            let uu____11511 =
              let uu____11514 =
                let uu____11515 =
                  let uu____11522 = desugar_term env e in (uu____11522, qi) in
                FStar_Syntax_Syntax.Tm_quoted uu____11515 in
              FStar_All.pipe_left mk1 uu____11514 in
            (uu____11511, noaqs)
        | uu____11537 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____11538 = desugar_formula env top in (uu____11538, noaqs)
        | uu____11549 ->
            let uu____11550 =
              let uu____11555 =
                let uu____11556 = FStar_Parser_AST.term_to_string top in
                Prims.strcat "Unexpected term: " uu____11556 in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____11555) in
            FStar_Errors.raise_error uu____11550 top.FStar_Parser_AST.range
and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____11562 -> false
    | uu____11571 -> true
and (is_synth_by_tactic :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun e ->
    fun t ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (l, r, FStar_Parser_AST.Hash) ->
          is_synth_by_tactic e l
      | FStar_Parser_AST.Var lid ->
          let uu____11577 =
            FStar_Syntax_DsEnv.resolve_to_fully_qualified_name e lid in
          (match uu____11577 with
           | FStar_Pervasives_Native.Some lid1 ->
               FStar_Ident.lid_equals lid1 FStar_Parser_Const.synth_lid
           | FStar_Pervasives_Native.None -> false)
      | uu____11581 -> false
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
           (fun uu____11618 ->
              match uu____11618 with
              | (a, imp) ->
                  let uu____11631 = desugar_term env a in
                  arg_withimp_e imp uu____11631))
and (desugar_comp :
  FStar_Range.range ->
    FStar_Syntax_DsEnv.env ->
      FStar_Parser_AST.term ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun r ->
    fun env ->
      fun t ->
        let fail1 err = FStar_Errors.raise_error err r in
        let is_requires uu____11663 =
          match uu____11663 with
          | (t1, uu____11669) ->
              let uu____11670 =
                let uu____11671 = unparen t1 in
                uu____11671.FStar_Parser_AST.tm in
              (match uu____11670 with
               | FStar_Parser_AST.Requires uu____11672 -> true
               | uu____11679 -> false) in
        let is_ensures uu____11689 =
          match uu____11689 with
          | (t1, uu____11695) ->
              let uu____11696 =
                let uu____11697 = unparen t1 in
                uu____11697.FStar_Parser_AST.tm in
              (match uu____11696 with
               | FStar_Parser_AST.Ensures uu____11698 -> true
               | uu____11705 -> false) in
        let is_app head1 uu____11720 =
          match uu____11720 with
          | (t1, uu____11726) ->
              let uu____11727 =
                let uu____11728 = unparen t1 in
                uu____11728.FStar_Parser_AST.tm in
              (match uu____11727 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____11730;
                      FStar_Parser_AST.level = uu____11731;_},
                    uu____11732, uu____11733)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____11734 -> false) in
        let is_smt_pat uu____11744 =
          match uu____11744 with
          | (t1, uu____11750) ->
              let uu____11751 =
                let uu____11752 = unparen t1 in
                uu____11752.FStar_Parser_AST.tm in
              (match uu____11751 with
               | FStar_Parser_AST.Construct
                   (cons1,
                    ({
                       FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                         (smtpat, uu____11755);
                       FStar_Parser_AST.range = uu____11756;
                       FStar_Parser_AST.level = uu____11757;_},
                     uu____11758)::uu____11759::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s -> smtpat.FStar_Ident.str = s)
                        ["SMTPat"; "SMTPatT"; "SMTPatOr"])
               | FStar_Parser_AST.Construct
                   (cons1,
                    ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var smtpat;
                       FStar_Parser_AST.range = uu____11798;
                       FStar_Parser_AST.level = uu____11799;_},
                     uu____11800)::uu____11801::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
               | uu____11826 -> false) in
        let is_decreases = is_app "decreases" in
        let pre_process_comp_typ t1 =
          let uu____11858 = head_and_args t1 in
          match uu____11858 with
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
                   let thunk_ens uu____11956 =
                     match uu____11956 with
                     | (e, i) ->
                         let uu____11967 = thunk_ens_ e in (uu____11967, i) in
                   let fail_lemma uu____11979 =
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
                         let uu____12059 =
                           let uu____12066 =
                             let uu____12073 = thunk_ens ens in
                             [uu____12073; nil_pat] in
                           req_true :: uu____12066 in
                         unit_tm :: uu____12059
                     | req::ens::[] when
                         (is_requires req) && (is_ensures ens) ->
                         let uu____12120 =
                           let uu____12127 =
                             let uu____12134 = thunk_ens ens in
                             [uu____12134; nil_pat] in
                           req :: uu____12127 in
                         unit_tm :: uu____12120
                     | ens::smtpat::[] when
                         (((let uu____12183 = is_requires ens in
                            Prims.op_Negation uu____12183) &&
                             (let uu____12185 = is_smt_pat ens in
                              Prims.op_Negation uu____12185))
                            &&
                            (let uu____12187 = is_decreases ens in
                             Prims.op_Negation uu____12187))
                           && (is_smt_pat smtpat)
                         ->
                         let uu____12188 =
                           let uu____12195 =
                             let uu____12202 = thunk_ens ens in
                             [uu____12202; smtpat] in
                           req_true :: uu____12195 in
                         unit_tm :: uu____12188
                     | ens::dec::[] when
                         (is_ensures ens) && (is_decreases dec) ->
                         let uu____12249 =
                           let uu____12256 =
                             let uu____12263 = thunk_ens ens in
                             [uu____12263; nil_pat; dec] in
                           req_true :: uu____12256 in
                         unit_tm :: uu____12249
                     | ens::dec::smtpat::[] when
                         ((is_ensures ens) && (is_decreases dec)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____12323 =
                           let uu____12330 =
                             let uu____12337 = thunk_ens ens in
                             [uu____12337; smtpat; dec] in
                           req_true :: uu____12330 in
                         unit_tm :: uu____12323
                     | req::ens::dec::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_decreases dec)
                         ->
                         let uu____12397 =
                           let uu____12404 =
                             let uu____12411 = thunk_ens ens in
                             [uu____12411; nil_pat; dec] in
                           req :: uu____12404 in
                         unit_tm :: uu____12397
                     | req::ens::smtpat::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____12471 =
                           let uu____12478 =
                             let uu____12485 = thunk_ens ens in
                             [uu____12485; smtpat] in
                           req :: uu____12478 in
                         unit_tm :: uu____12471
                     | req::ens::dec::smtpat::[] when
                         (((is_requires req) && (is_ensures ens)) &&
                            (is_smt_pat smtpat))
                           && (is_decreases dec)
                         ->
                         let uu____12550 =
                           let uu____12557 =
                             let uu____12564 = thunk_ens ens in
                             [uu____12564; dec; smtpat] in
                           req :: uu____12557 in
                         unit_tm :: uu____12550
                     | _other -> fail_lemma () in
                   let head_and_attributes =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) lemma in
                   (head_and_attributes, args1)
               | FStar_Parser_AST.Name l when
                   FStar_Syntax_DsEnv.is_effect_name env l ->
                   let uu____12626 =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) l in
                   (uu____12626, args)
               | FStar_Parser_AST.Name l when
                   (let uu____12654 = FStar_Syntax_DsEnv.current_module env in
                    FStar_Ident.lid_equals uu____12654
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   let uu____12655 =
                     let uu____12662 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_Tot_lid
                         head1.FStar_Parser_AST.range in
                     (uu____12662, []) in
                   (uu____12655, args)
               | FStar_Parser_AST.Name l when
                   (let uu____12680 = FStar_Syntax_DsEnv.current_module env in
                    FStar_Ident.lid_equals uu____12680
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                   ->
                   let uu____12681 =
                     let uu____12688 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_GTot_lid
                         head1.FStar_Parser_AST.range in
                     (uu____12688, []) in
                   (uu____12681, args)
               | FStar_Parser_AST.Name l when
                   (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                      ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                     || ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                   ->
                   let uu____12704 =
                     let uu____12711 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_Tot_lid
                         head1.FStar_Parser_AST.range in
                     (uu____12711, []) in
                   (uu____12704, [(t1, FStar_Parser_AST.Nothing)])
               | uu____12734 ->
                   let default_effect =
                     let uu____12736 = FStar_Options.ml_ish () in
                     if uu____12736
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____12739 =
                           FStar_Options.warn_default_effects () in
                         if uu____12739
                         then
                           FStar_Errors.log_issue
                             head1.FStar_Parser_AST.range
                             (FStar_Errors.Warning_UseDefaultEffect,
                               "Using default effect Tot")
                         else ());
                        FStar_Parser_Const.effect_Tot_lid) in
                   let uu____12741 =
                     let uu____12748 =
                       FStar_Ident.set_lid_range default_effect
                         head1.FStar_Parser_AST.range in
                     (uu____12748, []) in
                   (uu____12741, [(t1, FStar_Parser_AST.Nothing)])) in
        let uu____12771 = pre_process_comp_typ t in
        match uu____12771 with
        | ((eff, cattributes), args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____12820 =
                  let uu____12825 =
                    let uu____12826 = FStar_Syntax_Print.lid_to_string eff in
                    FStar_Util.format1 "Not enough args to effect %s"
                      uu____12826 in
                  (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____12825) in
                fail1 uu____12820)
             else ();
             (let is_universe uu____12837 =
                match uu____12837 with
                | (uu____12842, imp) -> imp = FStar_Parser_AST.UnivApp in
              let uu____12844 = FStar_Util.take is_universe args in
              match uu____12844 with
              | (universes, args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____12903 ->
                         match uu____12903 with
                         | (u, imp) -> desugar_universe u) universes in
                  let uu____12910 =
                    let uu____12925 = FStar_List.hd args1 in
                    let uu____12934 = FStar_List.tl args1 in
                    (uu____12925, uu____12934) in
                  (match uu____12910 with
                   | (result_arg, rest) ->
                       let result_typ =
                         desugar_typ env
                           (FStar_Pervasives_Native.fst result_arg) in
                       let rest1 = desugar_args env rest in
                       let uu____12989 =
                         let is_decrease uu____13027 =
                           match uu____13027 with
                           | (t1, uu____13037) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.pos = uu____13047;
                                       FStar_Syntax_Syntax.vars = uu____13048;_},
                                     uu____13049::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.decreases_lid
                                | uu____13080 -> false) in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease) in
                       (match uu____12989 with
                        | (dec, rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____13194 ->
                                      match uu____13194 with
                                      | (t1, uu____13204) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____13213,
                                                (arg, uu____13215)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____13244 -> failwith "impos"))) in
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
                                | uu____13261 -> false in
                              (((is_empty decreases_clause) &&
                                  (is_empty rest2))
                                 && (is_empty cattributes))
                                && (is_empty universes1) in
                            let uu____13272 =
                              no_additional_args &&
                                (FStar_Ident.lid_equals eff
                                   FStar_Parser_Const.effect_Tot_lid) in
                            if uu____13272
                            then FStar_Syntax_Syntax.mk_Total result_typ
                            else
                              (let uu____13276 =
                                 no_additional_args &&
                                   (FStar_Ident.lid_equals eff
                                      FStar_Parser_Const.effect_GTot_lid) in
                               if uu____13276
                               then FStar_Syntax_Syntax.mk_GTotal result_typ
                               else
                                 (let flags1 =
                                    let uu____13283 =
                                      FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_Lemma_lid in
                                    if uu____13283
                                    then [FStar_Syntax_Syntax.LEMMA]
                                    else
                                      (let uu____13287 =
                                         FStar_Ident.lid_equals eff
                                           FStar_Parser_Const.effect_Tot_lid in
                                       if uu____13287
                                       then [FStar_Syntax_Syntax.TOTAL]
                                       else
                                         (let uu____13291 =
                                            FStar_Ident.lid_equals eff
                                              FStar_Parser_Const.effect_ML_lid in
                                          if uu____13291
                                          then [FStar_Syntax_Syntax.MLEFFECT]
                                          else
                                            (let uu____13295 =
                                               FStar_Ident.lid_equals eff
                                                 FStar_Parser_Const.effect_GTot_lid in
                                             if uu____13295
                                             then
                                               [FStar_Syntax_Syntax.SOMETRIVIAL]
                                             else []))) in
                                  let flags2 =
                                    FStar_List.append flags1 cattributes in
                                  let rest3 =
                                    let uu____13313 =
                                      FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_Lemma_lid in
                                    if uu____13313
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
                                                  let uu____13402 =
                                                    FStar_Ident.set_lid_range
                                                      FStar_Parser_Const.pattern_lid
                                                      pat.FStar_Syntax_Syntax.pos in
                                                  FStar_Syntax_Syntax.fvar
                                                    uu____13402
                                                    FStar_Syntax_Syntax.Delta_constant
                                                    FStar_Pervasives_Native.None in
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  nil
                                                  [(pattern,
                                                     (FStar_Pervasives_Native.Some
                                                        FStar_Syntax_Syntax.imp_tag))]
                                                  FStar_Pervasives_Native.None
                                                  pat.FStar_Syntax_Syntax.pos
                                            | uu____13417 -> pat in
                                          let uu____13418 =
                                            let uu____13429 =
                                              let uu____13440 =
                                                let uu____13449 =
                                                  FStar_Syntax_Syntax.mk
                                                    (FStar_Syntax_Syntax.Tm_meta
                                                       (pat1,
                                                         (FStar_Syntax_Syntax.Meta_desugared
                                                            FStar_Syntax_Syntax.Meta_smt_pat)))
                                                    FStar_Pervasives_Native.None
                                                    pat1.FStar_Syntax_Syntax.pos in
                                                (uu____13449, aq) in
                                              [uu____13440] in
                                            ens :: uu____13429 in
                                          req :: uu____13418
                                      | uu____13490 -> rest2
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
                                    }))))))
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
        | uu____13514 -> FStar_Pervasives_Native.None in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range in
      let setpos t =
        let uu___129_13535 = t in
        {
          FStar_Syntax_Syntax.n = (uu___129_13535.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___129_13535.FStar_Syntax_Syntax.vars)
        } in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___130_13577 = b in
             {
               FStar_Parser_AST.b = (uu___130_13577.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___130_13577.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___130_13577.FStar_Parser_AST.aqual)
             }) in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e ->
                       let uu____13640 = desugar_term env1 e in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____13640)))
            pats1 in
        match tk with
        | (FStar_Pervasives_Native.Some a, k) ->
            let uu____13653 = FStar_Syntax_DsEnv.push_bv env a in
            (match uu____13653 with
             | (env1, a1) ->
                 let a2 =
                   let uu___131_13663 = a1 in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___131_13663.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___131_13663.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   } in
                 let pats1 = desugar_pats env1 pats in
                 let body1 = desugar_formula env1 body in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____13685 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1))) in
                 let body3 =
                   let uu____13699 =
                     let uu____13702 =
                       let uu____13703 = FStar_Syntax_Syntax.mk_binder a2 in
                       [uu____13703] in
                     no_annot_abs uu____13702 body2 in
                   FStar_All.pipe_left setpos uu____13699 in
                 let uu____13708 =
                   let uu____13709 =
                     let uu____13724 =
                       let uu____13725 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange in
                       FStar_Syntax_Syntax.fvar uu____13725
                         (FStar_Syntax_Syntax.Delta_defined_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None in
                     let uu____13726 =
                       let uu____13729 = FStar_Syntax_Syntax.as_arg body3 in
                       [uu____13729] in
                     (uu____13724, uu____13726) in
                   FStar_Syntax_Syntax.Tm_app uu____13709 in
                 FStar_All.pipe_left mk1 uu____13708)
        | uu____13734 -> failwith "impossible" in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest in
            let body1 =
              let uu____13814 = q (rest, pats, body) in
              let uu____13821 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range in
              FStar_Parser_AST.mk_term uu____13814 uu____13821
                FStar_Parser_AST.Formula in
            let uu____13822 = q ([b], [], body1) in
            FStar_Parser_AST.mk_term uu____13822 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____13831 -> failwith "impossible" in
      let uu____13834 =
        let uu____13835 = unparen f in uu____13835.FStar_Parser_AST.tm in
      match uu____13834 with
      | FStar_Parser_AST.Labeled (f1, l, p) ->
          let f2 = desugar_formula env f1 in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([], uu____13842, uu____13843) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([], uu____13854, uu____13855) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3, pats, body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____13886 =
            push_quant (fun x -> FStar_Parser_AST.QForall x) binders pats
              body in
          desugar_formula env uu____13886
      | FStar_Parser_AST.QExists (_1::_2::_3, pats, body) ->
          let binders = _1 :: _2 :: _3 in
          let uu____13922 =
            push_quant (fun x -> FStar_Parser_AST.QExists x) binders pats
              body in
          desugar_formula env uu____13922
      | FStar_Parser_AST.QForall (b::[], pats, body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[], pats, body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____13965 -> desugar_term env f
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
      let uu____13970 =
        FStar_List.fold_left
          (fun uu____14006 ->
             fun b ->
               match uu____14006 with
               | (env1, out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___132_14058 = b in
                        {
                          FStar_Parser_AST.b =
                            (uu___132_14058.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___132_14058.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___132_14058.FStar_Parser_AST.aqual)
                        }) in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a, k) ->
                        let uu____14075 = FStar_Syntax_DsEnv.push_bv env1 a in
                        (match uu____14075 with
                         | (env2, a1) ->
                             let a2 =
                               let uu___133_14095 = a1 in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___133_14095.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___133_14095.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               } in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____14112 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs in
      match uu____13970 with
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
          let uu____14199 = desugar_typ env t in
          ((FStar_Pervasives_Native.Some x), uu____14199)
      | FStar_Parser_AST.Annotated (x, t) ->
          let uu____14204 = desugar_typ env t in
          ((FStar_Pervasives_Native.Some x), uu____14204)
      | FStar_Parser_AST.TVariable x ->
          let uu____14208 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange in
          ((FStar_Pervasives_Native.Some x), uu____14208)
      | FStar_Parser_AST.NoName t ->
          let uu____14216 = desugar_typ env t in
          (FStar_Pervasives_Native.None, uu____14216)
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
               (fun uu___96_14255 ->
                  match uu___96_14255 with
                  | FStar_Syntax_Syntax.Abstract -> true
                  | FStar_Syntax_Syntax.Private -> true
                  | uu____14256 -> false)) in
        let quals2 q =
          let uu____14269 =
            (let uu____14272 = FStar_Syntax_DsEnv.iface env in
             Prims.op_Negation uu____14272) ||
              (FStar_Syntax_DsEnv.admitted_iface env) in
          if uu____14269
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1 in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d in
                let uu____14286 = FStar_Ident.range_of_lid disc_name in
                let uu____14287 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d] in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____14286;
                  FStar_Syntax_Syntax.sigquals = uu____14287;
                  FStar_Syntax_Syntax.sigmeta =
                    FStar_Syntax_Syntax.default_sigmeta;
                  FStar_Syntax_Syntax.sigattrs = []
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
            let uu____14328 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i ->
                      fun uu____14358 ->
                        match uu____14358 with
                        | (x, uu____14366) ->
                            let uu____14367 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i in
                            (match uu____14367 with
                             | (field_name, uu____14375) ->
                                 let only_decl =
                                   ((let uu____14379 =
                                       FStar_Syntax_DsEnv.current_module env in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____14379)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____14381 =
                                        let uu____14382 =
                                          FStar_Syntax_DsEnv.current_module
                                            env in
                                        uu____14382.FStar_Ident.str in
                                      FStar_Options.dont_gen_projectors
                                        uu____14381) in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____14398 =
                                       FStar_List.filter
                                         (fun uu___97_14402 ->
                                            match uu___97_14402 with
                                            | FStar_Syntax_Syntax.Abstract ->
                                                false
                                            | uu____14403 -> true) q in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____14398
                                   else q in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___98_14416 ->
                                             match uu___98_14416 with
                                             | FStar_Syntax_Syntax.Abstract
                                                 -> true
                                             | FStar_Syntax_Syntax.Private ->
                                                 true
                                             | uu____14417 -> false)) in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1) in
                                 let decl =
                                   let uu____14419 =
                                     FStar_Ident.range_of_lid field_name in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____14419;
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   } in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____14426 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract) in
                                      if uu____14426
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          FStar_Syntax_Syntax.Delta_equational
                                      else
                                        FStar_Syntax_Syntax.Delta_equational in
                                    let lb =
                                      let uu____14431 =
                                        let uu____14436 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None in
                                        FStar_Util.Inr uu____14436 in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____14431;
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
                                      let uu____14440 =
                                        let uu____14441 =
                                          let uu____14448 =
                                            let uu____14451 =
                                              let uu____14452 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right in
                                              FStar_All.pipe_right
                                                uu____14452
                                                (fun fv ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v) in
                                            [uu____14451] in
                                          ((false, [lb]), uu____14448) in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____14441 in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____14440;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      } in
                                    if no_decl then [impl] else [decl; impl])))) in
            FStar_All.pipe_right uu____14328 FStar_List.flatten
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
            (lid, uu____14502, t, uu____14504, n1, uu____14506) when
            let uu____14511 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid in
            Prims.op_Negation uu____14511 ->
            let uu____14512 = FStar_Syntax_Util.arrow_formals t in
            (match uu____14512 with
             | (formals, uu____14528) ->
                 (match formals with
                  | [] -> []
                  | uu____14551 ->
                      let filter_records uu___99_14565 =
                        match uu___99_14565 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____14568, fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____14580 -> FStar_Pervasives_Native.None in
                      let fv_qual =
                        let uu____14582 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records in
                        match uu____14582 with
                        | FStar_Pervasives_Native.None ->
                            FStar_Syntax_Syntax.Data_ctor
                        | FStar_Pervasives_Native.Some q -> q in
                      let iquals1 =
                        if
                          FStar_List.contains FStar_Syntax_Syntax.Abstract
                            iquals
                        then FStar_Syntax_Syntax.Private :: iquals
                        else iquals in
                      let uu____14592 = FStar_Util.first_N n1 formals in
                      (match uu____14592 with
                       | (uu____14615, rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____14641 -> []
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
                    let uu____14707 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract) in
                    if uu____14707
                    then
                      let uu____14710 =
                        FStar_Syntax_Util.incr_delta_qualifier t in
                      FStar_Syntax_Syntax.Delta_abstract uu____14710
                    else FStar_Syntax_Util.incr_delta_qualifier t in
                  let lb =
                    let uu____14713 =
                      let uu____14718 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None in
                      FStar_Util.Inr uu____14718 in
                    let uu____14719 =
                      let uu____14722 = FStar_Syntax_Syntax.mk_Total k in
                      FStar_Syntax_Util.arrow typars uu____14722 in
                    let uu____14725 = no_annot_abs typars t in
                    {
                      FStar_Syntax_Syntax.lbname = uu____14713;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____14719;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____14725;
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
          let tycon_id uu___100_14782 =
            match uu___100_14782 with
            | FStar_Parser_AST.TyconAbstract (id1, uu____14784, uu____14785)
                -> id1
            | FStar_Parser_AST.TyconAbbrev
                (id1, uu____14795, uu____14796, uu____14797) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1, uu____14807, uu____14808, uu____14809) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1, uu____14839, uu____14840, uu____14841) -> id1 in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x, uu____14885) ->
                let uu____14886 =
                  let uu____14887 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____14887 in
                FStar_Parser_AST.mk_term uu____14886 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____14889 =
                  let uu____14890 = FStar_Ident.lid_of_ids [x] in
                  FStar_Parser_AST.Var uu____14890 in
                FStar_Parser_AST.mk_term uu____14889 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a, uu____14892) ->
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
              | uu____14923 -> FStar_Parser_AST.Nothing in
            FStar_List.fold_left
              (fun out ->
                 fun b ->
                   let uu____14929 =
                     let uu____14930 =
                       let uu____14937 = binder_to_term b in
                       (out, uu____14937, (imp_of_aqual b)) in
                     FStar_Parser_AST.App uu____14930 in
                   FStar_Parser_AST.mk_term uu____14929
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders in
          let tycon_record_as_variant uu___101_14949 =
            match uu___101_14949 with
            | FStar_Parser_AST.TyconRecord (id1, parms, kopt, fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange)) in
                let mfields =
                  FStar_List.map
                    (fun uu____15005 ->
                       match uu____15005 with
                       | (x, t, uu____15016) ->
                           let uu____15021 =
                             let uu____15022 =
                               let uu____15027 =
                                 FStar_Syntax_Util.mangle_field_name x in
                               (uu____15027, t) in
                             FStar_Parser_AST.Annotated uu____15022 in
                           FStar_Parser_AST.mk_binder uu____15021
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields in
                let result =
                  let uu____15029 =
                    let uu____15030 =
                      let uu____15031 = FStar_Ident.lid_of_ids [id1] in
                      FStar_Parser_AST.Var uu____15031 in
                    FStar_Parser_AST.mk_term uu____15030
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                  apply_binders uu____15029 parms in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level in
                let uu____15035 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____15062 ->
                          match uu____15062 with
                          | (x, uu____15072, uu____15073) ->
                              FStar_Syntax_Util.unmangle_field_name x)) in
                ((FStar_Parser_AST.TyconVariant
                    (id1, parms, kopt,
                      [(constrName, (FStar_Pervasives_Native.Some constrTyp),
                         FStar_Pervasives_Native.None, false)])),
                  uu____15035)
            | uu____15126 -> failwith "impossible" in
          let desugar_abstract_tc quals1 _env mutuals uu___102_15165 =
            match uu___102_15165 with
            | FStar_Parser_AST.TyconAbstract (id1, binders, kopt) ->
                let uu____15189 = typars_of_binders _env binders in
                (match uu____15189 with
                 | (_env', typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k in
                     let tconstr =
                       let uu____15235 =
                         let uu____15236 =
                           let uu____15237 = FStar_Ident.lid_of_ids [id1] in
                           FStar_Parser_AST.Var uu____15237 in
                         FStar_Parser_AST.mk_term uu____15236
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level in
                       apply_binders uu____15235 binders in
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
            | uu____15250 -> failwith "Unexpected tycon" in
          let push_tparams env1 bs =
            let uu____15298 =
              FStar_List.fold_left
                (fun uu____15338 ->
                   fun uu____15339 ->
                     match (uu____15338, uu____15339) with
                     | ((env2, tps), (x, imp)) ->
                         let uu____15430 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname in
                         (match uu____15430 with
                          | (env3, y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs in
            match uu____15298 with
            | (env2, bs1) -> (env2, (FStar_List.rev bs1)) in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1, bs, kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None ->
                    let uu____15543 = tm_type_z id1.FStar_Ident.idRange in
                    FStar_Pervasives_Native.Some uu____15543
                | uu____15544 -> kopt in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1) in
              let uu____15552 = desugar_abstract_tc quals env [] tc in
              (match uu____15552 with
               | (uu____15565, uu____15566, se, uu____15568) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l, uu____15571, typars, k, [], []) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____15588 =
                                 let uu____15589 = FStar_Options.ml_ish () in
                                 Prims.op_Negation uu____15589 in
                               if uu____15588
                               then
                                 let uu____15590 =
                                   let uu____15595 =
                                     let uu____15596 =
                                       FStar_Syntax_Print.lid_to_string l in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____15596 in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____15595) in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____15590
                               else ());
                              FStar_Syntax_Syntax.Assumption
                              ::
                              FStar_Syntax_Syntax.New
                              ::
                              quals1) in
                         let t =
                           match typars with
                           | [] -> k
                           | uu____15603 ->
                               let uu____15604 =
                                 let uu____15611 =
                                   let uu____15612 =
                                     let uu____15625 =
                                       FStar_Syntax_Syntax.mk_Total k in
                                     (typars, uu____15625) in
                                   FStar_Syntax_Syntax.Tm_arrow uu____15612 in
                                 FStar_Syntax_Syntax.mk uu____15611 in
                               uu____15604 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng in
                         let uu___134_15629 = se in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___134_15629.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___134_15629.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___134_15629.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____15632 -> failwith "Impossible" in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1 in
                   let env2 =
                     let uu____15635 = FStar_Syntax_DsEnv.qualify env1 id1 in
                     FStar_Syntax_DsEnv.push_doc env1 uu____15635
                       d.FStar_Parser_AST.doc in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1, binders, kopt, t))::[] ->
              let uu____15650 = typars_of_binders env binders in
              (match uu____15650 with
               | (env', typars) ->
                   let k =
                     match kopt with
                     | FStar_Pervasives_Native.None ->
                         let uu____15686 =
                           FStar_Util.for_some
                             (fun uu___103_15688 ->
                                match uu___103_15688 with
                                | FStar_Syntax_Syntax.Effect -> true
                                | uu____15689 -> false) quals in
                         if uu____15686
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Util.ktype
                     | FStar_Pervasives_Native.Some k -> desugar_term env' k in
                   let t0 = t in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1 in
                   let se =
                     let uu____15695 =
                       FStar_All.pipe_right quals
                         (FStar_List.contains FStar_Syntax_Syntax.Effect) in
                     if uu____15695
                     then
                       let uu____15698 =
                         let uu____15705 =
                           let uu____15706 = unparen t in
                           uu____15706.FStar_Parser_AST.tm in
                         match uu____15705 with
                         | FStar_Parser_AST.Construct (head1, args) ->
                             let uu____15727 =
                               match FStar_List.rev args with
                               | (last_arg, uu____15757)::args_rev ->
                                   let uu____15769 =
                                     let uu____15770 = unparen last_arg in
                                     uu____15770.FStar_Parser_AST.tm in
                                   (match uu____15769 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____15798 -> ([], args))
                               | uu____15807 -> ([], args) in
                             (match uu____15727 with
                              | (cattributes, args1) ->
                                  let uu____15846 =
                                    desugar_attributes env cattributes in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____15846))
                         | uu____15857 -> (t, []) in
                       match uu____15698 with
                       | (t1, cattributes) ->
                           let c =
                             desugar_comp t1.FStar_Parser_AST.range env' t1 in
                           let typars1 =
                             FStar_Syntax_Subst.close_binders typars in
                           let c1 = FStar_Syntax_Subst.close_comp typars1 c in
                           let quals1 =
                             FStar_All.pipe_right quals
                               (FStar_List.filter
                                  (fun uu___104_15879 ->
                                     match uu___104_15879 with
                                     | FStar_Syntax_Syntax.Effect -> false
                                     | uu____15880 -> true)) in
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
          | (FStar_Parser_AST.TyconRecord uu____15891)::[] ->
              let trec = FStar_List.hd tcs in
              let uu____15915 = tycon_record_as_variant trec in
              (match uu____15915 with
               | (t, fs) ->
                   let uu____15932 =
                     let uu____15935 =
                       let uu____15936 =
                         let uu____15945 =
                           let uu____15948 =
                             FStar_Syntax_DsEnv.current_module env in
                           FStar_Ident.ids_of_lid uu____15948 in
                         (uu____15945, fs) in
                       FStar_Syntax_Syntax.RecordType uu____15936 in
                     uu____15935 :: quals in
                   desugar_tycon env d uu____15932 [t])
          | uu____15953::uu____15954 ->
              let env0 = env in
              let mutuals =
                FStar_List.map
                  (fun x ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs in
              let rec collect_tcs quals1 et tc =
                let uu____16121 = et in
                match uu____16121 with
                | (env1, tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____16346 ->
                         let trec = tc in
                         let uu____16370 = tycon_record_as_variant trec in
                         (match uu____16370 with
                          | (t, fs) ->
                              let uu____16429 =
                                let uu____16432 =
                                  let uu____16433 =
                                    let uu____16442 =
                                      let uu____16445 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1 in
                                      FStar_Ident.ids_of_lid uu____16445 in
                                    (uu____16442, fs) in
                                  FStar_Syntax_Syntax.RecordType uu____16433 in
                                uu____16432 :: quals1 in
                              collect_tcs uu____16429 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1, binders, kopt, constructors) ->
                         let uu____16532 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt)) in
                         (match uu____16532 with
                          | (env2, uu____16592, se, tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1, binders, kopt, t)
                         ->
                         let uu____16741 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt)) in
                         (match uu____16741 with
                          | (env2, uu____16801, se, tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____16926 ->
                         failwith "Unrecognized mutual type definition") in
              let uu____16973 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs in
              (match uu____16973 with
               | (env1, tcs1) ->
                   let tcs2 = FStar_List.rev tcs1 in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___106_17484 ->
                             match uu___106_17484 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1, uvs, tpars, k, uu____17551,
                                       uu____17552);
                                    FStar_Syntax_Syntax.sigrng = uu____17553;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____17554;
                                    FStar_Syntax_Syntax.sigmeta = uu____17555;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____17556;_},
                                  binders, t, quals1)
                                 ->
                                 let t1 =
                                   let uu____17617 =
                                     typars_of_binders env1 binders in
                                   match uu____17617 with
                                   | (env2, tpars1) ->
                                       let uu____17648 =
                                         push_tparams env2 tpars1 in
                                       (match uu____17648 with
                                        | (env_tps, tpars2) ->
                                            let t1 = desugar_typ env_tps t in
                                            let tpars3 =
                                              FStar_Syntax_Subst.close_binders
                                                tpars2 in
                                            FStar_Syntax_Subst.close tpars3
                                              t1) in
                                 let uu____17681 =
                                   let uu____17702 =
                                     mk_typ_abbrev id1 uvs tpars k t1 
                                       [id1] quals1 rng in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____17702) in
                                 [uu____17681]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname, univs1, tpars, k, mutuals1,
                                       uu____17770);
                                    FStar_Syntax_Syntax.sigrng = uu____17771;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____17773;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____17774;_},
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
                                 let uu____17872 = push_tparams env1 tpars in
                                 (match uu____17872 with
                                  | (env_tps, tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____17949 ->
                                             match uu____17949 with
                                             | (x, uu____17963) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps in
                                      let tot_tconstr = mk_tot tconstr in
                                      let uu____17971 =
                                        let uu____18000 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____18114 ->
                                                  match uu____18114 with
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
                                                        let uu____18170 =
                                                          close env_tps t in
                                                        desugar_term env_tps
                                                          uu____18170 in
                                                      let name =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env1 id1 in
                                                      let quals2 =
                                                        FStar_All.pipe_right
                                                          tname_quals
                                                          (FStar_List.collect
                                                             (fun
                                                                uu___105_18181
                                                                ->
                                                                match uu___105_18181
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____18193
                                                                    -> [])) in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars in
                                                      let uu____18201 =
                                                        let uu____18222 =
                                                          let uu____18223 =
                                                            let uu____18224 =
                                                              let uu____18239
                                                                =
                                                                let uu____18242
                                                                  =
                                                                  let uu____18245
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____18245 in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____18242 in
                                                              (name, univs1,
                                                                uu____18239,
                                                                tname, ntps,
                                                                mutuals1) in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____18224 in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____18223;
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
                                                          uu____18222) in
                                                      (name, uu____18201))) in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____18000 in
                                      (match uu____17971 with
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
                             | uu____18484 -> failwith "impossible")) in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____18616 ->
                             match uu____18616 with
                             | (name_doc, uu____18644, uu____18645) ->
                                 name_doc)) in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____18725 ->
                             match uu____18725 with
                             | (uu____18746, uu____18747, se) -> se)) in
                   let uu____18777 =
                     let uu____18784 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____18784 rng in
                   (match uu____18777 with
                    | (bundle, abbrevs) ->
                        let env2 = FStar_Syntax_DsEnv.push_sigelt env0 bundle in
                        let env3 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env2 abbrevs in
                        let data_ops =
                          FStar_All.pipe_right docs_tps_sigelts
                            (FStar_List.collect
                               (fun uu____18850 ->
                                  match uu____18850 with
                                  | (uu____18873, tps, se) ->
                                      mk_data_projector_names quals env3 se)) in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname, uu____18924, tps, k,
                                       uu____18927, constrs)
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
                                  | uu____18946 -> [])) in
                        let ops = FStar_List.append discs data_ops in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc ->
                               fun uu____18963 ->
                                 match uu____18963 with
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
      let uu____19002 =
        FStar_List.fold_left
          (fun uu____19025 ->
             fun b ->
               match uu____19025 with
               | (env1, binders1) ->
                   let uu____19045 = desugar_binder env1 b in
                   (match uu____19045 with
                    | (FStar_Pervasives_Native.Some a, k) ->
                        let uu____19062 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k) in
                        (match uu____19062 with
                         | (binder, env2) -> (env2, (binder :: binders1)))
                    | uu____19079 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders in
      match uu____19002 with
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
          let uu____19132 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___107_19137 ->
                    match uu___107_19137 with
                    | FStar_Syntax_Syntax.Reflectable uu____19138 -> true
                    | uu____19139 -> false)) in
          if uu____19132
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident in
            let reflect_lid =
              let uu____19142 = FStar_Ident.id_of_text "reflect" in
              FStar_All.pipe_right uu____19142
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
let (get_fail_attr :
  Prims.bool ->
    FStar_Syntax_Syntax.term ->
      Prims.int Prims.list FStar_Pervasives_Native.option)
  =
  fun warn ->
    fun at1 ->
      let uu____19168 = FStar_Syntax_Util.head_and_args at1 in
      match uu____19168 with
      | (hd1, args) ->
          let uu____19209 =
            let uu____19222 =
              let uu____19223 = FStar_Syntax_Subst.compress hd1 in
              uu____19223.FStar_Syntax_Syntax.n in
            (uu____19222, args) in
          (match uu____19209 with
           | (FStar_Syntax_Syntax.Tm_fvar fv, (a1, uu____19240)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.fail_errs_attr
               ->
               let uu____19265 =
                 let uu____19270 =
                   FStar_Syntax_Embeddings.e_list
                     FStar_Syntax_Embeddings.e_int in
                 FStar_Syntax_Embeddings.unembed uu____19270 a1 in
               FStar_Util.map_opt uu____19265
                 (FStar_List.map FStar_BigInt.to_int_fs)
           | (FStar_Syntax_Syntax.Tm_fvar fv, uu____19282) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.fail_errs_attr
               ->
               (if warn
                then
                  FStar_Errors.log_issue at1.FStar_Syntax_Syntax.pos
                    (FStar_Errors.Warning_UnappliedFail,
                      "Found ill-applied fail_errs, did you forget to use parentheses?")
                else ();
                FStar_Pervasives_Native.None)
           | uu____19303 ->
               let uu____19316 =
                 FStar_Syntax_Util.attr_eq at1 FStar_Syntax_Util.fail_attr in
               if uu____19316
               then FStar_Pervasives_Native.Some []
               else FStar_Pervasives_Native.None)
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
                  let uu____19464 = desugar_binders monad_env eff_binders in
                  match uu____19464 with
                  | (env1, binders) ->
                      let eff_t = desugar_term env1 eff_typ in
                      let for_free =
                        let uu____19485 =
                          let uu____19486 =
                            let uu____19493 =
                              FStar_Syntax_Util.arrow_formals eff_t in
                            FStar_Pervasives_Native.fst uu____19493 in
                          FStar_List.length uu____19486 in
                        uu____19485 = (Prims.parse_int "1") in
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
                            (uu____19537,
                             (FStar_Parser_AST.TyconAbbrev
                              (name, uu____19539, uu____19540, uu____19541),
                              uu____19542)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____19575 ->
                            failwith "Malformed effect member declaration." in
                      let uu____19576 =
                        FStar_List.partition
                          (fun decl ->
                             let uu____19588 = name_of_eff_decl decl in
                             FStar_List.mem uu____19588 mandatory_members)
                          eff_decls in
                      (match uu____19576 with
                       | (mandatory_members_decls, actions) ->
                           let uu____19605 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____19634 ->
                                     fun decl ->
                                       match uu____19634 with
                                       | (env2, out) ->
                                           let uu____19654 =
                                             desugar_decl env2 decl in
                                           (match uu____19654 with
                                            | (env3, ses) ->
                                                let uu____19667 =
                                                  let uu____19670 =
                                                    FStar_List.hd ses in
                                                  uu____19670 :: out in
                                                (env3, uu____19667)))
                                  (env1, [])) in
                           (match uu____19605 with
                            | (env2, decls) ->
                                let binders1 =
                                  FStar_Syntax_Subst.close_binders binders in
                                let actions_docs =
                                  FStar_All.pipe_right actions
                                    (FStar_List.map
                                       (fun d1 ->
                                          match d1.FStar_Parser_AST.d with
                                          | FStar_Parser_AST.Tycon
                                              (uu____19738,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name, action_params,
                                                 uu____19741,
                                                 {
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.Construct
                                                     (uu____19742,
                                                      (def, uu____19744)::
                                                      (cps_type, uu____19746)::[]);
                                                   FStar_Parser_AST.range =
                                                     uu____19747;
                                                   FStar_Parser_AST.level =
                                                     uu____19748;_}),
                                                doc1)::[])
                                              when Prims.op_Negation for_free
                                              ->
                                              let uu____19800 =
                                                desugar_binders env2
                                                  action_params in
                                              (match uu____19800 with
                                               | (env3, action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1 in
                                                   let uu____19820 =
                                                     let uu____19821 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name in
                                                     let uu____19822 =
                                                       let uu____19823 =
                                                         desugar_term env3
                                                           def in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____19823 in
                                                     let uu____19828 =
                                                       let uu____19829 =
                                                         desugar_typ env3
                                                           cps_type in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____19829 in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____19821;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____19822;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____19828
                                                     } in
                                                   (uu____19820, doc1))
                                          | FStar_Parser_AST.Tycon
                                              (uu____19836,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name, action_params,
                                                 uu____19839, defn),
                                                doc1)::[])
                                              when for_free ->
                                              let uu____19874 =
                                                desugar_binders env2
                                                  action_params in
                                              (match uu____19874 with
                                               | (env3, action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1 in
                                                   let uu____19894 =
                                                     let uu____19895 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name in
                                                     let uu____19896 =
                                                       let uu____19897 =
                                                         desugar_term env3
                                                           defn in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____19897 in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____19895;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____19896;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     } in
                                                   (uu____19894, doc1))
                                          | uu____19904 ->
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
                                    let uu____19936 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange)) in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____19936 in
                                  let uu____19937 =
                                    let uu____19938 =
                                      FStar_Syntax_DsEnv.fail_or env2
                                        (FStar_Syntax_DsEnv.try_lookup_definition
                                           env2) l in
                                    FStar_All.pipe_left
                                      (FStar_Syntax_Subst.close binders1)
                                      uu____19938 in
                                  ([], uu____19937) in
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
                                      let uu____19955 =
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange in
                                      ([], uu____19955) in
                                    let uu____19962 =
                                      let uu____19963 =
                                        let uu____19964 =
                                          let uu____19965 = lookup1 "repr" in
                                          FStar_Pervasives_Native.snd
                                            uu____19965 in
                                        let uu____19974 = lookup1 "return" in
                                        let uu____19975 = lookup1 "bind" in
                                        let uu____19976 =
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
                                            uu____19964;
                                          FStar_Syntax_Syntax.return_repr =
                                            uu____19974;
                                          FStar_Syntax_Syntax.bind_repr =
                                            uu____19975;
                                          FStar_Syntax_Syntax.actions =
                                            actions1;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            uu____19976
                                        } in
                                      FStar_Syntax_Syntax.Sig_new_effect_for_free
                                        uu____19963 in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____19962;
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
                                         (fun uu___108_19982 ->
                                            match uu___108_19982 with
                                            | FStar_Syntax_Syntax.Reifiable
                                                -> true
                                            | FStar_Syntax_Syntax.Reflectable
                                                uu____19983 -> true
                                            | uu____19984 -> false)
                                         qualifiers in
                                     let un_ts =
                                       ([], FStar_Syntax_Syntax.tun) in
                                     let uu____19994 =
                                       let uu____19995 =
                                         let uu____19996 =
                                           lookup1 "return_wp" in
                                         let uu____19997 = lookup1 "bind_wp" in
                                         let uu____19998 =
                                           lookup1 "if_then_else" in
                                         let uu____19999 = lookup1 "ite_wp" in
                                         let uu____20000 = lookup1 "stronger" in
                                         let uu____20001 = lookup1 "close_wp" in
                                         let uu____20002 = lookup1 "assert_p" in
                                         let uu____20003 = lookup1 "assume_p" in
                                         let uu____20004 = lookup1 "null_wp" in
                                         let uu____20005 = lookup1 "trivial" in
                                         let uu____20006 =
                                           if rr
                                           then
                                             let uu____20007 = lookup1 "repr" in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.snd
                                               uu____20007
                                           else FStar_Syntax_Syntax.tun in
                                         let uu____20023 =
                                           if rr
                                           then lookup1 "return"
                                           else un_ts in
                                         let uu____20025 =
                                           if rr
                                           then lookup1 "bind"
                                           else un_ts in
                                         let uu____20027 =
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
                                             uu____19996;
                                           FStar_Syntax_Syntax.bind_wp =
                                             uu____19997;
                                           FStar_Syntax_Syntax.if_then_else =
                                             uu____19998;
                                           FStar_Syntax_Syntax.ite_wp =
                                             uu____19999;
                                           FStar_Syntax_Syntax.stronger =
                                             uu____20000;
                                           FStar_Syntax_Syntax.close_wp =
                                             uu____20001;
                                           FStar_Syntax_Syntax.assert_p =
                                             uu____20002;
                                           FStar_Syntax_Syntax.assume_p =
                                             uu____20003;
                                           FStar_Syntax_Syntax.null_wp =
                                             uu____20004;
                                           FStar_Syntax_Syntax.trivial =
                                             uu____20005;
                                           FStar_Syntax_Syntax.repr =
                                             uu____20006;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____20023;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____20025;
                                           FStar_Syntax_Syntax.actions =
                                             actions1;
                                           FStar_Syntax_Syntax.eff_attrs =
                                             uu____20027
                                         } in
                                       FStar_Syntax_Syntax.Sig_new_effect
                                         uu____19995 in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         uu____19994;
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
                                          fun uu____20053 ->
                                            match uu____20053 with
                                            | (a, doc1) ->
                                                let env6 =
                                                  let uu____20067 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____20067 in
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
                let uu____20093 = desugar_binders env1 eff_binders in
                match uu____20093 with
                | (env2, binders) ->
                    let uu____20112 =
                      let uu____20131 = head_and_args defn in
                      match uu____20131 with
                      | (head1, args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____20176 ->
                                let uu____20177 =
                                  let uu____20182 =
                                    let uu____20183 =
                                      let uu____20184 =
                                        FStar_Parser_AST.term_to_string head1 in
                                      Prims.strcat uu____20184 " not found" in
                                    Prims.strcat "Effect " uu____20183 in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____20182) in
                                FStar_Errors.raise_error uu____20177
                                  d.FStar_Parser_AST.drange in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid in
                          let uu____20186 =
                            match FStar_List.rev args with
                            | (last_arg, uu____20216)::args_rev ->
                                let uu____20228 =
                                  let uu____20229 = unparen last_arg in
                                  uu____20229.FStar_Parser_AST.tm in
                                (match uu____20228 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____20257 -> ([], args))
                            | uu____20266 -> ([], args) in
                          (match uu____20186 with
                           | (cattributes, args1) ->
                               let uu____20317 = desugar_args env2 args1 in
                               let uu____20326 =
                                 desugar_attributes env2 cattributes in
                               (lid, ed, uu____20317, uu____20326)) in
                    (match uu____20112 with
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
                          (let uu____20382 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit in
                           match uu____20382 with
                           | (ed_binders, uu____20396, ed_binders_opening) ->
                               let sub1 uu____20409 =
                                 match uu____20409 with
                                 | (us, x) ->
                                     let x1 =
                                       let uu____20423 =
                                         FStar_Syntax_Subst.shift_subst
                                           (FStar_List.length us)
                                           ed_binders_opening in
                                       FStar_Syntax_Subst.subst uu____20423 x in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args in
                                     let uu____20427 =
                                       let uu____20428 =
                                         FStar_Syntax_Subst.subst s x1 in
                                       (us, uu____20428) in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____20427 in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name in
                               let ed1 =
                                 let uu____20433 =
                                   let uu____20434 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature)) in
                                   FStar_Pervasives_Native.snd uu____20434 in
                                 let uu____20445 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp in
                                 let uu____20446 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp in
                                 let uu____20447 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else in
                                 let uu____20448 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp in
                                 let uu____20449 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger in
                                 let uu____20450 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp in
                                 let uu____20451 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p in
                                 let uu____20452 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p in
                                 let uu____20453 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp in
                                 let uu____20454 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial in
                                 let uu____20455 =
                                   let uu____20456 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr)) in
                                   FStar_Pervasives_Native.snd uu____20456 in
                                 let uu____20467 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr in
                                 let uu____20468 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr in
                                 let uu____20469 =
                                   FStar_List.map
                                     (fun action ->
                                        let uu____20477 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name in
                                        let uu____20478 =
                                          let uu____20479 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn)) in
                                          FStar_Pervasives_Native.snd
                                            uu____20479 in
                                        let uu____20490 =
                                          let uu____20491 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ)) in
                                          FStar_Pervasives_Native.snd
                                            uu____20491 in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____20477;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____20478;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____20490
                                        }) ed.FStar_Syntax_Syntax.actions in
                                 {
                                   FStar_Syntax_Syntax.cattributes =
                                     cattributes;
                                   FStar_Syntax_Syntax.mname = mname;
                                   FStar_Syntax_Syntax.univs =
                                     (ed.FStar_Syntax_Syntax.univs);
                                   FStar_Syntax_Syntax.binders = binders1;
                                   FStar_Syntax_Syntax.signature =
                                     uu____20433;
                                   FStar_Syntax_Syntax.ret_wp = uu____20445;
                                   FStar_Syntax_Syntax.bind_wp = uu____20446;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____20447;
                                   FStar_Syntax_Syntax.ite_wp = uu____20448;
                                   FStar_Syntax_Syntax.stronger = uu____20449;
                                   FStar_Syntax_Syntax.close_wp = uu____20450;
                                   FStar_Syntax_Syntax.assert_p = uu____20451;
                                   FStar_Syntax_Syntax.assume_p = uu____20452;
                                   FStar_Syntax_Syntax.null_wp = uu____20453;
                                   FStar_Syntax_Syntax.trivial = uu____20454;
                                   FStar_Syntax_Syntax.repr = uu____20455;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____20467;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____20468;
                                   FStar_Syntax_Syntax.actions = uu____20469;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 } in
                               let se =
                                 let for_free =
                                   let uu____20504 =
                                     let uu____20505 =
                                       let uu____20512 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature in
                                       FStar_Pervasives_Native.fst
                                         uu____20512 in
                                     FStar_List.length uu____20505 in
                                   uu____20504 = (Prims.parse_int "1") in
                                 let uu____20541 =
                                   let uu____20544 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname) in
                                   FStar_List.collect uu____20544 quals in
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
                                   FStar_Syntax_Syntax.sigquals = uu____20541;
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
                                             let uu____20568 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____20568 in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4) in
                               let env6 =
                                 let uu____20570 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable) in
                                 if uu____20570
                                 then
                                   let reflect_lid =
                                     let uu____20574 =
                                       FStar_Ident.id_of_text "reflect" in
                                     FStar_All.pipe_right uu____20574
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
    let uu____20586 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc in
    match uu____20586 with
    | (text, kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.strcat "  " (Prims.strcat s "\n") in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____20637 ->
              let uu____20638 =
                let uu____20639 =
                  FStar_Parser_ToDocument.signature_to_document d in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____20639 in
              Prims.strcat "\n  " uu____20638
          | uu____20640 -> "" in
        let other =
          FStar_List.filter_map
            (fun uu____20653 ->
               match uu____20653 with
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
          let uu____20671 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment" in
          FStar_Syntax_Syntax.fvar uu____20671
            FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
        let arg = FStar_Syntax_Util.exp_string str in
        let uu____20673 =
          let uu____20682 = FStar_Syntax_Syntax.as_arg arg in [uu____20682] in
        FStar_Syntax_Util.mk_app fv uu____20673
and (desugar_decl :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t, FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun d ->
      let uu____20689 = desugar_decl_noattrs env d in
      match uu____20689 with
      | (env1, sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs in
          let attrs1 = FStar_List.map (desugar_term env1) attrs in
          let attrs2 =
            let uu____20709 = mk_comment_attr d in uu____20709 :: attrs1 in
          let uu____20714 =
            FStar_List.mapi
              (fun i ->
                 fun sigelt ->
                   if i = (Prims.parse_int "0")
                   then
                     let uu___135_20722 = sigelt in
                     {
                       FStar_Syntax_Syntax.sigel =
                         (uu___135_20722.FStar_Syntax_Syntax.sigel);
                       FStar_Syntax_Syntax.sigrng =
                         (uu___135_20722.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___135_20722.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___135_20722.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs = attrs2
                     }
                   else
                     (let uu___136_20724 = sigelt in
                      let uu____20725 =
                        FStar_List.filter
                          (fun at1 ->
                             let uu____20731 = get_fail_attr false at1 in
                             FStar_Option.isNone uu____20731) attrs2 in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___136_20724.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___136_20724.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___136_20724.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___136_20724.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs = uu____20725
                      })) sigelts in
          (env1, uu____20714)
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
      | FStar_Parser_AST.Fsdoc uu____20769 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x, l) ->
          let uu____20785 = FStar_Syntax_DsEnv.push_module_abbrev env x l in
          (uu____20785, [])
      | FStar_Parser_AST.Tycon (is_effect, tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals in
          let tcs1 =
            FStar_List.map
              (fun uu____20824 ->
                 match uu____20824 with | (x, uu____20832) -> x) tcs in
          let uu____20837 =
            FStar_List.collect (trans_qual1 FStar_Pervasives_Native.None)
              quals in
          desugar_tycon env d uu____20837 tcs1
      | FStar_Parser_AST.TopLevelLet (isrec, lets) ->
          let quals = d.FStar_Parser_AST.quals in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____20859;
                    FStar_Parser_AST.prange = uu____20860;_},
                  uu____20861)::[] -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____20870;
                    FStar_Parser_AST.prange = uu____20871;_},
                  uu____20872)::[] -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____20887;
                         FStar_Parser_AST.prange = uu____20888;_},
                       uu____20889);
                    FStar_Parser_AST.prange = uu____20890;_},
                  uu____20891)::[] -> false
               | (p, uu____20919)::[] ->
                   let uu____20928 = is_app_pattern p in
                   Prims.op_Negation uu____20928
               | uu____20929 -> false) in
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
            let uu____21002 = desugar_term_maybe_top true env as_inner_let in
            (match uu____21002 with
             | (ds_lets, aq) ->
                 (check_no_aq aq;
                  (let uu____21014 =
                     let uu____21015 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets in
                     uu____21015.FStar_Syntax_Syntax.n in
                   match uu____21014 with
                   | FStar_Syntax_Syntax.Tm_let (lbs, uu____21023) ->
                       let fvs =
                         FStar_All.pipe_right
                           (FStar_Pervasives_Native.snd lbs)
                           (FStar_List.map
                              (fun lb ->
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname)) in
                       let quals1 =
                         match quals with
                         | uu____21056::uu____21057 ->
                             FStar_List.collect
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____21060 ->
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.collect
                                  (fun uu___109_21075 ->
                                     match uu___109_21075 with
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inl uu____21078;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____21079;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____21080;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____21081;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____21082;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____21083;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____21084;_}
                                         -> []
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____21096;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____21097;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____21098;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____21099;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____21100;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____21101;_}
                                         ->
                                         FStar_Syntax_DsEnv.lookup_letbinding_quals
                                           env
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)) in
                       let lbs1 =
                         let uu____21119 =
                           FStar_All.pipe_right quals1
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract) in
                         if uu____21119
                         then
                           let uu____21128 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname in
                                     let uu___137_21142 = lb in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___138_21144 = fv in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___138_21144.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___138_21144.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___137_21142.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___137_21142.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___137_21142.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___137_21142.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___137_21142.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___137_21142.FStar_Syntax_Syntax.lbpos)
                                     })) in
                           ((FStar_Pervasives_Native.fst lbs), uu____21128)
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
                   | uu____21179 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____21185 =
               match lets with
               | (pat, body)::[] -> (pat, body)
               | uu____21204 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets" in
             match uu____21185 with
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
                       let uu___139_21240 = pat1 in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___139_21240.FStar_Parser_AST.prange)
                       }
                   | uu____21247 -> var_pat in
                 let main_let =
                   desugar_decl env
                     (let uu___140_21254 = d in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___140_21254.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___140_21254.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___140_21254.FStar_Parser_AST.attrs)
                      }) in
                 let build_projection uu____21290 id1 =
                   match uu____21290 with
                   | (env1, ses) ->
                       let main =
                         let uu____21311 =
                           let uu____21312 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name] in
                           FStar_Parser_AST.Var uu____21312 in
                         FStar_Parser_AST.mk_term uu____21311
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
                       let uu____21362 = desugar_decl env1 id_decl in
                       (match uu____21362 with
                        | (env2, ses') ->
                            (env2, (FStar_List.append ses ses'))) in
                 let bvs =
                   let uu____21380 = gather_pattern_bound_vars pat in
                   FStar_All.pipe_right uu____21380 FStar_Util.set_elements in
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
            let uu____21411 = close_fun env t in desugar_term env uu____21411 in
          let quals1 =
            let uu____21415 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env) in
            if uu____21415
            then FStar_Parser_AST.Assumption :: quals
            else quals in
          let lid = FStar_Syntax_DsEnv.qualify env id1 in
          let se =
            let uu____21421 =
              FStar_List.collect (trans_qual1 FStar_Pervasives_Native.None)
                quals1 in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____21421;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            } in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se in
          let env2 =
            FStar_Syntax_DsEnv.push_doc env1 lid d.FStar_Parser_AST.doc in
          (env2, [se])
      | FStar_Parser_AST.Exception (id1, FStar_Pervasives_Native.None) ->
          let uu____21433 =
            FStar_Syntax_DsEnv.fail_or env
              (FStar_Syntax_DsEnv.try_lookup_lid env)
              FStar_Parser_Const.exn_lid in
          (match uu____21433 with
           | (t, uu____21447) ->
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
            let uu____21481 =
              let uu____21488 = FStar_Syntax_Syntax.null_binder t in
              [uu____21488] in
            let uu____21489 =
              let uu____21492 =
                let uu____21493 =
                  FStar_Syntax_DsEnv.fail_or env
                    (FStar_Syntax_DsEnv.try_lookup_lid env)
                    FStar_Parser_Const.exn_lid in
                FStar_Pervasives_Native.fst uu____21493 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____21492 in
            FStar_Syntax_Util.arrow uu____21481 uu____21489 in
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
            let uu____21558 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1 in
            match uu____21558 with
            | FStar_Pervasives_Native.None ->
                let uu____21561 =
                  let uu____21566 =
                    let uu____21567 =
                      let uu____21568 = FStar_Syntax_Print.lid_to_string l1 in
                      Prims.strcat uu____21568 " not found" in
                    Prims.strcat "Effect name " uu____21567 in
                  (FStar_Errors.Fatal_EffectNotFound, uu____21566) in
                FStar_Errors.raise_error uu____21561
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2 in
          let src = lookup1 l.FStar_Parser_AST.msource in
          let dst = lookup1 l.FStar_Parser_AST.mdest in
          let uu____21572 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____21614 =
                  let uu____21623 =
                    let uu____21630 = desugar_term env t in ([], uu____21630) in
                  FStar_Pervasives_Native.Some uu____21623 in
                (uu____21614, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp, t) ->
                let uu____21663 =
                  let uu____21672 =
                    let uu____21679 = desugar_term env wp in
                    ([], uu____21679) in
                  FStar_Pervasives_Native.Some uu____21672 in
                let uu____21688 =
                  let uu____21697 =
                    let uu____21704 = desugar_term env t in ([], uu____21704) in
                  FStar_Pervasives_Native.Some uu____21697 in
                (uu____21663, uu____21688)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____21730 =
                  let uu____21739 =
                    let uu____21746 = desugar_term env t in ([], uu____21746) in
                  FStar_Pervasives_Native.Some uu____21739 in
                (FStar_Pervasives_Native.None, uu____21730) in
          (match uu____21572 with
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
      | FStar_Parser_AST.Splice (ids, t) ->
          let t1 = desugar_term env t in
          let se =
            let uu____21826 =
              let uu____21827 =
                let uu____21834 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids in
                (uu____21834, t1) in
              FStar_Syntax_Syntax.Sig_splice uu____21827 in
            {
              FStar_Syntax_Syntax.sigel = uu____21826;
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = [];
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            } in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se in (env1, [se])
let (desugar_decls :
  env_t ->
    FStar_Parser_AST.decl Prims.list ->
      (env_t, FStar_Syntax_Syntax.sigelt Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun decls ->
      let uu____21862 =
        FStar_List.fold_left
          (fun uu____21882 ->
             fun d ->
               match uu____21882 with
               | (env1, sigelts) ->
                   let uu____21902 = desugar_decl env1 d in
                   (match uu____21902 with
                    | (env2, se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls in
      match uu____21862 with
      | (env1, sigelts) ->
          let rec forward acc uu___111_21947 =
            match uu___111_21947 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ uu____21961,
                    FStar_Syntax_Syntax.Sig_let uu____21962) ->
                     let uu____21975 =
                       let uu____21978 =
                         let uu___141_21979 = se2 in
                         let uu____21980 =
                           let uu____21983 =
                             FStar_List.filter
                               (fun uu___110_21997 ->
                                  match uu___110_21997 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____22001;
                                           FStar_Syntax_Syntax.vars =
                                             uu____22002;_},
                                         uu____22003);
                                      FStar_Syntax_Syntax.pos = uu____22004;
                                      FStar_Syntax_Syntax.vars = uu____22005;_}
                                      when
                                      let uu____22028 =
                                        let uu____22029 =
                                          FStar_Syntax_Syntax.lid_of_fv fv in
                                        FStar_Ident.string_of_lid uu____22029 in
                                      uu____22028 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____22030 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs in
                           FStar_List.append uu____21983
                             se2.FStar_Syntax_Syntax.sigattrs in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___141_21979.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___141_21979.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___141_21979.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___141_21979.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____21980
                         } in
                       uu____21978 :: se1 :: acc in
                     forward uu____21975 sigelts1
                 | uu____22035 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1 in
          let uu____22043 = forward [] sigelts in (env1, uu____22043)
let (open_prims_all :
  (FStar_Parser_AST.decoration Prims.list -> FStar_Parser_AST.decl)
    Prims.list)
  =
  [FStar_Parser_AST.mk_decl
     (FStar_Parser_AST.Open FStar_Parser_Const.prims_lid)
     FStar_Range.dummyRange;
  FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open FStar_Parser_Const.all_lid)
    FStar_Range.dummyRange]
let (generalize_annotated_univs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun s ->
    let bs_univnames bs =
      let uu____22085 =
        let uu____22092 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name in
        FStar_List.fold_left
          (fun uvs ->
             fun uu____22109 ->
               match uu____22109 with
               | ({ FStar_Syntax_Syntax.ppname = uu____22118;
                    FStar_Syntax_Syntax.index = uu____22119;
                    FStar_Syntax_Syntax.sort = t;_},
                  uu____22121) ->
                   let uu____22124 = FStar_Syntax_Free.univnames t in
                   FStar_Util.set_union uvs uu____22124) uu____22092 in
      FStar_All.pipe_right bs uu____22085 in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____22132 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____22149 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs, lids) ->
        let uvs =
          let uu____22177 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs ->
                    fun se ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____22198, uu____22199, bs, t, uu____22202,
                             uu____22203)
                            ->
                            let uu____22212 = bs_univnames bs in
                            let uu____22215 = FStar_Syntax_Free.univnames t in
                            FStar_Util.set_union uu____22212 uu____22215
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____22218, uu____22219, t, uu____22221,
                             uu____22222, uu____22223)
                            -> FStar_Syntax_Free.univnames t
                        | uu____22228 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt" in
                      FStar_Util.set_union uvs se_univs) empty_set) in
          FStar_All.pipe_right uu____22177 FStar_Util.set_elements in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs in
        let uu___142_22238 = s in
        let uu____22239 =
          let uu____22240 =
            let uu____22249 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid, uu____22267, bs, t, lids1, lids2) ->
                          let uu___143_22280 = se in
                          let uu____22281 =
                            let uu____22282 =
                              let uu____22299 =
                                FStar_Syntax_Subst.subst_binders usubst bs in
                              let uu____22300 =
                                let uu____22301 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst in
                                FStar_Syntax_Subst.subst uu____22301 t in
                              (lid, uvs, uu____22299, uu____22300, lids1,
                                lids2) in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____22282 in
                          {
                            FStar_Syntax_Syntax.sigel = uu____22281;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___143_22280.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___143_22280.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___143_22280.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___143_22280.FStar_Syntax_Syntax.sigattrs)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid, uu____22315, t, tlid, n1, lids1) ->
                          let uu___144_22324 = se in
                          let uu____22325 =
                            let uu____22326 =
                              let uu____22341 =
                                FStar_Syntax_Subst.subst usubst t in
                              (lid, uvs, uu____22341, tlid, n1, lids1) in
                            FStar_Syntax_Syntax.Sig_datacon uu____22326 in
                          {
                            FStar_Syntax_Syntax.sigel = uu____22325;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___144_22324.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___144_22324.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___144_22324.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___144_22324.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____22346 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt")) in
            (uu____22249, lids) in
          FStar_Syntax_Syntax.Sig_bundle uu____22240 in
        {
          FStar_Syntax_Syntax.sigel = uu____22239;
          FStar_Syntax_Syntax.sigrng =
            (uu___142_22238.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___142_22238.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___142_22238.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___142_22238.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____22352, t) ->
        let uvs =
          let uu____22357 = FStar_Syntax_Free.univnames t in
          FStar_All.pipe_right uu____22357 FStar_Util.set_elements in
        let uu___145_22364 = s in
        let uu____22365 =
          let uu____22366 =
            let uu____22373 = FStar_Syntax_Subst.close_univ_vars uvs t in
            (lid, uvs, uu____22373) in
          FStar_Syntax_Syntax.Sig_declare_typ uu____22366 in
        {
          FStar_Syntax_Syntax.sigel = uu____22365;
          FStar_Syntax_Syntax.sigrng =
            (uu___145_22364.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___145_22364.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___145_22364.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___145_22364.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_let ((b, lbs), lids) ->
        let lb_univnames lb =
          let uu____22403 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp in
          let uu____22406 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs, e, uu____22413) ->
                let uvs1 = bs_univnames bs in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____22442, (FStar_Util.Inl t, uu____22444),
                       uu____22445)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____22492, (FStar_Util.Inr c, uu____22494),
                       uu____22495)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____22542 -> empty_set in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____22543, (FStar_Util.Inl t, uu____22545), uu____22546)
                -> FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____22593, (FStar_Util.Inr c, uu____22595), uu____22596)
                -> FStar_Syntax_Free.univnames_comp c
            | uu____22643 -> empty_set in
          FStar_Util.set_union uu____22403 uu____22406 in
        let all_lb_univs =
          let uu____22647 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs ->
                    fun lb ->
                      let uu____22663 = lb_univnames lb in
                      FStar_Util.set_union uvs uu____22663) empty_set) in
          FStar_All.pipe_right uu____22647 FStar_Util.set_elements in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs in
        let uu___146_22673 = s in
        let uu____22674 =
          let uu____22675 =
            let uu____22682 =
              let uu____22689 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb ->
                        let uu___147_22701 = lb in
                        let uu____22702 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp in
                        let uu____22705 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___147_22701.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____22702;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___147_22701.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____22705;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___147_22701.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___147_22701.FStar_Syntax_Syntax.lbpos)
                        })) in
              (b, uu____22689) in
            (uu____22682, lids) in
          FStar_Syntax_Syntax.Sig_let uu____22675 in
        {
          FStar_Syntax_Syntax.sigel = uu____22674;
          FStar_Syntax_Syntax.sigrng =
            (uu___146_22673.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___146_22673.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___146_22673.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___146_22673.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid, uu____22719, fml) ->
        let uvs =
          let uu____22724 = FStar_Syntax_Free.univnames fml in
          FStar_All.pipe_right uu____22724 FStar_Util.set_elements in
        let uu___148_22731 = s in
        let uu____22732 =
          let uu____22733 =
            let uu____22740 = FStar_Syntax_Subst.close_univ_vars uvs fml in
            (lid, uvs, uu____22740) in
          FStar_Syntax_Syntax.Sig_assume uu____22733 in
        {
          FStar_Syntax_Syntax.sigel = uu____22732;
          FStar_Syntax_Syntax.sigrng =
            (uu___148_22731.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___148_22731.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___148_22731.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___148_22731.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uu____22744, bs, c, flags1)
        ->
        let uvs =
          let uu____22755 =
            let uu____22758 = bs_univnames bs in
            let uu____22761 = FStar_Syntax_Free.univnames_comp c in
            FStar_Util.set_union uu____22758 uu____22761 in
          FStar_All.pipe_right uu____22755 FStar_Util.set_elements in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs in
        let uu___149_22771 = s in
        let uu____22772 =
          let uu____22773 =
            let uu____22786 = FStar_Syntax_Subst.subst_binders usubst bs in
            let uu____22787 = FStar_Syntax_Subst.subst_comp usubst c in
            (lid, uvs, uu____22786, uu____22787, flags1) in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____22773 in
        {
          FStar_Syntax_Syntax.sigel = uu____22772;
          FStar_Syntax_Syntax.sigrng =
            (uu___149_22771.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___149_22771.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___149_22771.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___149_22771.FStar_Syntax_Syntax.sigattrs)
        }
    | uu____22792 -> s
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
          | (FStar_Pervasives_Native.None, uu____22827) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____22831;
               FStar_Syntax_Syntax.exports = uu____22832;
               FStar_Syntax_Syntax.is_interface = uu____22833;_},
             FStar_Parser_AST.Module (current_lid, uu____22835)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod, uu____22843) ->
              let uu____22846 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod in
              FStar_Pervasives_Native.fst uu____22846 in
        let uu____22851 =
          match m with
          | FStar_Parser_AST.Interface (mname, decls, admitted) ->
              let uu____22887 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii in
              (uu____22887, mname, decls, true)
          | FStar_Parser_AST.Module (mname, decls) ->
              let uu____22904 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii in
              (uu____22904, mname, decls, false) in
        match uu____22851 with
        | ((env2, pop_when_done), mname, decls, intf) ->
            let uu____22934 = desugar_decls env2 decls in
            (match uu____22934 with
             | (env3, sigelts) ->
                 let sigelts1 =
                   FStar_All.pipe_right sigelts
                     (FStar_List.map generalize_annotated_univs) in
                 let modul =
                   {
                     FStar_Syntax_Syntax.name = mname;
                     FStar_Syntax_Syntax.declarations = sigelts1;
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
          let uu____23003 =
            (FStar_Options.interactive ()) &&
              (let uu____23005 =
                 let uu____23006 =
                   let uu____23007 = FStar_Options.file_list () in
                   FStar_List.hd uu____23007 in
                 FStar_Util.get_file_extension uu____23006 in
               FStar_List.mem uu____23005 ["fsti"; "fsi"]) in
          if uu____23003 then as_interface m else m in
        let uu____23011 = desugar_modul_common curmod env m1 in
        match uu____23011 with
        | (x, y, pop_when_done) ->
            (if pop_when_done
             then (let uu____23026 = FStar_Syntax_DsEnv.pop () in ())
             else ();
             (x, y))
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul ->
      (env_t, FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2)
  =
  fun env ->
    fun m ->
      let uu____23046 =
        desugar_modul_common FStar_Pervasives_Native.None env m in
      match uu____23046 with
      | (env1, modul, pop_when_done) ->
          let uu____23060 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul in
          (match uu____23060 with
           | (env2, modul1) ->
               ((let uu____23072 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str in
                 if uu____23072
                 then
                   let uu____23073 =
                     FStar_Syntax_Print.modul_to_string modul1 in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____23073
                 else ());
                (let uu____23075 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2 in
                 (uu____23075, modul1))))
let (ast_modul_to_modul :
  FStar_Parser_AST.modul ->
    FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul ->
    fun env ->
      let uu____23093 = desugar_modul env modul in
      match uu____23093 with | (env1, modul1) -> (modul1, env1)
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls ->
    fun env ->
      let uu____23124 = desugar_decls env decls in
      match uu____23124 with | (env1, sigelts) -> (sigelts, env1)
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul ->
    fun a_modul ->
      fun env ->
        let uu____23168 = desugar_partial_modul modul env a_modul in
        match uu____23168 with | (env1, modul1) -> (modul1, env1)
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
              | uu____23254 ->
                  let t =
                    let uu____23262 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange in
                    erase_univs uu____23262 in
                  let uu____23271 =
                    let uu____23272 = FStar_Syntax_Subst.compress t in
                    uu____23272.FStar_Syntax_Syntax.n in
                  (match uu____23271 with
                   | FStar_Syntax_Syntax.Tm_abs
                       (bs1, uu____23282, uu____23283) -> bs1
                   | uu____23304 -> failwith "Impossible") in
            let uu____23311 =
              let uu____23318 = erase_binders ed.FStar_Syntax_Syntax.binders in
              FStar_Syntax_Subst.open_term' uu____23318
                FStar_Syntax_Syntax.t_unit in
            match uu____23311 with
            | (binders, uu____23320, binders_opening) ->
                let erase_term t =
                  let uu____23328 =
                    let uu____23329 =
                      FStar_Syntax_Subst.subst binders_opening t in
                    erase_univs uu____23329 in
                  FStar_Syntax_Subst.close binders uu____23328 in
                let erase_tscheme uu____23347 =
                  match uu____23347 with
                  | (us, t) ->
                      let t1 =
                        let uu____23367 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening in
                        FStar_Syntax_Subst.subst uu____23367 t in
                      let uu____23370 =
                        let uu____23371 = erase_univs t1 in
                        FStar_Syntax_Subst.close binders uu____23371 in
                      ([], uu____23370) in
                let erase_action action =
                  let opening =
                    FStar_Syntax_Subst.shift_subst
                      (FStar_List.length
                         action.FStar_Syntax_Syntax.action_univs)
                      binders_opening in
                  let erased_action_params =
                    match action.FStar_Syntax_Syntax.action_params with
                    | [] -> []
                    | uu____23402 ->
                        let bs =
                          let uu____23410 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params in
                          FStar_All.pipe_left erase_binders uu____23410 in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange in
                        let uu____23440 =
                          let uu____23441 =
                            let uu____23444 =
                              FStar_Syntax_Subst.close binders t in
                            FStar_Syntax_Subst.compress uu____23444 in
                          uu____23441.FStar_Syntax_Syntax.n in
                        (match uu____23440 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1, uu____23452, uu____23453) -> bs1
                         | uu____23474 -> failwith "Impossible") in
                  let erase_term1 t =
                    let uu____23487 =
                      let uu____23488 = FStar_Syntax_Subst.subst opening t in
                      erase_univs uu____23488 in
                    FStar_Syntax_Subst.close binders uu____23487 in
                  let uu___150_23489 = action in
                  let uu____23490 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn in
                  let uu____23491 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___150_23489.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___150_23489.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____23490;
                    FStar_Syntax_Syntax.action_typ = uu____23491
                  } in
                let uu___151_23492 = ed in
                let uu____23493 = FStar_Syntax_Subst.close_binders binders in
                let uu____23494 = erase_term ed.FStar_Syntax_Syntax.signature in
                let uu____23495 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp in
                let uu____23496 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp in
                let uu____23497 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else in
                let uu____23498 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp in
                let uu____23499 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger in
                let uu____23500 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp in
                let uu____23501 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p in
                let uu____23502 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p in
                let uu____23503 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp in
                let uu____23504 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial in
                let uu____23505 = erase_term ed.FStar_Syntax_Syntax.repr in
                let uu____23506 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr in
                let uu____23507 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr in
                let uu____23508 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___151_23492.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___151_23492.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____23493;
                  FStar_Syntax_Syntax.signature = uu____23494;
                  FStar_Syntax_Syntax.ret_wp = uu____23495;
                  FStar_Syntax_Syntax.bind_wp = uu____23496;
                  FStar_Syntax_Syntax.if_then_else = uu____23497;
                  FStar_Syntax_Syntax.ite_wp = uu____23498;
                  FStar_Syntax_Syntax.stronger = uu____23499;
                  FStar_Syntax_Syntax.close_wp = uu____23500;
                  FStar_Syntax_Syntax.assert_p = uu____23501;
                  FStar_Syntax_Syntax.assume_p = uu____23502;
                  FStar_Syntax_Syntax.null_wp = uu____23503;
                  FStar_Syntax_Syntax.trivial = uu____23504;
                  FStar_Syntax_Syntax.repr = uu____23505;
                  FStar_Syntax_Syntax.return_repr = uu____23506;
                  FStar_Syntax_Syntax.bind_repr = uu____23507;
                  FStar_Syntax_Syntax.actions = uu____23508;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___151_23492.FStar_Syntax_Syntax.eff_attrs)
                } in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___152_23524 = se in
                  let uu____23525 =
                    let uu____23526 = erase_univs_ed ed in
                    FStar_Syntax_Syntax.Sig_new_effect uu____23526 in
                  {
                    FStar_Syntax_Syntax.sigel = uu____23525;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___152_23524.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___152_23524.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___152_23524.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___152_23524.FStar_Syntax_Syntax.sigattrs)
                  } in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se' in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___153_23530 = se in
                  let uu____23531 =
                    let uu____23532 = erase_univs_ed ed in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____23532 in
                  {
                    FStar_Syntax_Syntax.sigel = uu____23531;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___153_23530.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___153_23530.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___153_23530.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___153_23530.FStar_Syntax_Syntax.sigattrs)
                  } in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se' in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____23534 -> FStar_Syntax_DsEnv.push_sigelt env se in
          let uu____23535 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii in
          match uu____23535 with
          | (en1, pop_when_done) ->
              let en2 =
                let uu____23547 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name in
                FStar_List.fold_left push_sigelt1 uu____23547
                  m.FStar_Syntax_Syntax.exports in
              let env = FStar_Syntax_DsEnv.finish en2 m in
              let uu____23549 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env in
              ((), uu____23549)