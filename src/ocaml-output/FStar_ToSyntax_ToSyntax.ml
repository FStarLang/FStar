open Prims
let (desugar_disjunctive_pattern :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t Prims.list ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.branch Prims.list)
  =
  fun pats  ->
    fun when_opt  ->
      fun branch1  ->
        FStar_All.pipe_right pats
          (FStar_List.map
             (fun pat  -> FStar_Syntax_Util.branch (pat, when_opt, branch1)))
  
let (trans_aqual :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
  =
  fun uu___82_58  ->
    match uu___82_58 with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
    | uu____63 -> FStar_Pervasives_Native.None
  
let (trans_qual :
  FStar_Range.range ->
    FStar_Ident.lident FStar_Pervasives_Native.option ->
      FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier)
  =
  fun r  ->
    fun maybe_effect_id  ->
      fun uu___83_76  ->
        match uu___83_76 with
        | FStar_Parser_AST.Private  -> FStar_Syntax_Syntax.Private
        | FStar_Parser_AST.Assumption  -> FStar_Syntax_Syntax.Assumption
        | FStar_Parser_AST.Unfold_for_unification_and_vcgen  ->
            FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
        | FStar_Parser_AST.Inline_for_extraction  ->
            FStar_Syntax_Syntax.Inline_for_extraction
        | FStar_Parser_AST.NoExtract  -> FStar_Syntax_Syntax.NoExtract
        | FStar_Parser_AST.Irreducible  -> FStar_Syntax_Syntax.Irreducible
        | FStar_Parser_AST.Logic  -> FStar_Syntax_Syntax.Logic
        | FStar_Parser_AST.TotalEffect  -> FStar_Syntax_Syntax.TotalEffect
        | FStar_Parser_AST.Effect_qual  -> FStar_Syntax_Syntax.Effect
        | FStar_Parser_AST.New  -> FStar_Syntax_Syntax.New
        | FStar_Parser_AST.Abstract  -> FStar_Syntax_Syntax.Abstract
        | FStar_Parser_AST.Opaque  ->
            (FStar_Errors.log_issue r
               (FStar_Errors.Warning_DeprecatedOpaqueQualifier,
                 "The 'opaque' qualifier is deprecated since its use was strangely schizophrenic. There were two overloaded uses: (1) Given 'opaque val f : t', the behavior was to exclude the definition of 'f' to the SMT solver. This corresponds roughly to the new 'irreducible' qualifier. (2) Given 'opaque type t = t'', the behavior was to provide the definition of 't' to the SMT solver, but not to inline it, unless absolutely required for unification. This corresponds roughly to the behavior of 'unfoldable' (which is currently the default).");
             FStar_Syntax_Syntax.Visible_default)
        | FStar_Parser_AST.Reflectable  ->
            (match maybe_effect_id with
             | FStar_Pervasives_Native.None  ->
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_ReflectOnlySupportedOnEffects,
                     "Qualifier reflect only supported on effects") r
             | FStar_Pervasives_Native.Some effect_id ->
                 FStar_Syntax_Syntax.Reflectable effect_id)
        | FStar_Parser_AST.Reifiable  -> FStar_Syntax_Syntax.Reifiable
        | FStar_Parser_AST.Noeq  -> FStar_Syntax_Syntax.Noeq
        | FStar_Parser_AST.Unopteq  -> FStar_Syntax_Syntax.Unopteq
        | FStar_Parser_AST.DefaultEffect  ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_DefaultQualifierNotAllowedOnEffects,
                "The 'default' qualifier on effects is no longer supported")
              r
        | FStar_Parser_AST.Inline  ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnsupportedQualifier,
                "Unsupported qualifier") r
        | FStar_Parser_AST.Visible  ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnsupportedQualifier,
                "Unsupported qualifier") r
  
let (trans_pragma : FStar_Parser_AST.pragma -> FStar_Syntax_Syntax.pragma) =
  fun uu___84_83  ->
    match uu___84_83 with
    | FStar_Parser_AST.SetOptions s -> FStar_Syntax_Syntax.SetOptions s
    | FStar_Parser_AST.ResetOptions sopt ->
        FStar_Syntax_Syntax.ResetOptions sopt
    | FStar_Parser_AST.LightOff  -> FStar_Syntax_Syntax.LightOff
  
let (as_imp :
  FStar_Parser_AST.imp ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
  =
  fun uu___85_92  ->
    match uu___85_92 with
    | FStar_Parser_AST.Hash  ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | uu____95 -> FStar_Pervasives_Native.None
  
let arg_withimp_e :
  'Auu____99 .
    FStar_Parser_AST.imp ->
      'Auu____99 ->
        ('Auu____99,FStar_Syntax_Syntax.arg_qualifier
                      FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2
  = fun imp  -> fun t  -> (t, (as_imp imp)) 
let arg_withimp_t :
  'Auu____119 .
    FStar_Parser_AST.imp ->
      'Auu____119 ->
        ('Auu____119,FStar_Syntax_Syntax.arg_qualifier
                       FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2
  =
  fun imp  ->
    fun t  ->
      match imp with
      | FStar_Parser_AST.Hash  ->
          (t, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag))
      | uu____136 -> (t, FStar_Pervasives_Native.None)
  
let (contains_binder : FStar_Parser_AST.binder Prims.list -> Prims.bool) =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b  ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____151 -> true
            | uu____156 -> false))
  
let rec (unparen : FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____161 -> t
  
let (tm_type_z : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____165 =
      let uu____166 = FStar_Ident.lid_of_path ["Type0"] r  in
      FStar_Parser_AST.Name uu____166  in
    FStar_Parser_AST.mk_term uu____165 r FStar_Parser_AST.Kind
  
let (tm_type : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____170 =
      let uu____171 = FStar_Ident.lid_of_path ["Type"] r  in
      FStar_Parser_AST.Name uu____171  in
    FStar_Parser_AST.mk_term uu____170 r FStar_Parser_AST.Kind
  
let rec (is_comp_type :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____178 =
        let uu____179 = unparen t  in uu____179.FStar_Parser_AST.tm  in
      match uu____178 with
      | FStar_Parser_AST.Name l ->
          let uu____181 = FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
          FStar_All.pipe_right uu____181 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l,uu____187) ->
          let uu____200 = FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
          FStar_All.pipe_right uu____200 FStar_Option.isSome
      | FStar_Parser_AST.App (head1,uu____206,uu____207) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,uu____210,uu____211) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____216,t1) -> is_comp_type env t1
      | uu____218 -> false
  
let (unit_ty : FStar_Parser_AST.term) =
  FStar_Parser_AST.mk_term
    (FStar_Parser_AST.Name FStar_Parser_Const.unit_lid)
    FStar_Range.dummyRange FStar_Parser_AST.Type_level
  
let (compile_op_lid :
  Prims.int -> Prims.string -> FStar_Range.range -> FStar_Ident.lident) =
  fun n1  ->
    fun s  ->
      fun r  ->
        let uu____228 =
          let uu____231 =
            let uu____232 =
              let uu____237 = FStar_Parser_AST.compile_op n1 s r  in
              (uu____237, r)  in
            FStar_Ident.mk_ident uu____232  in
          [uu____231]  in
        FStar_All.pipe_right uu____228 FStar_Ident.lid_of_ids
  
let op_as_term :
  'Auu____245 .
    FStar_Syntax_DsEnv.env ->
      Prims.int ->
        'Auu____245 ->
          FStar_Ident.ident ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun arity  ->
      fun rng  ->
        fun op  ->
          let r l dd =
            let uu____273 =
              let uu____274 =
                FStar_Syntax_Syntax.lid_as_fv
                  (FStar_Ident.set_lid_range l op.FStar_Ident.idRange) dd
                  FStar_Pervasives_Native.None
                 in
              FStar_All.pipe_right uu____274 FStar_Syntax_Syntax.fv_to_tm  in
            FStar_Pervasives_Native.Some uu____273  in
          let fallback uu____280 =
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
                let uu____283 = FStar_Options.ml_ish ()  in
                if uu____283
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
            | uu____287 -> FStar_Pervasives_Native.None  in
          let uu____288 =
            let uu____295 =
              compile_op_lid arity op.FStar_Ident.idText
                op.FStar_Ident.idRange
               in
            FStar_Syntax_DsEnv.try_lookup_lid env uu____295  in
          match uu____288 with
          | FStar_Pervasives_Native.Some t ->
              FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst t)
          | uu____307 -> fallback ()
  
let (sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list)
  =
  fun ftv  ->
    let uu____323 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv
       in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____323
  
let rec (free_type_vars_b :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Syntax_DsEnv.env,FStar_Ident.ident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____362 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____366 = FStar_Syntax_DsEnv.push_bv env x  in
          (match uu____366 with | (env1,uu____378) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____381,term) ->
          let uu____383 = free_type_vars env term  in (env, uu____383)
      | FStar_Parser_AST.TAnnotated (id1,uu____389) ->
          let uu____390 = FStar_Syntax_DsEnv.push_bv env id1  in
          (match uu____390 with | (env1,uu____402) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____406 = free_type_vars env t  in (env, uu____406)

and (free_type_vars :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun t  ->
      let uu____413 =
        let uu____414 = unparen t  in uu____414.FStar_Parser_AST.tm  in
      match uu____413 with
      | FStar_Parser_AST.Labeled uu____417 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____427 = FStar_Syntax_DsEnv.try_lookup_id env a  in
          (match uu____427 with
           | FStar_Pervasives_Native.None  -> [a]
           | uu____440 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____447 -> []
      | FStar_Parser_AST.Uvar uu____448 -> []
      | FStar_Parser_AST.Var uu____449 -> []
      | FStar_Parser_AST.Projector uu____450 -> []
      | FStar_Parser_AST.Discrim uu____455 -> []
      | FStar_Parser_AST.Name uu____456 -> []
      | FStar_Parser_AST.Requires (t1,uu____458) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____464) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____469,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None  -> []
             | FStar_Pervasives_Native.Some t2 -> [t2])
             in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____487,ts) ->
          FStar_List.collect
            (fun uu____508  ->
               match uu____508 with | (t1,uu____516) -> free_type_vars env t1)
            ts
      | FStar_Parser_AST.Op (uu____517,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____525) ->
          let uu____526 = free_type_vars env t1  in
          let uu____529 = free_type_vars env t2  in
          FStar_List.append uu____526 uu____529
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____534 = free_type_vars_b env b  in
          (match uu____534 with
           | (env1,f) ->
               let uu____549 = free_type_vars env1 t1  in
               FStar_List.append f uu____549)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____558 =
            FStar_List.fold_left
              (fun uu____578  ->
                 fun binder  ->
                   match uu____578 with
                   | (env1,free) ->
                       let uu____598 = free_type_vars_b env1 binder  in
                       (match uu____598 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____558 with
           | (env1,free) ->
               let uu____629 = free_type_vars env1 body  in
               FStar_List.append free uu____629)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____638 =
            FStar_List.fold_left
              (fun uu____658  ->
                 fun binder  ->
                   match uu____658 with
                   | (env1,free) ->
                       let uu____678 = free_type_vars_b env1 binder  in
                       (match uu____678 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____638 with
           | (env1,free) ->
               let uu____709 = free_type_vars env1 body  in
               FStar_List.append free uu____709)
      | FStar_Parser_AST.Project (t1,uu____713) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.Abs uu____717 -> []
      | FStar_Parser_AST.Let uu____724 -> []
      | FStar_Parser_AST.LetOpen uu____745 -> []
      | FStar_Parser_AST.If uu____750 -> []
      | FStar_Parser_AST.QForall uu____757 -> []
      | FStar_Parser_AST.QExists uu____770 -> []
      | FStar_Parser_AST.Record uu____783 -> []
      | FStar_Parser_AST.Match uu____796 -> []
      | FStar_Parser_AST.TryWith uu____811 -> []
      | FStar_Parser_AST.Bind uu____826 -> []
      | FStar_Parser_AST.Quote uu____833 -> []
      | FStar_Parser_AST.Seq uu____838 -> []

let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term,(FStar_Parser_AST.term,FStar_Parser_AST.imp)
                             FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let rec aux args t1 =
      let uu____885 =
        let uu____886 = unparen t1  in uu____886.FStar_Parser_AST.tm  in
      match uu____885 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____928 -> (t1, args)  in
    aux [] t
  
let (close :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____948 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____948  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____966 =
                     let uu____967 =
                       let uu____972 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____972)  in
                     FStar_Parser_AST.TAnnotated uu____967  in
                   FStar_Parser_AST.mk_binder uu____966 x.FStar_Ident.idRange
                     FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let result =
           FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (binders, t))
             t.FStar_Parser_AST.range t.FStar_Parser_AST.level
            in
         result)
  
let (close_fun :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____985 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____985  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1003 =
                     let uu____1004 =
                       let uu____1009 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____1009)  in
                     FStar_Parser_AST.TAnnotated uu____1004  in
                   FStar_Parser_AST.mk_binder uu____1003
                     x.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____1011 =
             let uu____1012 = unparen t  in uu____1012.FStar_Parser_AST.tm
              in
           match uu____1011 with
           | FStar_Parser_AST.Product uu____1013 -> t
           | uu____1020 ->
               FStar_Parser_AST.mk_term
                 (FStar_Parser_AST.App
                    ((FStar_Parser_AST.mk_term
                        (FStar_Parser_AST.Name
                           FStar_Parser_Const.effect_Tot_lid)
                        t.FStar_Parser_AST.range t.FStar_Parser_AST.level),
                      t, FStar_Parser_AST.Nothing)) t.FStar_Parser_AST.range
                 t.FStar_Parser_AST.level
            in
         let result =
           FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (binders, t1))
             t1.FStar_Parser_AST.range t1.FStar_Parser_AST.level
            in
         result)
  
let rec (uncurry :
  FStar_Parser_AST.binder Prims.list ->
    FStar_Parser_AST.term ->
      (FStar_Parser_AST.binder Prims.list,FStar_Parser_AST.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun bs  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (binders,t1) ->
          uncurry (FStar_List.append bs binders) t1
      | uu____1052 -> (bs, t)
  
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild  -> true
    | FStar_Parser_AST.PatTvar (uu____1058,uu____1059) -> true
    | FStar_Parser_AST.PatVar (uu____1064,uu____1065) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____1071) -> is_var_pattern p1
    | uu____1072 -> false
  
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____1077) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____1078;
           FStar_Parser_AST.prange = uu____1079;_},uu____1080)
        -> true
    | uu____1091 -> false
  
let (replace_unit_pattern :
  FStar_Parser_AST.pattern -> FStar_Parser_AST.pattern) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatConst (FStar_Const.Const_unit ) ->
        FStar_Parser_AST.mk_pattern
          (FStar_Parser_AST.PatAscribed
             ((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild
                 p.FStar_Parser_AST.prange), unit_ty))
          p.FStar_Parser_AST.prange
    | uu____1095 -> p
  
let rec (destruct_app_pattern :
  FStar_Syntax_DsEnv.env ->
    Prims.bool ->
      FStar_Parser_AST.pattern ->
        ((FStar_Ident.ident,FStar_Ident.lident) FStar_Util.either,FStar_Parser_AST.pattern
                                                                    Prims.list,
          FStar_Parser_AST.term FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun is_top_level1  ->
      fun p  ->
        match p.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatAscribed (p1,t) ->
            let uu____1135 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____1135 with
             | (name,args,uu____1166) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1192);
               FStar_Parser_AST.prange = uu____1193;_},args)
            when is_top_level1 ->
            let uu____1203 =
              let uu____1208 = FStar_Syntax_DsEnv.qualify env id1  in
              FStar_Util.Inr uu____1208  in
            (uu____1203, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1218);
               FStar_Parser_AST.prange = uu____1219;_},args)
            -> ((FStar_Util.Inl id1), args, FStar_Pervasives_Native.None)
        | uu____1237 -> failwith "Not an app pattern"
  
let rec (gather_pattern_bound_vars_maybe_top :
  FStar_Ident.ident FStar_Util.set ->
    FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set)
  =
  fun acc  ->
    fun p  ->
      let gather_pattern_bound_vars_from_list =
        FStar_List.fold_left gather_pattern_bound_vars_maybe_top acc  in
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatWild  -> acc
      | FStar_Parser_AST.PatConst uu____1275 -> acc
      | FStar_Parser_AST.PatVar
          (uu____1276,FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit
           ))
          -> acc
      | FStar_Parser_AST.PatName uu____1279 -> acc
      | FStar_Parser_AST.PatTvar uu____1280 -> acc
      | FStar_Parser_AST.PatOp uu____1287 -> acc
      | FStar_Parser_AST.PatApp (phead,pats) ->
          gather_pattern_bound_vars_from_list (phead :: pats)
      | FStar_Parser_AST.PatVar (x,uu____1295) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatTuple (pats,uu____1304) ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu____1319 =
            FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
          gather_pattern_bound_vars_from_list uu____1319
      | FStar_Parser_AST.PatAscribed (pat,uu____1327) ->
          gather_pattern_bound_vars_maybe_top acc pat
  
let (gather_pattern_bound_vars :
  FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set) =
  let acc =
    FStar_Util.new_set
      (fun id1  ->
         fun id2  ->
           if id1.FStar_Ident.idText = id2.FStar_Ident.idText
           then (Prims.parse_int "0")
           else (Prims.parse_int "1"))
     in
  fun p  -> gather_pattern_bound_vars_maybe_top acc p 
type bnd =
  | LocalBinder of (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
  FStar_Pervasives_Native.tuple2 
  | LetBinder of (FStar_Ident.lident,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2 [@@deriving show]
let (uu___is_LocalBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LocalBinder _0 -> true | uu____1365 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____1393 -> false
  
let (__proj__LetBinder__item___0 :
  bnd ->
    (FStar_Ident.lident,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | LetBinder _0 -> _0 
let (binder_of_bnd :
  bnd ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___86_1419  ->
    match uu___86_1419 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____1426 -> failwith "Impossible"
  
let (as_binder :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      (FStar_Ident.ident FStar_Pervasives_Native.option,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2 ->
        (FStar_Syntax_Syntax.binder,FStar_Syntax_DsEnv.env)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun imp  ->
      fun uu___87_1451  ->
        match uu___87_1451 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____1467 = FStar_Syntax_Syntax.null_binder k  in
            (uu____1467, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____1472 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____1472 with
             | (env1,a1) ->
                 (((let uu___111_1492 = a1  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___111_1492.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___111_1492.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = k
                    }), (trans_aqual imp)), env1))
  
type env_t = FStar_Syntax_DsEnv.env[@@deriving show]
type lenv_t = FStar_Syntax_Syntax.bv Prims.list[@@deriving show]
let (mk_lb :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list,(FStar_Syntax_Syntax.bv,
                                                                    FStar_Syntax_Syntax.fv)
                                                                    FStar_Util.either,
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.term'
                                                           FStar_Syntax_Syntax.syntax)
    FStar_Pervasives_Native.tuple4 -> FStar_Syntax_Syntax.letbinding)
  =
  fun uu____1517  ->
    match uu____1517 with
    | (attrs,n1,t,e) ->
        {
          FStar_Syntax_Syntax.lbname = n1;
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_ALL_lid;
          FStar_Syntax_Syntax.lbdef = e;
          FStar_Syntax_Syntax.lbattrs = attrs
        }
  
let (no_annot_abs :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun bs  ->
    fun t  -> FStar_Syntax_Util.abs bs t FStar_Pervasives_Native.None
  
let (mk_ref_read :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____1582 =
        let uu____1597 =
          let uu____1598 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____1598  in
        let uu____1599 =
          let uu____1608 =
            let uu____1615 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____1615)  in
          [uu____1608]  in
        (uu____1597, uu____1599)  in
      FStar_Syntax_Syntax.Tm_app uu____1582  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____1648 =
        let uu____1663 =
          let uu____1664 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____1664  in
        let uu____1665 =
          let uu____1674 =
            let uu____1681 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____1681)  in
          [uu____1674]  in
        (uu____1663, uu____1665)  in
      FStar_Syntax_Syntax.Tm_app uu____1648  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_assign :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Range.range ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      fun pos  ->
        let tm =
          let uu____1724 =
            let uu____1739 =
              let uu____1740 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____1740  in
            let uu____1741 =
              let uu____1750 =
                let uu____1757 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____1757)  in
              let uu____1760 =
                let uu____1769 =
                  let uu____1776 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____1776)  in
                [uu____1769]  in
              uu____1750 :: uu____1760  in
            (uu____1739, uu____1741)  in
          FStar_Syntax_Syntax.Tm_app uu____1724  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___88_1807  ->
    match uu___88_1807 with
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
    | uu____1808 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____1816 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____1816)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____1831 =
      let uu____1832 = unparen t  in uu____1832.FStar_Parser_AST.tm  in
    match uu____1831 with
    | FStar_Parser_AST.Wild  ->
        let uu____1837 =
          let uu____1838 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____1838  in
        FStar_Util.Inr uu____1837
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____1849)) ->
        let n1 = FStar_Util.int_of_string repr  in
        (if n1 < (Prims.parse_int "0")
         then
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_NegativeUniverseConstFatal_NotSupported,
               (Prims.strcat
                  "Negative universe constant  are not supported : " repr))
             t.FStar_Parser_AST.range
         else ();
         FStar_Util.Inl n1)
    | FStar_Parser_AST.Op (op_plus,t1::t2::[]) ->
        let u1 = desugar_maybe_non_constant_universe t1  in
        let u2 = desugar_maybe_non_constant_universe t2  in
        (match (u1, u2) with
         | (FStar_Util.Inl n1,FStar_Util.Inl n2) -> FStar_Util.Inl (n1 + n2)
         | (FStar_Util.Inl n1,FStar_Util.Inr u) ->
             let uu____1915 = sum_to_universe u n1  in
             FStar_Util.Inr uu____1915
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____1926 = sum_to_universe u n1  in
             FStar_Util.Inr uu____1926
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____1937 =
               let uu____1942 =
                 let uu____1943 = FStar_Parser_AST.term_to_string t  in
                 Prims.strcat
                   "This universe might contain a sum of two universe variables "
                   uu____1943
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____1942)
                in
             FStar_Errors.raise_error uu____1937 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____1948 ->
        let rec aux t1 univargs =
          let uu____1978 =
            let uu____1979 = unparen t1  in uu____1979.FStar_Parser_AST.tm
             in
          match uu____1978 with
          | FStar_Parser_AST.App (t2,targ,uu____1986) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___89_2010  ->
                     match uu___89_2010 with
                     | FStar_Util.Inr uu____2015 -> true
                     | uu____2016 -> false) univargs
              then
                let uu____2021 =
                  let uu____2022 =
                    FStar_List.map
                      (fun uu___90_2031  ->
                         match uu___90_2031 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____2022  in
                FStar_Util.Inr uu____2021
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___91_2048  ->
                        match uu___91_2048 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____2054 -> failwith "impossible")
                     univargs
                    in
                 let uu____2055 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____2055)
          | uu____2061 ->
              let uu____2062 =
                let uu____2067 =
                  let uu____2068 =
                    let uu____2069 = FStar_Parser_AST.term_to_string t1  in
                    Prims.strcat uu____2069 " in universe context"  in
                  Prims.strcat "Unexpected term " uu____2068  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____2067)  in
              FStar_Errors.raise_error uu____2062 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____2078 ->
        let uu____2079 =
          let uu____2084 =
            let uu____2085 =
              let uu____2086 = FStar_Parser_AST.term_to_string t  in
              Prims.strcat uu____2086 " in universe context"  in
            Prims.strcat "Unexpected term " uu____2085  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____2084)  in
        FStar_Errors.raise_error uu____2079 t.FStar_Parser_AST.range
  
let rec (desugar_universe :
  FStar_Parser_AST.term -> FStar_Syntax_Syntax.universe) =
  fun t  ->
    let u = desugar_maybe_non_constant_universe t  in
    match u with
    | FStar_Util.Inl n1 -> int_to_universe n1
    | FStar_Util.Inr u1 -> u1
  
let check_fields :
  'Auu____2105 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident,'Auu____2105) FStar_Pervasives_Native.tuple2
        Prims.list -> FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____2130 = FStar_List.hd fields  in
        match uu____2130 with
        | (f,uu____2140) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____2150 =
                match uu____2150 with
                | (f',uu____2156) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____2158 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____2158
                      then ()
                      else
                        (let msg =
                           FStar_Util.format3
                             "Field %s belongs to record type %s, whereas field %s does not"
                             f.FStar_Ident.str
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                             f'.FStar_Ident.str
                            in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_FieldsNotBelongToSameRecordType,
                             msg) rg)))
                 in
              (let uu____2162 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____2162);
              (match () with | () -> record)))
  
let rec (desugar_data_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern ->
      Prims.bool ->
        (env_t,bnd,FStar_Syntax_Syntax.pat Prims.list)
          FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun p  ->
      fun is_mut  ->
        let check_linear_pattern_variables p1 r =
          let rec pat_vars p2 =
            match p2.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_dot_term uu____2379 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_wild uu____2386 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_constant uu____2387 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_var x ->
                FStar_Util.set_add x FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_cons (uu____2389,pats) ->
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun out  ->
                        fun uu____2430  ->
                          match uu____2430 with
                          | (p3,uu____2440) ->
                              let uu____2441 =
                                let uu____2442 =
                                  let uu____2445 = pat_vars p3  in
                                  FStar_Util.set_intersect uu____2445 out  in
                                FStar_Util.set_is_empty uu____2442  in
                              if uu____2441
                              then
                                let uu____2450 = pat_vars p3  in
                                FStar_Util.set_union out uu____2450
                              else
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                                    "Non-linear patterns are not permitted.")
                                  r) FStar_Syntax_Syntax.no_names)
             in
          pat_vars p1  in
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false ,uu____2457) -> ()
         | (true ,FStar_Parser_AST.PatVar uu____2458) -> ()
         | (true ,uu____2465) ->
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_LetMutableForVariablesOnly,
                 "let-mutable is for variables only")
               p.FStar_Parser_AST.prange);
        (let push_bv_maybe_mut =
           if is_mut
           then FStar_Syntax_DsEnv.push_bv_mutable
           else FStar_Syntax_DsEnv.push_bv  in
         let resolvex l e x =
           let uu____2500 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText))
              in
           match uu____2500 with
           | FStar_Pervasives_Native.Some y -> (l, e, y)
           | uu____2514 ->
               let uu____2517 = push_bv_maybe_mut e x  in
               (match uu____2517 with | (e1,x1) -> ((x1 :: l), e1, x1))
            in
         let rec aux' top loc env1 p1 =
           let pos q =
             FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange  in
           let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
           let orig = p1  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr uu____2604 -> failwith "impossible"
           | FStar_Parser_AST.PatOp op ->
               let uu____2620 =
                 let uu____2621 =
                   let uu____2622 =
                     let uu____2629 =
                       let uu____2630 =
                         let uu____2635 =
                           FStar_Parser_AST.compile_op (Prims.parse_int "0")
                             op.FStar_Ident.idText op.FStar_Ident.idRange
                            in
                         (uu____2635, (op.FStar_Ident.idRange))  in
                       FStar_Ident.mk_ident uu____2630  in
                     (uu____2629, FStar_Pervasives_Native.None)  in
                   FStar_Parser_AST.PatVar uu____2622  in
                 {
                   FStar_Parser_AST.pat = uu____2621;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 }  in
               aux loc env1 uu____2620
           | FStar_Parser_AST.PatAscribed (p2,t) ->
               let uu____2640 = aux loc env1 p2  in
               (match uu____2640 with
                | (loc1,env',binder,p3,imp) ->
                    let annot_pat_var p4 t1 =
                      match p4.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_var x ->
                          let uu___112_2694 = p4  in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_var
                                 (let uu___113_2699 = x  in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___113_2699.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___113_2699.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = t1
                                  }));
                            FStar_Syntax_Syntax.p =
                              (uu___112_2694.FStar_Syntax_Syntax.p)
                          }
                      | FStar_Syntax_Syntax.Pat_wild x ->
                          let uu___114_2701 = p4  in
                          {
                            FStar_Syntax_Syntax.v =
                              (FStar_Syntax_Syntax.Pat_wild
                                 (let uu___115_2706 = x  in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___115_2706.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___115_2706.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = t1
                                  }));
                            FStar_Syntax_Syntax.p =
                              (uu___114_2701.FStar_Syntax_Syntax.p)
                          }
                      | uu____2707 when top -> p4
                      | uu____2708 ->
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                              "Type ascriptions within patterns are only allowed on variables")
                            orig.FStar_Parser_AST.prange
                       in
                    let uu____2711 =
                      match binder with
                      | LetBinder uu____2724 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____2738 = close_fun env1 t  in
                            desugar_term env1 uu____2738  in
                          (if
                             (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                              with
                              | FStar_Syntax_Syntax.Tm_unknown  -> false
                              | uu____2740 -> true)
                           then
                             (let uu____2741 =
                                let uu____2746 =
                                  let uu____2747 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____2748 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____2749 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3
                                    "Multiple ascriptions for %s in pattern, type %s was shadowed by %s\n"
                                    uu____2747 uu____2748 uu____2749
                                   in
                                (FStar_Errors.Warning_MultipleAscriptions,
                                  uu____2746)
                                 in
                              FStar_Errors.log_issue
                                orig.FStar_Parser_AST.prange uu____2741)
                           else ();
                           (let uu____2751 = annot_pat_var p3 t1  in
                            (uu____2751,
                              (LocalBinder
                                 ((let uu___116_2757 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___116_2757.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___116_2757.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }), aq)))))
                       in
                    (match uu____2711 with
                     | (p4,binder1) -> (loc1, env', binder1, p4, imp)))
           | FStar_Parser_AST.PatWild  ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____2779 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____2779, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____2790 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____2790, false)
           | FStar_Parser_AST.PatTvar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual aq  in
               let uu____2811 = resolvex loc env1 x  in
               (match uu____2811 with
                | (loc1,env2,xbv) ->
                    let uu____2833 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____2833, imp))
           | FStar_Parser_AST.PatVar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual aq  in
               let uu____2854 = resolvex loc env1 x  in
               (match uu____2854 with
                | (loc1,env2,xbv) ->
                    let uu____2876 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____2876, imp))
           | FStar_Parser_AST.PatName l ->
               let l1 =
                 FStar_Syntax_DsEnv.fail_or env1
                   (FStar_Syntax_DsEnv.try_lookup_datacon env1) l
                  in
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____2888 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, []))
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____2888, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____2912;_},args)
               ->
               let uu____2918 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____2959  ->
                        match uu____2959 with
                        | (loc1,env2,args1) ->
                            let uu____3007 = aux loc1 env2 arg  in
                            (match uu____3007 with
                             | (loc2,env3,uu____3036,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, [])
                  in
               (match uu____2918 with
                | (loc1,env2,args1) ->
                    let l1 =
                      FStar_Syntax_DsEnv.fail_or env2
                        (FStar_Syntax_DsEnv.try_lookup_datacon env2) l
                       in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun
                       in
                    let uu____3106 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                       in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)),
                      uu____3106, false))
           | FStar_Parser_AST.PatApp uu____3123 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                 p1.FStar_Parser_AST.prange
           | FStar_Parser_AST.PatList pats ->
               let uu____3145 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____3178  ->
                        match uu____3178 with
                        | (loc1,env2,pats1) ->
                            let uu____3210 = aux loc1 env2 pat  in
                            (match uu____3210 with
                             | (loc2,env3,uu____3235,pat1,uu____3237) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, [])
                  in
               (match uu____3145 with
                | (loc1,env2,pats1) ->
                    let pat =
                      let uu____3280 =
                        let uu____3283 =
                          let uu____3288 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange
                             in
                          pos_r uu____3288  in
                        let uu____3289 =
                          let uu____3290 =
                            let uu____3303 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Parser_Const.nil_lid
                                FStar_Syntax_Syntax.Delta_constant
                                (FStar_Pervasives_Native.Some
                                   FStar_Syntax_Syntax.Data_ctor)
                               in
                            (uu____3303, [])  in
                          FStar_Syntax_Syntax.Pat_cons uu____3290  in
                        FStar_All.pipe_left uu____3283 uu____3289  in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p
                                in
                             let uu____3335 =
                               let uu____3336 =
                                 let uu____3349 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.cons_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Data_ctor)
                                    in
                                 (uu____3349, [(hd1, false); (tl1, false)])
                                  in
                               FStar_Syntax_Syntax.Pat_cons uu____3336  in
                             FStar_All.pipe_left (pos_r r) uu____3335) pats1
                        uu____3280
                       in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun
                       in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)), pat,
                      false))
           | FStar_Parser_AST.PatTuple (args,dep1) ->
               let uu____3393 =
                 FStar_List.fold_left
                   (fun uu____3433  ->
                      fun p2  ->
                        match uu____3433 with
                        | (loc1,env2,pats) ->
                            let uu____3482 = aux loc1 env2 p2  in
                            (match uu____3482 with
                             | (loc2,env3,uu____3511,pat,uu____3513) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args
                  in
               (match uu____3393 with
                | (loc1,env2,args1) ->
                    let args2 = FStar_List.rev args1  in
                    let l =
                      if dep1
                      then
                        FStar_Parser_Const.mk_dtuple_data_lid
                          (FStar_List.length args2)
                          p1.FStar_Parser_AST.prange
                      else
                        FStar_Parser_Const.mk_tuple_data_lid
                          (FStar_List.length args2)
                          p1.FStar_Parser_AST.prange
                       in
                    let uu____3608 =
                      FStar_Syntax_DsEnv.fail_or env2
                        (FStar_Syntax_DsEnv.try_lookup_lid env2) l
                       in
                    (match uu____3608 with
                     | (constr,uu____3630) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____3633 -> failwith "impossible"  in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (FStar_Pervasives_Native.Some
                                (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun
                            in
                         let uu____3635 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                            in
                         (loc1, env2,
                           (LocalBinder (x, FStar_Pervasives_Native.None)),
                           uu____3635, false)))
           | FStar_Parser_AST.PatRecord [] ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                 p1.FStar_Parser_AST.prange
           | FStar_Parser_AST.PatRecord fields ->
               let record =
                 check_fields env1 fields p1.FStar_Parser_AST.prange  in
               let fields1 =
                 FStar_All.pipe_right fields
                   (FStar_List.map
                      (fun uu____3706  ->
                         match uu____3706 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2)))
                  in
               let args =
                 FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                   (FStar_List.map
                      (fun uu____3736  ->
                         match uu____3736 with
                         | (f,uu____3742) ->
                             let uu____3743 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____3769  ->
                                       match uu____3769 with
                                       | (g,uu____3775) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText))
                                in
                             (match uu____3743 with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
                              | FStar_Pervasives_Native.Some (uu____3780,p2)
                                  -> p2)))
                  in
               let app =
                 let uu____3787 =
                   let uu____3788 =
                     let uu____3795 =
                       let uu____3796 =
                         let uu____3797 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                                [record.FStar_Syntax_DsEnv.constrname])
                            in
                         FStar_Parser_AST.PatName uu____3797  in
                       FStar_Parser_AST.mk_pattern uu____3796
                         p1.FStar_Parser_AST.prange
                        in
                     (uu____3795, args)  in
                   FStar_Parser_AST.PatApp uu____3788  in
                 FStar_Parser_AST.mk_pattern uu____3787
                   p1.FStar_Parser_AST.prange
                  in
               let uu____3800 = aux loc env1 app  in
               (match uu____3800 with
                | (env2,e,b,p2,uu____3829) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____3857 =
                            let uu____3858 =
                              let uu____3871 =
                                let uu___117_3872 = fv  in
                                let uu____3873 =
                                  let uu____3876 =
                                    let uu____3877 =
                                      let uu____3884 =
                                        FStar_All.pipe_right
                                          record.FStar_Syntax_DsEnv.fields
                                          (FStar_List.map
                                             FStar_Pervasives_Native.fst)
                                         in
                                      ((record.FStar_Syntax_DsEnv.typename),
                                        uu____3884)
                                       in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____3877
                                     in
                                  FStar_Pervasives_Native.Some uu____3876  in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___117_3872.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___117_3872.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____3873
                                }  in
                              (uu____3871, args1)  in
                            FStar_Syntax_Syntax.Pat_cons uu____3858  in
                          FStar_All.pipe_left pos uu____3857
                      | uu____3911 -> p2  in
                    (env2, e, b, p3, false))
         
         and aux loc env1 p1 = aux' false loc env1 p1
          in
         let aux_maybe_or env1 p1 =
           let loc = []  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____3961 = aux' true loc env1 p2  in
               (match uu____3961 with
                | (loc1,env2,var,p3,uu____3988) ->
                    let uu____3993 =
                      FStar_List.fold_left
                        (fun uu____4025  ->
                           fun p4  ->
                             match uu____4025 with
                             | (loc2,env3,ps1) ->
                                 let uu____4058 = aux' true loc2 env3 p4  in
                                 (match uu____4058 with
                                  | (loc3,env4,uu____4083,p5,uu____4085) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps
                       in
                    (match uu____3993 with
                     | (loc2,env3,ps1) ->
                         let pats = p3 :: (FStar_List.rev ps1)  in
                         (env3, var, pats)))
           | uu____4136 ->
               let uu____4137 = aux' true loc env1 p1  in
               (match uu____4137 with
                | (loc1,env2,vars,pat,b) -> (env2, vars, [pat]))
            in
         let uu____4177 = aux_maybe_or env p  in
         match uu____4177 with
         | (env1,b,pats) ->
             ((let uu____4208 =
                 FStar_List.map
                   (fun pats1  ->
                      check_linear_pattern_variables pats1
                        p.FStar_Parser_AST.prange) pats
                  in
               FStar_All.pipe_left FStar_Pervasives.ignore uu____4208);
              (env1, b, pats)))

and (desugar_binding_pat_maybe_top :
  Prims.bool ->
    FStar_Syntax_DsEnv.env ->
      FStar_Parser_AST.pattern ->
        Prims.bool ->
          (env_t,bnd,FStar_Syntax_Syntax.pat Prims.list)
            FStar_Pervasives_Native.tuple3)
  =
  fun top  ->
    fun env  ->
      fun p  ->
        fun is_mut  ->
          let mklet x =
            let uu____4245 =
              let uu____4246 =
                let uu____4251 = FStar_Syntax_DsEnv.qualify env x  in
                (uu____4251, FStar_Syntax_Syntax.tun)  in
              LetBinder uu____4246  in
            (env, uu____4245, [])  in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____4271 =
                  let uu____4272 =
                    let uu____4277 =
                      FStar_Parser_AST.compile_op (Prims.parse_int "0")
                        x.FStar_Ident.idText x.FStar_Ident.idRange
                       in
                    (uu____4277, (x.FStar_Ident.idRange))  in
                  FStar_Ident.mk_ident uu____4272  in
                mklet uu____4271
            | FStar_Parser_AST.PatVar (x,uu____4279) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____4285);
                   FStar_Parser_AST.prange = uu____4286;_},t)
                ->
                let uu____4292 =
                  let uu____4293 =
                    let uu____4298 = FStar_Syntax_DsEnv.qualify env x  in
                    let uu____4299 = desugar_term env t  in
                    (uu____4298, uu____4299)  in
                  LetBinder uu____4293  in
                (env, uu____4292, [])
            | uu____4302 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_UnexpectedPattern,
                    "Unexpected pattern at the top-level")
                  p.FStar_Parser_AST.prange
          else
            (let uu____4312 = desugar_data_pat env p is_mut  in
             match uu____4312 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1 with
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                         uu____4341;
                       FStar_Syntax_Syntax.p = uu____4342;_}::[] -> []
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                         uu____4347;
                       FStar_Syntax_Syntax.p = uu____4348;_}::[] -> []
                   | uu____4353 -> p1  in
                 (env1, binder, p2))

and (desugar_binding_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern ->
      (env_t,bnd,FStar_Syntax_Syntax.pat Prims.list)
        FStar_Pervasives_Native.tuple3)
  = fun env  -> fun p  -> desugar_binding_pat_maybe_top false env p false

and (desugar_match_pat_maybe_top :
  Prims.bool ->
    FStar_Syntax_DsEnv.env ->
      FStar_Parser_AST.pattern ->
        (env_t,FStar_Syntax_Syntax.pat Prims.list)
          FStar_Pervasives_Native.tuple2)
  =
  fun uu____4360  ->
    fun env  ->
      fun pat  ->
        let uu____4363 = desugar_data_pat env pat false  in
        match uu____4363 with | (env1,uu____4379,pat1) -> (env1, pat1)

and (desugar_match_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern ->
      (env_t,FStar_Syntax_Syntax.pat Prims.list)
        FStar_Pervasives_Native.tuple2)
  = fun env  -> fun p  -> desugar_match_pat_maybe_top false env p

and (desugar_term :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let env1 = FStar_Syntax_DsEnv.set_expect_typ env false  in
      desugar_term_maybe_top false env1 e

and (desugar_typ :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let env1 = FStar_Syntax_DsEnv.set_expect_typ env true  in
      desugar_term_maybe_top false env1 e

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness,FStar_Const.width)
        FStar_Pervasives_Native.tuple2 ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____4397  ->
        fun range  ->
          match uu____4397 with
          | (signedness,width) ->
              let tnm =
                Prims.strcat "FStar."
                  (Prims.strcat
                     (match signedness with
                      | FStar_Const.Unsigned  -> "U"
                      | FStar_Const.Signed  -> "")
                     (Prims.strcat "Int"
                        (match width with
                         | FStar_Const.Int8  -> "8"
                         | FStar_Const.Int16  -> "16"
                         | FStar_Const.Int32  -> "32"
                         | FStar_Const.Int64  -> "64")))
                 in
              ((let uu____4407 =
                  let uu____4408 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____4408  in
                if uu____4407
                then
                  let uu____4409 =
                    let uu____4414 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____4414)  in
                  FStar_Errors.log_issue range uu____4409
                else ());
               (let private_intro_nm =
                  Prims.strcat tnm
                    (Prims.strcat ".__"
                       (Prims.strcat
                          (match signedness with
                           | FStar_Const.Unsigned  -> "u"
                           | FStar_Const.Signed  -> "") "int_to_t"))
                   in
                let intro_nm =
                  Prims.strcat tnm
                    (Prims.strcat "."
                       (Prims.strcat
                          (match signedness with
                           | FStar_Const.Unsigned  -> "u"
                           | FStar_Const.Signed  -> "") "int_to_t"))
                   in
                let lid =
                  FStar_Ident.lid_of_path (FStar_Ident.path_of_text intro_nm)
                    range
                   in
                let lid1 =
                  let uu____4422 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____4422 with
                  | FStar_Pervasives_Native.Some (intro_term,uu____4432) ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             FStar_Ident.lid_of_path
                               (FStar_Ident.path_of_text private_intro_nm)
                               range
                              in
                           let private_fv =
                             let uu____4442 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____4442 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___118_4443 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___118_4443.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___118_4443.FStar_Syntax_Syntax.vars)
                           }
                       | uu____4444 ->
                           failwith
                             (Prims.strcat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____4451 =
                        let uu____4456 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____4456)
                         in
                      FStar_Errors.raise_error uu____4451 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____4472 =
                  let uu____4475 =
                    let uu____4476 =
                      let uu____4491 =
                        let uu____4500 =
                          let uu____4507 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____4507)  in
                        [uu____4500]  in
                      (lid1, uu____4491)  in
                    FStar_Syntax_Syntax.Tm_app uu____4476  in
                  FStar_Syntax_Syntax.mk uu____4475  in
                uu____4472 FStar_Pervasives_Native.None range))

and (desugar_name :
  (FStar_Syntax_Syntax.term' -> FStar_Syntax_Syntax.term) ->
    (FStar_Syntax_Syntax.term ->
       FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
      -> env_t -> Prims.bool -> FStar_Ident.lid -> FStar_Syntax_Syntax.term)
  =
  fun mk1  ->
    fun setpos  ->
      fun env  ->
        fun resolve  ->
          fun l  ->
            let uu____4546 =
              FStar_Syntax_DsEnv.fail_or env
                ((if resolve
                  then FStar_Syntax_DsEnv.try_lookup_lid_with_attributes
                  else
                    FStar_Syntax_DsEnv.try_lookup_lid_with_attributes_no_resolve)
                   env) l
               in
            match uu____4546 with
            | (tm,mut,attrs) ->
                let warn_if_deprecated attrs1 =
                  FStar_List.iter
                    (fun a  ->
                       match a.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_app
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____4592;
                              FStar_Syntax_Syntax.vars = uu____4593;_},args)
                           when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____4616 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____4616 " is deprecated"  in
                           let msg1 =
                             if
                               (FStar_List.length args) >
                                 (Prims.parse_int "0")
                             then
                               let uu____4624 =
                                 let uu____4625 =
                                   let uu____4628 = FStar_List.hd args  in
                                   FStar_Pervasives_Native.fst uu____4628  in
                                 uu____4625.FStar_Syntax_Syntax.n  in
                               match uu____4624 with
                               | FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_string (s,uu____4644))
                                   when
                                   Prims.op_Negation
                                     ((FStar_Util.trim_string s) = "")
                                   ->
                                   Prims.strcat msg
                                     (Prims.strcat ", use "
                                        (Prims.strcat s " instead"))
                               | uu____4645 -> msg
                             else msg  in
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
                             let uu____4649 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____4649 " is deprecated"  in
                           FStar_Errors.log_issue
                             (FStar_Ident.range_of_lid l)
                             (FStar_Errors.Warning_DeprecatedDefinition, msg)
                       | uu____4650 -> ()) attrs1
                   in
                (warn_if_deprecated attrs;
                 (let tm1 = setpos tm  in
                  if mut
                  then
                    let uu____4655 =
                      let uu____4656 =
                        let uu____4663 = mk_ref_read tm1  in
                        (uu____4663,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Mutable_rval))
                         in
                      FStar_Syntax_Syntax.Tm_meta uu____4656  in
                    FStar_All.pipe_left mk1 uu____4655
                  else tm1))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____4679 =
          let uu____4680 = unparen t  in uu____4680.FStar_Parser_AST.tm  in
        match uu____4679 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____4681; FStar_Ident.ident = uu____4682;
              FStar_Ident.nsstr = uu____4683; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____4686 ->
            let uu____4687 =
              let uu____4692 =
                let uu____4693 = FStar_Parser_AST.term_to_string t  in
                Prims.strcat "Unknown attribute " uu____4693  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____4692)  in
            FStar_Errors.raise_error uu____4687 t.FStar_Parser_AST.range
         in
      FStar_List.map desugar_attribute cattributes

and (desugar_term_maybe_top :
  Prims.bool -> env_t -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term) =
  fun top_level  ->
    fun env  ->
      fun top  ->
        let mk1 e =
          FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
            top.FStar_Parser_AST.range
           in
        let setpos e =
          let uu___119_4713 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___119_4713.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___119_4713.FStar_Syntax_Syntax.vars)
          }  in
        let uu____4716 =
          let uu____4717 = unparen top  in uu____4717.FStar_Parser_AST.tm  in
        match uu____4716 with
        | FStar_Parser_AST.Wild  -> setpos FStar_Syntax_Syntax.tun
        | FStar_Parser_AST.Labeled uu____4718 -> desugar_formula env top
        | FStar_Parser_AST.Requires (t,lopt) -> desugar_formula env t
        | FStar_Parser_AST.Ensures (t,lopt) -> desugar_formula env t
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            desugar_machine_integer env i size top.FStar_Parser_AST.range
        | FStar_Parser_AST.Const c -> mk1 (FStar_Syntax_Syntax.Tm_constant c)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Op ((FStar_Ident.mk_ident ("==", r)), args))
                top.FStar_Parser_AST.range top.FStar_Parser_AST.level
               in
            desugar_term env
              (FStar_Parser_AST.mk_term
                 (FStar_Parser_AST.Op ((FStar_Ident.mk_ident ("~", r)), [e]))
                 top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
        | FStar_Parser_AST.Op (op_star,uu____4769::uu____4770::[]) when
            ((FStar_Ident.text_of_id op_star) = "*") &&
              (let uu____4774 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____4774 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____4787;_},t1::t2::[])
                  ->
                  let uu____4792 = flatten1 t1  in
                  FStar_List.append uu____4792 [t2]
              | uu____4795 -> [t]  in
            let targs =
              let uu____4799 =
                let uu____4802 = unparen top  in flatten1 uu____4802  in
              FStar_All.pipe_right uu____4799
                (FStar_List.map
                   (fun t  ->
                      let uu____4810 = desugar_typ env t  in
                      FStar_Syntax_Syntax.as_arg uu____4810))
               in
            let uu____4811 =
              let uu____4816 =
                FStar_Parser_Const.mk_tuple_lid (FStar_List.length targs)
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_DsEnv.fail_or env
                (FStar_Syntax_DsEnv.try_lookup_lid env) uu____4816
               in
            (match uu____4811 with
             | (tup,uu____4822) ->
                 mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs)))
        | FStar_Parser_AST.Tvar a ->
            let uu____4826 =
              let uu____4829 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_Pervasives_Native.fst uu____4829  in
            FStar_All.pipe_left setpos uu____4826
        | FStar_Parser_AST.Uvar u ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedUniverseVariable,
                (Prims.strcat "Unexpected universe variable "
                   (Prims.strcat (FStar_Ident.text_of_id u)
                      " in non-universe context")))
              top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____4849 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____4849 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     (Prims.strcat "Unexpected or unbound operator: "
                        (FStar_Ident.text_of_id s)))
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let args1 =
                     FStar_All.pipe_right args
                       (FStar_List.map
                          (fun t  ->
                             let uu____4881 = desugar_term env t  in
                             (uu____4881, FStar_Pervasives_Native.None)))
                      in
                   mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))
                 else op)
        | FStar_Parser_AST.Construct (n1,(a,uu____4895)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____4910 =
              let uu___120_4911 = top  in
              let uu____4912 =
                let uu____4913 =
                  let uu____4920 =
                    let uu___121_4921 = top  in
                    let uu____4922 =
                      let uu____4923 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____4923  in
                    {
                      FStar_Parser_AST.tm = uu____4922;
                      FStar_Parser_AST.range =
                        (uu___121_4921.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___121_4921.FStar_Parser_AST.level)
                    }  in
                  (uu____4920, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____4913  in
              {
                FStar_Parser_AST.tm = uu____4912;
                FStar_Parser_AST.range =
                  (uu___120_4911.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___120_4911.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____4910
        | FStar_Parser_AST.Construct (n1,(a,uu____4926)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____4942 =
                let uu___122_4943 = top  in
                let uu____4944 =
                  let uu____4945 =
                    let uu____4952 =
                      let uu___123_4953 = top  in
                      let uu____4954 =
                        let uu____4955 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____4955  in
                      {
                        FStar_Parser_AST.tm = uu____4954;
                        FStar_Parser_AST.range =
                          (uu___123_4953.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___123_4953.FStar_Parser_AST.level)
                      }  in
                    (uu____4952, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____4945  in
                {
                  FStar_Parser_AST.tm = uu____4944;
                  FStar_Parser_AST.range =
                    (uu___122_4943.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___122_4943.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____4942))
        | FStar_Parser_AST.Construct (n1,(a,uu____4958)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____4973 =
              let uu___124_4974 = top  in
              let uu____4975 =
                let uu____4976 =
                  let uu____4983 =
                    let uu___125_4984 = top  in
                    let uu____4985 =
                      let uu____4986 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____4986  in
                    {
                      FStar_Parser_AST.tm = uu____4985;
                      FStar_Parser_AST.range =
                        (uu___125_4984.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___125_4984.FStar_Parser_AST.level)
                    }  in
                  (uu____4983, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____4976  in
              {
                FStar_Parser_AST.tm = uu____4975;
                FStar_Parser_AST.range =
                  (uu___124_4974.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___124_4974.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____4973
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____4987; FStar_Ident.ident = uu____4988;
              FStar_Ident.nsstr = uu____4989; FStar_Ident.str = "Type0";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____4992; FStar_Ident.ident = uu____4993;
              FStar_Ident.nsstr = uu____4994; FStar_Ident.str = "Type";_}
            ->
            mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____4997; FStar_Ident.ident = uu____4998;
               FStar_Ident.nsstr = uu____4999; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____5017 =
              let uu____5018 = desugar_universe t  in
              FStar_Syntax_Syntax.Tm_type uu____5018  in
            mk1 uu____5017
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5019; FStar_Ident.ident = uu____5020;
              FStar_Ident.nsstr = uu____5021; FStar_Ident.str = "Effect";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5024; FStar_Ident.ident = uu____5025;
              FStar_Ident.nsstr = uu____5026; FStar_Ident.str = "True";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5029; FStar_Ident.ident = uu____5030;
              FStar_Ident.nsstr = uu____5031; FStar_Ident.str = "False";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____5036;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____5038 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____5038 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  FStar_Syntax_Syntax.fvar lid
                    (FStar_Syntax_Syntax.Delta_defined_at_level
                       (Prims.parse_int "1")) FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.None  ->
                  let uu____5043 =
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      (FStar_Ident.text_of_lid eff_name) txt
                     in
                  failwith uu____5043))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             desugar_name mk1 setpos env true l)
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             desugar_name mk1 setpos env true l)
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____5058 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____5058 with
                | FStar_Pervasives_Native.Some uu____5067 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____5072 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____5072 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____5086 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____5099 =
                    FStar_Syntax_Util.mk_field_projector_name_from_ident
                      new_name i
                     in
                  desugar_name mk1 setpos env resolve uu____5099
              | uu____5100 ->
                  let uu____5107 =
                    let uu____5112 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____5112)  in
                  FStar_Errors.raise_error uu____5107
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____5115 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____5115 with
              | FStar_Pervasives_Native.None  ->
                  let uu____5118 =
                    let uu____5123 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____5123)
                     in
                  FStar_Errors.raise_error uu____5118
                    top.FStar_Parser_AST.range
              | uu____5124 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  desugar_name mk1 setpos env true lid'))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____5143 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____5143 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> head2
                   | uu____5154 ->
                       let uu____5161 =
                         FStar_Util.take
                           (fun uu____5185  ->
                              match uu____5185 with
                              | (uu____5190,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____5161 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let args2 =
                              FStar_List.map
                                (fun uu____5254  ->
                                   match uu____5254 with
                                   | (t,imp) ->
                                       let te = desugar_term env t  in
                                       arg_withimp_e imp te) args1
                               in
                            let head3 =
                              if universes1 = []
                              then head2
                              else
                                mk1
                                  (FStar_Syntax_Syntax.Tm_uinst
                                     (head2, universes1))
                               in
                            mk1 (FStar_Syntax_Syntax.Tm_app (head3, args2))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____5295 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____5295 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.strcat "Constructor "
                             (Prims.strcat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____5302 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.strcat "Effect "
                             (Prims.strcat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____5309 =
              FStar_List.fold_left
                (fun uu____5354  ->
                   fun b  ->
                     match uu____5354 with
                     | (env1,tparams,typs) ->
                         let uu____5411 = desugar_binder env1 b  in
                         (match uu____5411 with
                          | (xopt,t1) ->
                              let uu____5440 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____5449 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____5449)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____5440 with
                               | (env2,x) ->
                                   let uu____5469 =
                                     let uu____5472 =
                                       let uu____5475 =
                                         let uu____5476 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____5476
                                          in
                                       [uu____5475]  in
                                     FStar_List.append typs uu____5472  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___126_5502 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___126_5502.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___126_5502.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____5469)))) (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      FStar_Pervasives_Native.None])
               in
            (match uu____5309 with
             | (env1,uu____5526,targs) ->
                 let uu____5548 =
                   let uu____5553 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____5553
                    in
                 (match uu____5548 with
                  | (tup,uu____5559) ->
                      FStar_All.pipe_left mk1
                        (FStar_Syntax_Syntax.Tm_app (tup, targs))))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____5570 = uncurry binders t  in
            (match uu____5570 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___92_5602 =
                   match uu___92_5602 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1  in
                       let uu____5616 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____5616
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____5638 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____5638 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 aux env [] bs)
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____5653 = desugar_binder env b  in
            (match uu____5653 with
             | (FStar_Pervasives_Native.None ,uu____5660) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____5670 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____5670 with
                  | ((x,uu____5676),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____5683 = FStar_Syntax_Util.refine x f1  in
                      FStar_All.pipe_left setpos uu____5683))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern)
               in
            let uu____5703 =
              FStar_List.fold_left
                (fun uu____5723  ->
                   fun pat  ->
                     match uu____5723 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed (uu____5749,t) ->
                              let uu____5751 =
                                let uu____5754 = free_type_vars env1 t  in
                                FStar_List.append uu____5754 ftvs  in
                              (env1, uu____5751)
                          | uu____5759 -> (env1, ftvs))) (env, []) binders1
               in
            (match uu____5703 with
             | (uu____5764,ftv) ->
                 let ftv1 = sort_ftv ftv  in
                 let binders2 =
                   let uu____5776 =
                     FStar_All.pipe_right ftv1
                       (FStar_List.map
                          (fun a  ->
                             FStar_Parser_AST.mk_pattern
                               (FStar_Parser_AST.PatTvar
                                  (a,
                                    (FStar_Pervasives_Native.Some
                                       FStar_Parser_AST.Implicit)))
                               top.FStar_Parser_AST.range))
                      in
                   FStar_List.append uu____5776 binders1  in
                 let rec aux env1 bs sc_pat_opt uu___93_5817 =
                   match uu___93_5817 with
                   | [] ->
                       let body1 = desugar_term env1 body  in
                       let body2 =
                         match sc_pat_opt with
                         | FStar_Pervasives_Native.Some (sc,pat) ->
                             let body2 =
                               let uu____5855 =
                                 let uu____5856 =
                                   FStar_Syntax_Syntax.pat_bvs pat  in
                                 FStar_All.pipe_right uu____5856
                                   (FStar_List.map
                                      FStar_Syntax_Syntax.mk_binder)
                                  in
                               FStar_Syntax_Subst.close uu____5855 body1  in
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_match
                                  (sc,
                                    [(pat, FStar_Pervasives_Native.None,
                                       body2)])) FStar_Pervasives_Native.None
                               body2.FStar_Syntax_Syntax.pos
                         | FStar_Pervasives_Native.None  -> body1  in
                       let uu____5909 =
                         no_annot_abs (FStar_List.rev bs) body2  in
                       setpos uu____5909
                   | p::rest ->
                       let uu____5920 = desugar_binding_pat env1 p  in
                       (match uu____5920 with
                        | (env2,b,pat) ->
                            let pat1 =
                              match pat with
                              | [] -> FStar_Pervasives_Native.None
                              | p1::[] -> FStar_Pervasives_Native.Some p1
                              | uu____5944 ->
                                  FStar_Errors.raise_error
                                    (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                      "Disjunctive patterns are not supported in abstractions")
                                    p.FStar_Parser_AST.prange
                               in
                            let uu____5949 =
                              match b with
                              | LetBinder uu____5982 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat1, sc_pat_opt) with
                                    | (FStar_Pervasives_Native.None
                                       ,uu____6032) -> sc_pat_opt
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.None ) ->
                                        let uu____6068 =
                                          let uu____6073 =
                                            FStar_Syntax_Syntax.bv_to_name x
                                             in
                                          (uu____6073, p1)  in
                                        FStar_Pervasives_Native.Some
                                          uu____6068
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.Some
                                       (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____6109,uu____6110) ->
                                             let tup2 =
                                               let uu____6112 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____6112
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____6116 =
                                                 let uu____6119 =
                                                   let uu____6120 =
                                                     let uu____6135 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2)
                                                        in
                                                     let uu____6138 =
                                                       let uu____6141 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc
                                                          in
                                                       let uu____6142 =
                                                         let uu____6145 =
                                                           let uu____6146 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x
                                                              in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____6146
                                                            in
                                                         [uu____6145]  in
                                                       uu____6141 ::
                                                         uu____6142
                                                        in
                                                     (uu____6135, uu____6138)
                                                      in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____6120
                                                    in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____6119
                                                  in
                                               uu____6116
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Parser_AST.range
                                                in
                                             let p2 =
                                               let uu____6157 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p1, false)]))
                                                 uu____6157
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____6188,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____6190,pats)) ->
                                             let tupn =
                                               let uu____6229 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____6229
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____6239 =
                                                 let uu____6240 =
                                                   let uu____6255 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn)
                                                      in
                                                   let uu____6258 =
                                                     let uu____6267 =
                                                       let uu____6276 =
                                                         let uu____6277 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____6277
                                                          in
                                                       [uu____6276]  in
                                                     FStar_List.append args
                                                       uu____6267
                                                      in
                                                   (uu____6255, uu____6258)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____6240
                                                  in
                                               mk1 uu____6239  in
                                             let p2 =
                                               let uu____6297 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p1, false)])))
                                                 uu____6297
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | uu____6332 ->
                                             failwith "Impossible")
                                     in
                                  ((x, aq), sc_pat_opt1)
                               in
                            (match uu____5949 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest))
                    in
                 aux env [] FStar_Pervasives_Native.None binders2)
        | FStar_Parser_AST.App
            (uu____6399,uu____6400,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____6414 =
                let uu____6415 = unparen e  in uu____6415.FStar_Parser_AST.tm
                 in
              match uu____6414 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____6421 ->
                  let head1 = desugar_term env e  in
                  mk1 (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
               in
            aux [] top
        | FStar_Parser_AST.App uu____6425 ->
            let rec aux args e =
              let uu____6457 =
                let uu____6458 = unparen e  in uu____6458.FStar_Parser_AST.tm
                 in
              match uu____6457 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let arg =
                    let uu____6471 = desugar_term env t  in
                    FStar_All.pipe_left (arg_withimp_e imp) uu____6471  in
                  aux (arg :: args) e1
              | uu____6484 ->
                  let head1 = desugar_term env e  in
                  mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))
               in
            aux [] top
        | FStar_Parser_AST.Bind (x,t1,t2) ->
            let tac_bind_lid =
              FStar_Ident.lid_of_path ["FStar"; "Tactics"; "Effect"; "bind"]
                x.FStar_Ident.idRange
               in
            let xpat =
              FStar_Parser_AST.mk_pattern
                (FStar_Parser_AST.PatVar (x, FStar_Pervasives_Native.None))
                x.FStar_Ident.idRange
               in
            let k =
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Abs ([xpat], t2))
                t2.FStar_Parser_AST.range t2.FStar_Parser_AST.level
               in
            let bind_lid =
              FStar_Ident.lid_of_path ["bind"] x.FStar_Ident.idRange  in
            let bind1 =
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Var bind_lid)
                x.FStar_Ident.idRange FStar_Parser_AST.Expr
               in
            let uu____6512 =
              FStar_Syntax_DsEnv.resolve_to_fully_qualified_name env bind_lid
               in
            (match uu____6512 with
             | FStar_Pervasives_Native.Some flid when
                 FStar_Ident.lid_equals flid tac_bind_lid ->
                 let r =
                   FStar_Parser_AST.mk_term
                     (FStar_Parser_AST.Const
                        (FStar_Const.Const_range (t2.FStar_Parser_AST.range)))
                     t2.FStar_Parser_AST.range FStar_Parser_AST.Expr
                    in
                 let uu____6517 =
                   FStar_Parser_AST.mkExplicitApp bind1 [r; t1; k]
                     top.FStar_Parser_AST.range
                    in
                 desugar_term env uu____6517
             | uu____6518 ->
                 let uu____6521 =
                   FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                     top.FStar_Parser_AST.range
                    in
                 desugar_term env uu____6521)
        | FStar_Parser_AST.Seq (t1,t2) ->
            let uu____6524 =
              let uu____6525 =
                let uu____6532 =
                  desugar_term env
                    (FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Let
                          (FStar_Parser_AST.NoLetQualifier,
                            [(FStar_Pervasives_Native.None,
                               ((FStar_Parser_AST.mk_pattern
                                   FStar_Parser_AST.PatWild
                                   t1.FStar_Parser_AST.range), t1))], t2))
                       top.FStar_Parser_AST.range FStar_Parser_AST.Expr)
                   in
                (uu____6532,
                  (FStar_Syntax_Syntax.Meta_desugared
                     FStar_Syntax_Syntax.Sequence))
                 in
              FStar_Syntax_Syntax.Tm_meta uu____6525  in
            mk1 uu____6524
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____6584 =
              let uu____6589 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____6589 then desugar_typ else desugar_term  in
            uu____6584 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____6632 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____6757  ->
                        match uu____6757 with
                        | (attr_opt,(p,def)) ->
                            let uu____6809 = is_app_pattern p  in
                            if uu____6809
                            then
                              let uu____6834 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____6834, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____6898 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____6898, def1)
                               | uu____6931 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____6963);
                                           FStar_Parser_AST.prange =
                                             uu____6964;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____6994 =
                                            let uu____7009 =
                                              let uu____7014 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____7014  in
                                            (uu____7009, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____6994, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____7069) ->
                                        if top_level
                                        then
                                          let uu____7098 =
                                            let uu____7113 =
                                              let uu____7118 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____7118  in
                                            (uu____7113, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____7098, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____7172 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____7197 =
                FStar_List.fold_left
                  (fun uu____7264  ->
                     fun uu____7265  ->
                       match (uu____7264, uu____7265) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____7361,uu____7362),uu____7363))
                           ->
                           let uu____7456 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____7482 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____7482 with
                                  | (env2,xx) ->
                                      let uu____7501 =
                                        let uu____7504 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____7504 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx), uu____7501))
                             | FStar_Util.Inr l ->
                                 let uu____7512 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.Delta_equational
                                    in
                                 (uu____7512, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____7456 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____7197 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____7644 =
                    match uu____7644 with
                    | (attrs_opt,(uu____7674,args,result_t),def) ->
                        let args1 =
                          FStar_All.pipe_right args
                            (FStar_List.map replace_unit_pattern)
                           in
                        let def1 =
                          match result_t with
                          | FStar_Pervasives_Native.None  -> def
                          | FStar_Pervasives_Native.Some t ->
                              let t1 =
                                let uu____7726 = is_comp_type env1 t  in
                                if uu____7726
                                then
                                  ((let uu____7728 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____7738 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____7738))
                                       in
                                    match uu____7728 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____7741 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____7743 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____7743))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____7741
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t)
                                 in
                              let uu____7747 =
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range
                                 in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed
                                   (def, t1, FStar_Pervasives_Native.None))
                                uu____7747 FStar_Parser_AST.Expr
                           in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____7751 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level
                           in
                        let body1 = desugar_term env1 def2  in
                        let lbname1 =
                          match lbname with
                          | FStar_Util.Inl x -> FStar_Util.Inl x
                          | FStar_Util.Inr l ->
                              let uu____7766 =
                                let uu____7767 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____7767
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____7766
                           in
                        let body2 =
                          if is_rec
                          then FStar_Syntax_Subst.close rec_bindings1 body1
                          else body1  in
                        let attrs =
                          match attrs_opt with
                          | FStar_Pervasives_Native.None  -> []
                          | FStar_Pervasives_Native.Some l ->
                              FStar_List.map (desugar_term env1) l
                           in
                        mk_lb
                          (attrs, lbname1, FStar_Syntax_Syntax.tun, body2)
                     in
                  let lbs1 =
                    FStar_List.map2
                      (desugar_one_def (if is_rec then env' else env))
                      fnames1 funs
                     in
                  let body1 = desugar_term env' body  in
                  let uu____7821 =
                    let uu____7822 =
                      let uu____7835 =
                        FStar_Syntax_Subst.close rec_bindings1 body1  in
                      ((is_rec, lbs1), uu____7835)  in
                    FStar_Syntax_Syntax.Tm_let uu____7822  in
                  FStar_All.pipe_left mk1 uu____7821
               in
            let ds_non_rec attrs_opt pat t1 t2 =
              let attrs =
                match attrs_opt with
                | FStar_Pervasives_Native.None  -> []
                | FStar_Pervasives_Native.Some l ->
                    FStar_List.map (desugar_term env) l
                 in
              let t11 = desugar_term env t1  in
              let is_mutable = qual = FStar_Parser_AST.Mutable  in
              let t12 = if is_mutable then mk_ref_alloc t11 else t11  in
              let uu____7889 =
                desugar_binding_pat_maybe_top top_level env pat is_mutable
                 in
              match uu____7889 with
              | (env1,binder,pat1) ->
                  let tm =
                    match binder with
                    | LetBinder (l,t) ->
                        let body1 = desugar_term env1 t2  in
                        let fv =
                          let uu____7916 =
                            FStar_Syntax_Util.incr_delta_qualifier t12  in
                          FStar_Syntax_Syntax.lid_as_fv l uu____7916
                            FStar_Pervasives_Native.None
                           in
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_let
                             ((false,
                                [mk_lb (attrs, (FStar_Util.Inr fv), t, t12)]),
                               body1))
                    | LocalBinder (x,uu____7936) ->
                        let body1 = desugar_term env1 t2  in
                        let body2 =
                          match pat1 with
                          | [] -> body1
                          | {
                              FStar_Syntax_Syntax.v =
                                FStar_Syntax_Syntax.Pat_wild uu____7939;
                              FStar_Syntax_Syntax.p = uu____7940;_}::[] ->
                              body1
                          | uu____7945 ->
                              let uu____7948 =
                                let uu____7951 =
                                  let uu____7952 =
                                    let uu____7975 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    let uu____7976 =
                                      desugar_disjunctive_pattern pat1
                                        FStar_Pervasives_Native.None body1
                                       in
                                    (uu____7975, uu____7976)  in
                                  FStar_Syntax_Syntax.Tm_match uu____7952  in
                                FStar_Syntax_Syntax.mk uu____7951  in
                              uu____7948 FStar_Pervasives_Native.None
                                top.FStar_Parser_AST.range
                           in
                        let uu____7986 =
                          let uu____7987 =
                            let uu____8000 =
                              let uu____8001 =
                                let uu____8002 =
                                  FStar_Syntax_Syntax.mk_binder x  in
                                [uu____8002]  in
                              FStar_Syntax_Subst.close uu____8001 body2  in
                            ((false,
                               [mk_lb
                                  (attrs, (FStar_Util.Inl x),
                                    (x.FStar_Syntax_Syntax.sort), t12)]),
                              uu____8000)
                             in
                          FStar_Syntax_Syntax.Tm_let uu____7987  in
                        FStar_All.pipe_left mk1 uu____7986
                     in
                  if is_mutable
                  then
                    FStar_All.pipe_left mk1
                      (FStar_Syntax_Syntax.Tm_meta
                         (tm,
                           (FStar_Syntax_Syntax.Meta_desugared
                              FStar_Syntax_Syntax.Mutable_alloc)))
                  else tm
               in
            let uu____8030 = FStar_List.hd lbs  in
            (match uu____8030 with
             | (attrs,(head_pat,defn)) ->
                 let uu____8070 = is_rec || (is_app_pattern head_pat)  in
                 if uu____8070
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____8079 =
                let uu____8080 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.Delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____8080  in
              mk1 uu____8079  in
            let uu____8081 =
              let uu____8082 =
                let uu____8105 =
                  let uu____8108 = desugar_term env t1  in
                  FStar_Syntax_Util.ascribe uu____8108
                    ((FStar_Util.Inl t_bool1), FStar_Pervasives_Native.None)
                   in
                let uu____8129 =
                  let uu____8144 =
                    let uu____8157 =
                      FStar_Syntax_Syntax.withinfo
                        (FStar_Syntax_Syntax.Pat_constant
                           (FStar_Const.Const_bool true))
                        t2.FStar_Parser_AST.range
                       in
                    let uu____8160 = desugar_term env t2  in
                    (uu____8157, FStar_Pervasives_Native.None, uu____8160)
                     in
                  let uu____8169 =
                    let uu____8184 =
                      let uu____8197 =
                        FStar_Syntax_Syntax.withinfo
                          (FStar_Syntax_Syntax.Pat_wild x)
                          t3.FStar_Parser_AST.range
                         in
                      let uu____8200 = desugar_term env t3  in
                      (uu____8197, FStar_Pervasives_Native.None, uu____8200)
                       in
                    [uu____8184]  in
                  uu____8144 :: uu____8169  in
                (uu____8105, uu____8129)  in
              FStar_Syntax_Syntax.Tm_match uu____8082  in
            mk1 uu____8081
        | FStar_Parser_AST.TryWith (e,branches) ->
            let r = top.FStar_Parser_AST.range  in
            let handler = FStar_Parser_AST.mk_function branches r r  in
            let body =
              FStar_Parser_AST.mk_function
                [((FStar_Parser_AST.mk_pattern
                     (FStar_Parser_AST.PatConst FStar_Const.Const_unit) r),
                   FStar_Pervasives_Native.None, e)] r r
               in
            let a1 =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   ((FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Var FStar_Parser_Const.try_with_lid)
                       r top.FStar_Parser_AST.level), body,
                     FStar_Parser_AST.Nothing)) r top.FStar_Parser_AST.level
               in
            let a2 =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App (a1, handler, FStar_Parser_AST.Nothing))
                r top.FStar_Parser_AST.level
               in
            desugar_term env a2
        | FStar_Parser_AST.Match (e,branches) ->
            let desugar_branch uu____8341 =
              match uu____8341 with
              | (pat,wopt,b) ->
                  let uu____8359 = desugar_match_pat env pat  in
                  (match uu____8359 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____8380 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____8380
                          in
                       let b1 = desugar_term env1 b  in
                       desugar_disjunctive_pattern pat1 wopt1 b1)
               in
            let uu____8382 =
              let uu____8383 =
                let uu____8406 = desugar_term env e  in
                let uu____8407 = FStar_List.collect desugar_branch branches
                   in
                (uu____8406, uu____8407)  in
              FStar_Syntax_Syntax.Tm_match uu____8383  in
            FStar_All.pipe_left mk1 uu____8382
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____8436 = is_comp_type env t  in
              if uu____8436
              then
                let uu____8443 = desugar_comp t.FStar_Parser_AST.range env t
                   in
                FStar_Util.Inr uu____8443
              else
                (let uu____8449 = desugar_term env t  in
                 FStar_Util.Inl uu____8449)
               in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)  in
            let uu____8455 =
              let uu____8456 =
                let uu____8483 = desugar_term env e  in
                (uu____8483, (annot, tac_opt1), FStar_Pervasives_Native.None)
                 in
              FStar_Syntax_Syntax.Tm_ascribed uu____8456  in
            FStar_All.pipe_left mk1 uu____8455
        | FStar_Parser_AST.Record (uu____8508,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____8545 = FStar_List.hd fields  in
              match uu____8545 with | (f,uu____8557) -> f.FStar_Ident.ns  in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____8599  ->
                        match uu____8599 with
                        | (g,uu____8605) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____8611,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____8625 =
                         let uu____8630 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____8630)
                          in
                       FStar_Errors.raise_error uu____8625
                         top.FStar_Parser_AST.range
                   | FStar_Pervasives_Native.Some x ->
                       (fn,
                         (FStar_Parser_AST.mk_term
                            (FStar_Parser_AST.Project (x, fn))
                            x.FStar_Parser_AST.range x.FStar_Parser_AST.level)))
               in
            let user_constrname =
              FStar_Ident.lid_of_ids
                (FStar_List.append user_ns
                   [record.FStar_Syntax_DsEnv.constrname])
               in
            let recterm =
              match eopt with
              | FStar_Pervasives_Native.None  ->
                  let uu____8638 =
                    let uu____8649 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____8680  ->
                              match uu____8680 with
                              | (f,uu____8690) ->
                                  let uu____8691 =
                                    let uu____8692 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____8692
                                     in
                                  (uu____8691, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____8649)  in
                  FStar_Parser_AST.Construct uu____8638
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____8710 =
                      let uu____8711 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____8711  in
                    FStar_Parser_AST.mk_term uu____8710 x.FStar_Ident.idRange
                      FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____8713 =
                      let uu____8726 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____8756  ->
                                match uu____8756 with
                                | (f,uu____8766) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____8726)  in
                    FStar_Parser_AST.Record uu____8713  in
                  FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier,
                      [(FStar_Pervasives_Native.None,
                         ((FStar_Parser_AST.mk_pattern
                             (FStar_Parser_AST.PatVar
                                (x, FStar_Pervasives_Native.None))
                             x.FStar_Ident.idRange), e))],
                      (FStar_Parser_AST.mk_term record1
                         top.FStar_Parser_AST.range
                         top.FStar_Parser_AST.level))
               in
            let recterm1 =
              FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let e = desugar_term env recterm1  in
            (match e.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_app
                 ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                    FStar_Syntax_Syntax.pos = uu____8828;
                    FStar_Syntax_Syntax.vars = uu____8829;_},args)
                 ->
                 let uu____8851 =
                   let uu____8852 =
                     let uu____8867 =
                       let uu____8868 =
                         let uu____8871 =
                           let uu____8872 =
                             let uu____8879 =
                               FStar_All.pipe_right
                                 record.FStar_Syntax_DsEnv.fields
                                 (FStar_List.map FStar_Pervasives_Native.fst)
                                in
                             ((record.FStar_Syntax_DsEnv.typename),
                               uu____8879)
                              in
                           FStar_Syntax_Syntax.Record_ctor uu____8872  in
                         FStar_Pervasives_Native.Some uu____8871  in
                       FStar_Syntax_Syntax.fvar
                         (FStar_Ident.set_lid_range
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            e.FStar_Syntax_Syntax.pos)
                         FStar_Syntax_Syntax.Delta_constant uu____8868
                        in
                     (uu____8867, args)  in
                   FStar_Syntax_Syntax.Tm_app uu____8852  in
                 FStar_All.pipe_left mk1 uu____8851
             | uu____8906 -> e)
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____8910 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____8910 with
              | (constrname,is_rec) ->
                  let e1 = desugar_term env e  in
                  let projname =
                    FStar_Syntax_Util.mk_field_projector_name_from_ident
                      constrname f.FStar_Ident.ident
                     in
                  let qual =
                    if is_rec
                    then
                      FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Record_projector
                           (constrname, (f.FStar_Ident.ident)))
                    else FStar_Pervasives_Native.None  in
                  let uu____8929 =
                    let uu____8930 =
                      let uu____8945 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range projname
                             (FStar_Ident.range_of_lid f))
                          FStar_Syntax_Syntax.Delta_equational qual
                         in
                      let uu____8946 =
                        let uu____8949 = FStar_Syntax_Syntax.as_arg e1  in
                        [uu____8949]  in
                      (uu____8945, uu____8946)  in
                    FStar_Syntax_Syntax.Tm_app uu____8930  in
                  FStar_All.pipe_left mk1 uu____8929))
        | FStar_Parser_AST.NamedTyp (uu____8954,e) -> desugar_term env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.Quote (e,qopen) ->
            let uu____8959 =
              let uu____8960 =
                let uu____8967 =
                  let uu____8968 =
                    let uu____8975 = desugar_term env e  in
                    (uu____8975, { FStar_Syntax_Syntax.qopen = qopen })  in
                  FStar_Syntax_Syntax.Meta_quoted uu____8968  in
                (FStar_Syntax_Syntax.tun, uu____8967)  in
              FStar_Syntax_Syntax.Tm_meta uu____8960  in
            FStar_All.pipe_left mk1 uu____8959
        | uu____8978 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            desugar_formula env top
        | uu____8979 ->
            let uu____8980 =
              let uu____8985 =
                let uu____8986 = FStar_Parser_AST.term_to_string top  in
                Prims.strcat "Unexpected term" uu____8986  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____8985)  in
            FStar_Errors.raise_error uu____8980 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____8988 -> false
    | uu____8997 -> true

and (is_synth_by_tactic :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (l,r,FStar_Parser_AST.Hash ) ->
          is_synth_by_tactic e l
      | FStar_Parser_AST.Var lid ->
          let uu____9003 =
            FStar_Syntax_DsEnv.resolve_to_fully_qualified_name e lid  in
          (match uu____9003 with
           | FStar_Pervasives_Native.Some lid1 ->
               FStar_Ident.lid_equals lid1 FStar_Parser_Const.synth_lid
           | FStar_Pervasives_Native.None  -> false)
      | uu____9007 -> false

and (desugar_args :
  FStar_Syntax_DsEnv.env ->
    (FStar_Parser_AST.term,FStar_Parser_AST.imp)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.arg_qualifier
                                  FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun env  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____9044  ->
              match uu____9044 with
              | (a,imp) ->
                  let uu____9057 = desugar_term env a  in
                  arg_withimp_e imp uu____9057))

and (desugar_comp :
  FStar_Range.range ->
    FStar_Syntax_DsEnv.env ->
      FStar_Parser_AST.term ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun r  ->
    fun env  ->
      fun t  ->
        let fail a err = FStar_Errors.raise_error err r  in
        let is_requires uu____9083 =
          match uu____9083 with
          | (t1,uu____9089) ->
              let uu____9090 =
                let uu____9091 = unparen t1  in
                uu____9091.FStar_Parser_AST.tm  in
              (match uu____9090 with
               | FStar_Parser_AST.Requires uu____9092 -> true
               | uu____9099 -> false)
           in
        let is_ensures uu____9107 =
          match uu____9107 with
          | (t1,uu____9113) ->
              let uu____9114 =
                let uu____9115 = unparen t1  in
                uu____9115.FStar_Parser_AST.tm  in
              (match uu____9114 with
               | FStar_Parser_AST.Ensures uu____9116 -> true
               | uu____9123 -> false)
           in
        let is_app head1 uu____9134 =
          match uu____9134 with
          | (t1,uu____9140) ->
              let uu____9141 =
                let uu____9142 = unparen t1  in
                uu____9142.FStar_Parser_AST.tm  in
              (match uu____9141 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____9144;
                      FStar_Parser_AST.level = uu____9145;_},uu____9146,uu____9147)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____9148 -> false)
           in
        let is_smt_pat uu____9156 =
          match uu____9156 with
          | (t1,uu____9162) ->
              let uu____9163 =
                let uu____9164 = unparen t1  in
                uu____9164.FStar_Parser_AST.tm  in
              (match uu____9163 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____9167);
                             FStar_Parser_AST.range = uu____9168;
                             FStar_Parser_AST.level = uu____9169;_},uu____9170)::uu____9171::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["SMTPat"; "SMTPatT"; "SMTPatOr"])
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Var
                               smtpat;
                             FStar_Parser_AST.range = uu____9210;
                             FStar_Parser_AST.level = uu____9211;_},uu____9212)::uu____9213::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
               | uu____9238 -> false)
           in
        let is_decreases = is_app "decreases"  in
        let pre_process_comp_typ t1 =
          let uu____9266 = head_and_args t1  in
          match uu____9266 with
          | (head1,args) ->
              (match head1.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Name lemma when
                   (lemma.FStar_Ident.ident).FStar_Ident.idText = "Lemma" ->
                   let unit_tm =
                     ((FStar_Parser_AST.mk_term
                         (FStar_Parser_AST.Name FStar_Parser_Const.unit_lid)
                         t1.FStar_Parser_AST.range
                         FStar_Parser_AST.Type_level),
                       FStar_Parser_AST.Nothing)
                      in
                   let nil_pat =
                     ((FStar_Parser_AST.mk_term
                         (FStar_Parser_AST.Name FStar_Parser_Const.nil_lid)
                         t1.FStar_Parser_AST.range FStar_Parser_AST.Expr),
                       FStar_Parser_AST.Nothing)
                      in
                   let req_true =
                     let req =
                       FStar_Parser_AST.Requires
                         ((FStar_Parser_AST.mk_term
                             (FStar_Parser_AST.Name
                                FStar_Parser_Const.true_lid)
                             t1.FStar_Parser_AST.range
                             FStar_Parser_AST.Formula),
                           FStar_Pervasives_Native.None)
                        in
                     ((FStar_Parser_AST.mk_term req t1.FStar_Parser_AST.range
                         FStar_Parser_AST.Type_level),
                       FStar_Parser_AST.Nothing)
                      in
                   let thunk_ens_ ens =
                     let wildpat =
                       FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild
                         ens.FStar_Parser_AST.range
                        in
                     FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Abs ([wildpat], ens))
                       ens.FStar_Parser_AST.range FStar_Parser_AST.Expr
                      in
                   let thunk_ens uu____9360 =
                     match uu____9360 with
                     | (e,i) ->
                         let uu____9371 = thunk_ens_ e  in (uu____9371, i)
                      in
                   let fail_lemma uu____9381 =
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
                       "Lemma (requires pre) (ensures post) (decreases d) [SMTPat ...]"]
                        in
                     let msg = FStar_String.concat "\n\t" expected_one_of  in
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_InvalidLemmaArgument,
                         (Prims.strcat
                            "Invalid arguments to 'Lemma'; expected one of the following:\n\t"
                            msg)) t1.FStar_Parser_AST.range
                      in
                   let args1 =
                     match args with
                     | [] -> fail_lemma ()
                     | req::[] when is_requires req -> fail_lemma ()
                     | smtpat::[] when is_smt_pat smtpat -> fail_lemma ()
                     | dec::[] when is_decreases dec -> fail_lemma ()
                     | ens::[] ->
                         let uu____9461 =
                           let uu____9468 =
                             let uu____9475 = thunk_ens ens  in
                             [uu____9475; nil_pat]  in
                           req_true :: uu____9468  in
                         unit_tm :: uu____9461
                     | req::ens::[] when
                         (is_requires req) && (is_ensures ens) ->
                         let uu____9522 =
                           let uu____9529 =
                             let uu____9536 = thunk_ens ens  in
                             [uu____9536; nil_pat]  in
                           req :: uu____9529  in
                         unit_tm :: uu____9522
                     | ens::smtpat::[] when
                         (((let uu____9585 = is_requires ens  in
                            Prims.op_Negation uu____9585) &&
                             (let uu____9587 = is_smt_pat ens  in
                              Prims.op_Negation uu____9587))
                            &&
                            (let uu____9589 = is_decreases ens  in
                             Prims.op_Negation uu____9589))
                           && (is_smt_pat smtpat)
                         ->
                         let uu____9590 =
                           let uu____9597 =
                             let uu____9604 = thunk_ens ens  in
                             [uu____9604; smtpat]  in
                           req_true :: uu____9597  in
                         unit_tm :: uu____9590
                     | ens::dec::[] when
                         (is_ensures ens) && (is_decreases dec) ->
                         let uu____9651 =
                           let uu____9658 =
                             let uu____9665 = thunk_ens ens  in
                             [uu____9665; nil_pat; dec]  in
                           req_true :: uu____9658  in
                         unit_tm :: uu____9651
                     | ens::dec::smtpat::[] when
                         ((is_ensures ens) && (is_decreases dec)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____9725 =
                           let uu____9732 =
                             let uu____9739 = thunk_ens ens  in
                             [uu____9739; smtpat; dec]  in
                           req_true :: uu____9732  in
                         unit_tm :: uu____9725
                     | req::ens::dec::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_decreases dec)
                         ->
                         let uu____9799 =
                           let uu____9806 =
                             let uu____9813 = thunk_ens ens  in
                             [uu____9813; nil_pat; dec]  in
                           req :: uu____9806  in
                         unit_tm :: uu____9799
                     | req::ens::smtpat::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____9873 =
                           let uu____9880 =
                             let uu____9887 = thunk_ens ens  in
                             [uu____9887; smtpat]  in
                           req :: uu____9880  in
                         unit_tm :: uu____9873
                     | req::ens::dec::smtpat::[] when
                         (((is_requires req) && (is_ensures ens)) &&
                            (is_smt_pat smtpat))
                           && (is_decreases dec)
                         ->
                         let uu____9952 =
                           let uu____9959 =
                             let uu____9966 = thunk_ens ens  in
                             [uu____9966; dec; smtpat]  in
                           req :: uu____9959  in
                         unit_tm :: uu____9952
                     | _other -> fail_lemma ()  in
                   let head_and_attributes =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) lemma
                      in
                   (head_and_attributes, args1)
               | FStar_Parser_AST.Name l when
                   FStar_Syntax_DsEnv.is_effect_name env l ->
                   let uu____10028 =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) l
                      in
                   (uu____10028, args)
               | FStar_Parser_AST.Name l when
                   (let uu____10056 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____10056
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Parser_Const.effect_Tot_lid
                        head1.FStar_Parser_AST.range), []), args)
               | FStar_Parser_AST.Name l when
                   (let uu____10074 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____10074
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
               | uu____10112 ->
                   let default_effect =
                     let uu____10114 = FStar_Options.ml_ish ()  in
                     if uu____10114
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____10117 =
                           FStar_Options.warn_default_effects ()  in
                         if uu____10117
                         then
                           FStar_Errors.log_issue
                             head1.FStar_Parser_AST.range
                             (FStar_Errors.Warning_UseDefaultEffect,
                               "Using default effect Tot")
                         else ());
                        FStar_Parser_Const.effect_Tot_lid)
                      in
                   (((FStar_Ident.set_lid_range default_effect
                        head1.FStar_Parser_AST.range), []),
                     [(t1, FStar_Parser_AST.Nothing)]))
           in
        let uu____10141 = pre_process_comp_typ t  in
        match uu____10141 with
        | ((eff,cattributes),args) ->
            (Obj.magic
               (if (FStar_List.length args) = (Prims.parse_int "0")
                then
                  Obj.repr
                    (let uu____10190 =
                       let uu____10195 =
                         let uu____10196 =
                           FStar_Syntax_Print.lid_to_string eff  in
                         FStar_Util.format1 "Not enough args to effect %s"
                           uu____10196
                          in
                       (FStar_Errors.Fatal_NotEnoughArgsToEffect,
                         uu____10195)
                        in
                     fail () uu____10190)
                else Obj.repr ());
             (let is_universe uu____10205 =
                match uu____10205 with
                | (uu____10210,imp) -> imp = FStar_Parser_AST.UnivApp  in
              let uu____10212 = FStar_Util.take is_universe args  in
              match uu____10212 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____10271  ->
                         match uu____10271 with
                         | (u,imp) -> desugar_universe u) universes
                     in
                  let uu____10278 =
                    let uu____10293 = FStar_List.hd args1  in
                    let uu____10302 = FStar_List.tl args1  in
                    (uu____10293, uu____10302)  in
                  (match uu____10278 with
                   | (result_arg,rest) ->
                       let result_typ =
                         desugar_typ env
                           (FStar_Pervasives_Native.fst result_arg)
                          in
                       let rest1 = desugar_args env rest  in
                       let uu____10357 =
                         let is_decrease uu____10393 =
                           match uu____10393 with
                           | (t1,uu____10403) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.pos = uu____10413;
                                       FStar_Syntax_Syntax.vars = uu____10414;_},uu____10415::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.decreases_lid
                                | uu____10446 -> false)
                            in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease)
                          in
                       (match uu____10357 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____10560  ->
                                      match uu____10560 with
                                      | (t1,uu____10570) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____10579,(arg,uu____10581)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____10610 -> failwith "impos")))
                               in
                            let no_additional_args =
                              let is_empty a l =
                                match l with
                                | [] -> true
                                | uu____10623 -> false  in
                              (((is_empty () (Obj.magic decreases_clause)) &&
                                  (is_empty () (Obj.magic rest2)))
                                 && (is_empty () (Obj.magic cattributes)))
                                && (is_empty () (Obj.magic universes1))
                               in
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
                                         else []
                                    in
                                 let flags2 =
                                   FStar_List.append flags1 cattributes  in
                                 let rest3 =
                                   if
                                     FStar_Ident.lid_equals eff
                                       FStar_Parser_Const.effect_Lemma_lid
                                   then
                                     match rest2 with
                                     | req::ens::(pat,aq)::[] ->
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
                                                   [FStar_Syntax_Syntax.U_zero]
                                                  in
                                               let pattern =
                                                 FStar_Syntax_Syntax.fvar
                                                   (FStar_Ident.set_lid_range
                                                      FStar_Parser_Const.pattern_lid
                                                      pat.FStar_Syntax_Syntax.pos)
                                                   FStar_Syntax_Syntax.Delta_constant
                                                   FStar_Pervasives_Native.None
                                                  in
                                               FStar_Syntax_Syntax.mk_Tm_app
                                                 nil
                                                 [(pattern,
                                                    (FStar_Pervasives_Native.Some
                                                       FStar_Syntax_Syntax.imp_tag))]
                                                 FStar_Pervasives_Native.None
                                                 pat.FStar_Syntax_Syntax.pos
                                           | uu____10763 -> pat  in
                                         let uu____10764 =
                                           let uu____10775 =
                                             let uu____10786 =
                                               let uu____10795 =
                                                 FStar_Syntax_Syntax.mk
                                                   (FStar_Syntax_Syntax.Tm_meta
                                                      (pat1,
                                                        (FStar_Syntax_Syntax.Meta_desugared
                                                           FStar_Syntax_Syntax.Meta_smt_pat)))
                                                   FStar_Pervasives_Native.None
                                                   pat1.FStar_Syntax_Syntax.pos
                                                  in
                                               (uu____10795, aq)  in
                                             [uu____10786]  in
                                           ens :: uu____10775  in
                                         req :: uu____10764
                                     | uu____10836 -> rest2
                                   else rest2  in
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
  fun env  ->
    fun f  ->
      let connective s =
        match s with
        | "/\\" -> FStar_Pervasives_Native.Some FStar_Parser_Const.and_lid
        | "\\/" -> FStar_Pervasives_Native.Some FStar_Parser_Const.or_lid
        | "==>" -> FStar_Pervasives_Native.Some FStar_Parser_Const.imp_lid
        | "<==>" -> FStar_Pervasives_Native.Some FStar_Parser_Const.iff_lid
        | "~" -> FStar_Pervasives_Native.Some FStar_Parser_Const.not_lid
        | uu____10858 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___127_10875 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___127_10875.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___127_10875.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___128_10909 = b  in
             {
               FStar_Parser_AST.b = (uu___128_10909.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___128_10909.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___128_10909.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____10968 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____10968)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____10981 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____10981 with
             | (env1,a1) ->
                 let a2 =
                   let uu___129_10991 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___129_10991.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___129_10991.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____11013 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____11027 =
                     let uu____11030 =
                       let uu____11031 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____11031]  in
                     no_annot_abs uu____11030 body2  in
                   FStar_All.pipe_left setpos uu____11027  in
                 let uu____11036 =
                   let uu____11037 =
                     let uu____11052 =
                       FStar_Syntax_Syntax.fvar
                         (FStar_Ident.set_lid_range q
                            b.FStar_Parser_AST.brange)
                         (FStar_Syntax_Syntax.Delta_defined_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____11053 =
                       let uu____11056 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____11056]  in
                     (uu____11052, uu____11053)  in
                   FStar_Syntax_Syntax.Tm_app uu____11037  in
                 FStar_All.pipe_left mk1 uu____11036)
        | uu____11061 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____11133 = q (rest, pats, body)  in
              let uu____11140 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____11133 uu____11140
                FStar_Parser_AST.Formula
               in
            let uu____11141 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____11141 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____11150 -> failwith "impossible"  in
      let uu____11153 =
        let uu____11154 = unparen f  in uu____11154.FStar_Parser_AST.tm  in
      match uu____11153 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____11161,uu____11162) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____11173,uu____11174) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____11205 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____11205
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____11241 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____11241
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____11284 -> desugar_term env f

and (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                                                        FStar_Pervasives_Native.option)
                                FStar_Pervasives_Native.tuple2 Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bs  ->
      let uu____11289 =
        FStar_List.fold_left
          (fun uu____11325  ->
             fun b  ->
               match uu____11325 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___130_11377 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___130_11377.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___130_11377.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___130_11377.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____11394 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____11394 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___131_11414 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___131_11414.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___131_11414.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____11431 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____11289 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

and (desugar_binder :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Ident.ident FStar_Pervasives_Native.option,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.TAnnotated (x,t) ->
          let uu____11518 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____11518)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____11523 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____11523)
      | FStar_Parser_AST.TVariable x ->
          let uu____11527 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____11527)
      | FStar_Parser_AST.NoName t ->
          let uu____11535 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____11535)
      | FStar_Parser_AST.Variable x ->
          ((FStar_Pervasives_Native.Some x), FStar_Syntax_Syntax.tun)

let (mk_data_discriminators :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_DsEnv.env ->
      FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun quals  ->
    fun env  ->
      fun datas  ->
        let quals1 =
          FStar_All.pipe_right quals
            (FStar_List.filter
               (fun uu___94_11568  ->
                  match uu___94_11568 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____11569 -> false))
           in
        let quals2 q =
          let uu____11580 =
            (let uu____11583 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____11583) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____11580
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____11596 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng =
                    (FStar_Ident.range_of_lid disc_name);
                  FStar_Syntax_Syntax.sigquals = uu____11596;
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
  fun iquals  ->
    fun fvq  ->
      fun env  ->
        fun lid  ->
          fun fields  ->
            let p = FStar_Ident.range_of_lid lid  in
            let uu____11627 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____11657  ->
                        match uu____11657 with
                        | (x,uu____11665) ->
                            let uu____11666 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____11666 with
                             | (field_name,uu____11674) ->
                                 let only_decl =
                                   ((let uu____11678 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____11678)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____11680 =
                                        let uu____11681 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____11681.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____11680)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____11695 =
                                       FStar_List.filter
                                         (fun uu___95_11699  ->
                                            match uu___95_11699 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____11700 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____11695
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___96_11713  ->
                                             match uu___96_11713 with
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____11714 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
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
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____11722 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____11722
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          FStar_Syntax_Syntax.Delta_equational
                                      else
                                        FStar_Syntax_Syntax.Delta_equational
                                       in
                                    let lb =
                                      let uu____11727 =
                                        let uu____11732 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____11732  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____11727;
                                        FStar_Syntax_Syntax.lbunivs = [];
                                        FStar_Syntax_Syntax.lbtyp =
                                          FStar_Syntax_Syntax.tun;
                                        FStar_Syntax_Syntax.lbeff =
                                          FStar_Parser_Const.effect_Tot_lid;
                                        FStar_Syntax_Syntax.lbdef =
                                          FStar_Syntax_Syntax.tun;
                                        FStar_Syntax_Syntax.lbattrs = []
                                      }  in
                                    let impl =
                                      let uu____11736 =
                                        let uu____11737 =
                                          let uu____11744 =
                                            let uu____11747 =
                                              let uu____11748 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____11748
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____11747]  in
                                          ((false, [lb]), uu____11744)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____11737
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____11736;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____11627 FStar_List.flatten
  
let (mk_data_projector_names :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_DsEnv.env ->
      FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun iquals  ->
    fun env  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_datacon
            (lid,uu____11792,t,uu____11794,n1,uu____11796) when
            Prims.op_Negation
              (FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid)
            ->
            let uu____11801 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____11801 with
             | (formals,uu____11817) ->
                 (match formals with
                  | [] -> []
                  | uu____11840 ->
                      let filter_records uu___97_11852 =
                        match uu___97_11852 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____11855,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____11867 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____11869 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____11869 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Syntax_Syntax.Data_ctor
                        | FStar_Pervasives_Native.Some q -> q  in
                      let iquals1 =
                        if
                          FStar_List.contains FStar_Syntax_Syntax.Abstract
                            iquals
                        then FStar_Syntax_Syntax.Private :: iquals
                        else iquals  in
                      let uu____11879 = FStar_Util.first_N n1 formals  in
                      (match uu____11879 with
                       | (uu____11902,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____11928 -> []
  
let (mk_typ_abbrev :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.typ ->
          FStar_Syntax_Syntax.term ->
            FStar_Ident.lident Prims.list ->
              FStar_Syntax_Syntax.qualifier Prims.list ->
                FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun lid  ->
    fun uvs  ->
      fun typars  ->
        fun k  ->
          fun t  ->
            fun lids  ->
              fun quals  ->
                fun rng  ->
                  let dd =
                    let uu____11978 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____11978
                    then
                      let uu____11981 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____11981
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____11984 =
                      let uu____11989 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____11989  in
                    let uu____11990 =
                      let uu____11993 = FStar_Syntax_Syntax.mk_Total k  in
                      FStar_Syntax_Util.arrow typars uu____11993  in
                    let uu____11996 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____11984;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____11990;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____11996;
                      FStar_Syntax_Syntax.lbattrs = []
                    }  in
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
          (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      fun quals  ->
        fun tcs  ->
          let rng = d.FStar_Parser_AST.drange  in
          let tycon_id uu___98_12043 =
            match uu___98_12043 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____12045,uu____12046) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____12056,uu____12057,uu____12058) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____12068,uu____12069,uu____12070) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____12100,uu____12101,uu____12102) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____12144) ->
                let uu____12145 =
                  let uu____12146 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____12146  in
                FStar_Parser_AST.mk_term uu____12145 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____12148 =
                  let uu____12149 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____12149  in
                FStar_Parser_AST.mk_term uu____12148 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____12151) ->
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  a.FStar_Ident.idRange FStar_Parser_AST.Type_level
            | FStar_Parser_AST.TVariable a ->
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  a.FStar_Ident.idRange FStar_Parser_AST.Type_level
            | FStar_Parser_AST.NoName t -> t  in
          let tot =
            FStar_Parser_AST.mk_term
              (FStar_Parser_AST.Name FStar_Parser_Const.effect_Tot_lid) rng
              FStar_Parser_AST.Expr
             in
          let with_constructor_effect t =
            FStar_Parser_AST.mk_term
              (FStar_Parser_AST.App (tot, t, FStar_Parser_AST.Nothing))
              t.FStar_Parser_AST.range t.FStar_Parser_AST.level
             in
          let apply_binders t binders =
            let imp_of_aqual b =
              match b.FStar_Parser_AST.aqual with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
                  FStar_Parser_AST.Hash
              | uu____12174 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____12180 =
                     let uu____12181 =
                       let uu____12188 = binder_to_term b  in
                       (out, uu____12188, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____12181  in
                   FStar_Parser_AST.mk_term uu____12180
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___99_12198 =
            match uu___99_12198 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____12253  ->
                       match uu____12253 with
                       | (x,t,uu____12264) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated
                                ((FStar_Syntax_Util.mangle_field_name x), t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____12270 =
                    let uu____12271 =
                      let uu____12272 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____12272  in
                    FStar_Parser_AST.mk_term uu____12271
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____12270 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let uu____12276 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____12303  ->
                          match uu____12303 with
                          | (x,uu____12313,uu____12314) ->
                              FStar_Syntax_Util.unmangle_field_name x))
                   in
                ((FStar_Parser_AST.TyconVariant
                    (id1, parms, kopt,
                      [(constrName, (FStar_Pervasives_Native.Some constrTyp),
                         FStar_Pervasives_Native.None, false)])),
                  uu____12276)
            | uu____12367 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___100_12398 =
            match uu___100_12398 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____12422 = typars_of_binders _env binders  in
                (match uu____12422 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____12468 =
                         let uu____12469 =
                           let uu____12470 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____12470  in
                         FStar_Parser_AST.mk_term uu____12469
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____12468 binders  in
                     let qlid = FStar_Syntax_DsEnv.qualify _env id1  in
                     let typars1 = FStar_Syntax_Subst.close_binders typars
                        in
                     let k1 = FStar_Syntax_Subst.close typars1 k  in
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
                       }  in
                     let _env1 =
                       FStar_Syntax_DsEnv.push_top_level_rec_binding _env id1
                         FStar_Syntax_Syntax.Delta_constant
                        in
                     let _env2 =
                       FStar_Syntax_DsEnv.push_top_level_rec_binding _env'
                         id1 FStar_Syntax_Syntax.Delta_constant
                        in
                     (_env1, _env2, se, tconstr))
            | uu____12483 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____12527 =
              FStar_List.fold_left
                (fun uu____12567  ->
                   fun uu____12568  ->
                     match (uu____12567, uu____12568) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____12659 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____12659 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____12527 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____12772 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____12772
                | uu____12773 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____12781 = desugar_abstract_tc quals env [] tc  in
              (match uu____12781 with
               | (uu____12794,uu____12795,se,uu____12797) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____12800,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____12817 =
                                 let uu____12818 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____12818  in
                               if uu____12817
                               then
                                 let uu____12819 =
                                   let uu____12824 =
                                     let uu____12825 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____12825
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____12824)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____12819
                               else ());
                              FStar_Syntax_Syntax.Assumption
                              ::
                              FStar_Syntax_Syntax.New
                              ::
                              quals1)
                            in
                         let t =
                           match typars with
                           | [] -> k
                           | uu____12832 ->
                               let uu____12833 =
                                 let uu____12836 =
                                   let uu____12837 =
                                     let uu____12850 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____12850)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____12837
                                    in
                                 FStar_Syntax_Syntax.mk uu____12836  in
                               uu____12833 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___132_12854 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___132_12854.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___132_12854.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___132_12854.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____12857 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____12860 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____12860
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____12875 = typars_of_binders env binders  in
              (match uu____12875 with
               | (env',typars) ->
                   let k =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____12911 =
                           FStar_Util.for_some
                             (fun uu___101_12913  ->
                                match uu___101_12913 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____12914 -> false) quals
                            in
                         if uu____12911
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Util.ktype
                     | FStar_Pervasives_Native.Some k -> desugar_term env' k
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____12921 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___102_12925  ->
                               match uu___102_12925 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____12926 -> false))
                        in
                     if uu____12921
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____12935 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____12935
                     then
                       let uu____12938 =
                         let uu____12945 =
                           let uu____12946 = unparen t  in
                           uu____12946.FStar_Parser_AST.tm  in
                         match uu____12945 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____12967 =
                               match FStar_List.rev args with
                               | (last_arg,uu____12997)::args_rev ->
                                   let uu____13009 =
                                     let uu____13010 = unparen last_arg  in
                                     uu____13010.FStar_Parser_AST.tm  in
                                   (match uu____13009 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____13038 -> ([], args))
                               | uu____13047 -> ([], args)  in
                             (match uu____12967 with
                              | (cattributes,args1) ->
                                  let uu____13086 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____13086))
                         | uu____13097 -> (t, [])  in
                       match uu____12938 with
                       | (t1,cattributes) ->
                           let c =
                             desugar_comp t1.FStar_Parser_AST.range env' t1
                              in
                           let typars1 =
                             FStar_Syntax_Subst.close_binders typars  in
                           let c1 = FStar_Syntax_Subst.close_comp typars1 c
                              in
                           let quals2 =
                             FStar_All.pipe_right quals1
                               (FStar_List.filter
                                  (fun uu___103_13119  ->
                                     match uu___103_13119 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____13120 -> true))
                              in
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
                             FStar_Syntax_Syntax.sigattrs = []
                           }
                     else
                       (let t1 = desugar_typ env' t  in
                        mk_typ_abbrev qlid [] typars k t1 [qlid] quals1 rng)
                      in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in
                   let env2 =
                     FStar_Syntax_DsEnv.push_doc env1 qlid
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se]))
          | (FStar_Parser_AST.TyconRecord uu____13131)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____13155 = tycon_record_as_variant trec  in
              (match uu____13155 with
               | (t,fs) ->
                   let uu____13172 =
                     let uu____13175 =
                       let uu____13176 =
                         let uu____13185 =
                           let uu____13188 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____13188  in
                         (uu____13185, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____13176  in
                     uu____13175 :: quals  in
                   desugar_tycon env d uu____13172 [t])
          | uu____13193::uu____13194 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____13355 = et  in
                match uu____13355 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____13580 ->
                         let trec = tc  in
                         let uu____13604 = tycon_record_as_variant trec  in
                         (match uu____13604 with
                          | (t,fs) ->
                              let uu____13663 =
                                let uu____13666 =
                                  let uu____13667 =
                                    let uu____13676 =
                                      let uu____13679 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____13679  in
                                    (uu____13676, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____13667
                                   in
                                uu____13666 :: quals1  in
                              collect_tcs uu____13663 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____13766 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____13766 with
                          | (env2,uu____13826,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____13975 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____13975 with
                          | (env2,uu____14035,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____14160 ->
                         failwith "Unrecognized mutual type definition")
                 in
              let uu____14207 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____14207 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___105_14718  ->
                             match uu___105_14718 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____14785,uu____14786);
                                    FStar_Syntax_Syntax.sigrng = uu____14787;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____14788;
                                    FStar_Syntax_Syntax.sigmeta = uu____14789;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____14790;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____14851 =
                                     typars_of_binders env1 binders  in
                                   match uu____14851 with
                                   | (env2,tpars1) ->
                                       let uu____14882 =
                                         push_tparams env2 tpars1  in
                                       (match uu____14882 with
                                        | (env_tps,tpars2) ->
                                            let t1 = desugar_typ env_tps t
                                               in
                                            let tpars3 =
                                              FStar_Syntax_Subst.close_binders
                                                tpars2
                                               in
                                            FStar_Syntax_Subst.close tpars3
                                              t1)
                                    in
                                 let uu____14915 =
                                   let uu____14936 =
                                     mk_typ_abbrev id1 uvs tpars k t1 
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____14936)
                                    in
                                 [uu____14915]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____15004);
                                    FStar_Syntax_Syntax.sigrng = uu____15005;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____15007;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____15008;_},constrs,tconstr,quals1)
                                 ->
                                 let mk_tot t =
                                   let tot1 =
                                     FStar_Parser_AST.mk_term
                                       (FStar_Parser_AST.Name
                                          FStar_Parser_Const.effect_Tot_lid)
                                       t.FStar_Parser_AST.range
                                       t.FStar_Parser_AST.level
                                      in
                                   FStar_Parser_AST.mk_term
                                     (FStar_Parser_AST.App
                                        (tot1, t, FStar_Parser_AST.Nothing))
                                     t.FStar_Parser_AST.range
                                     t.FStar_Parser_AST.level
                                    in
                                 let tycon = (tname, tpars, k)  in
                                 let uu____15104 = push_tparams env1 tpars
                                    in
                                 (match uu____15104 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____15181  ->
                                             match uu____15181 with
                                             | (x,uu____15195) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____15203 =
                                        let uu____15232 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____15346  ->
                                                  match uu____15346 with
                                                  | (id1,topt,doc1,of_notation)
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
                                                               t -> t)
                                                         in
                                                      let t1 =
                                                        let uu____15402 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____15402
                                                         in
                                                      let name =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env1 id1
                                                         in
                                                      let quals2 =
                                                        FStar_All.pipe_right
                                                          tname_quals
                                                          (FStar_List.collect
                                                             (fun
                                                                uu___104_15413
                                                                 ->
                                                                match uu___104_15413
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____15425
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____15433 =
                                                        let uu____15454 =
                                                          let uu____15455 =
                                                            let uu____15456 =
                                                              let uu____15471
                                                                =
                                                                let uu____15474
                                                                  =
                                                                  let uu____15477
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____15477
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____15474
                                                                 in
                                                              (name, univs1,
                                                                uu____15471,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____15456
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____15455;
                                                            FStar_Syntax_Syntax.sigrng
                                                              = rng;
                                                            FStar_Syntax_Syntax.sigquals
                                                              = quals2;
                                                            FStar_Syntax_Syntax.sigmeta
                                                              =
                                                              FStar_Syntax_Syntax.default_sigmeta;
                                                            FStar_Syntax_Syntax.sigattrs
                                                              = []
                                                          }  in
                                                        ((name, doc1), tps,
                                                          uu____15454)
                                                         in
                                                      (name, uu____15433)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____15232
                                         in
                                      (match uu____15203 with
                                       | (constrNames,constrs1) ->
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
                             | uu____15716 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____15848  ->
                             match uu____15848 with
                             | (name_doc,uu____15876,uu____15877) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____15957  ->
                             match uu____15957 with
                             | (uu____15978,uu____15979,se) -> se))
                      in
                   let uu____16009 =
                     let uu____16016 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____16016 rng
                      in
                   (match uu____16009 with
                    | (bundle,abbrevs) ->
                        let env2 = FStar_Syntax_DsEnv.push_sigelt env0 bundle
                           in
                        let env3 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env2 abbrevs
                           in
                        let data_ops =
                          FStar_All.pipe_right docs_tps_sigelts
                            (FStar_List.collect
                               (fun uu____16082  ->
                                  match uu____16082 with
                                  | (uu____16105,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____16156,tps,k,uu____16159,constrs)
                                      when
                                      (FStar_List.length constrs) >
                                        (Prims.parse_int "1")
                                      ->
                                      let quals1 =
                                        se.FStar_Syntax_Syntax.sigquals  in
                                      let quals2 =
                                        if
                                          FStar_List.contains
                                            FStar_Syntax_Syntax.Abstract
                                            quals1
                                        then FStar_Syntax_Syntax.Private ::
                                          quals1
                                        else quals1  in
                                      mk_data_discriminators quals2 env3
                                        constrs
                                  | uu____16178 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____16195  ->
                                 match uu____16195 with
                                 | (lid,doc1) ->
                                     FStar_Syntax_DsEnv.push_doc env4 lid
                                       doc1) env4 name_docs
                           in
                        (env5,
                          (FStar_List.append [bundle]
                             (FStar_List.append abbrevs ops)))))
          | [] -> failwith "impossible"
  
let (desugar_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env,FStar_Syntax_Syntax.binder Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun binders  ->
      let uu____16230 =
        FStar_List.fold_left
          (fun uu____16253  ->
             fun b  ->
               match uu____16253 with
               | (env1,binders1) ->
                   let uu____16273 = desugar_binder env1 b  in
                   (match uu____16273 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____16290 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____16290 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____16307 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____16230 with
      | (env1,binders1) -> (env1, (FStar_List.rev binders1))
  
let (push_reflect_effect :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Ident.lid -> FStar_Range.range -> FStar_Syntax_DsEnv.env)
  =
  fun env  ->
    fun quals  ->
      fun effect_name  ->
        fun range  ->
          let uu____16352 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___106_16357  ->
                    match uu___106_16357 with
                    | FStar_Syntax_Syntax.Reflectable uu____16358 -> true
                    | uu____16359 -> false))
             in
          if uu____16352
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              FStar_All.pipe_right (FStar_Ident.id_of_text "reflect")
                (FStar_Syntax_DsEnv.qualify monad_env)
               in
            let quals1 =
              [FStar_Syntax_Syntax.Assumption;
              FStar_Syntax_Syntax.Reflectable effect_name]  in
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
              }  in
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
                (FStar_Syntax_DsEnv.env,FStar_Syntax_Syntax.sigelt Prims.list)
                  FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      fun quals  ->
        fun eff_name  ->
          fun eff_binders  ->
            fun eff_typ  ->
              fun eff_decls  ->
                let env0 = env  in
                let monad_env =
                  FStar_Syntax_DsEnv.enter_monad_scope env eff_name  in
                let uu____16458 = desugar_binders monad_env eff_binders  in
                match uu____16458 with
                | (env1,binders) ->
                    let eff_t = desugar_term env1 eff_typ  in
                    let for_free =
                      let uu____16479 =
                        let uu____16480 =
                          let uu____16487 =
                            FStar_Syntax_Util.arrow_formals eff_t  in
                          FStar_Pervasives_Native.fst uu____16487  in
                        FStar_List.length uu____16480  in
                      uu____16479 = (Prims.parse_int "1")  in
                    let mandatory_members =
                      let rr_members = ["repr"; "return"; "bind"]  in
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
                          "trivial"]
                       in
                    let name_of_eff_decl decl =
                      match decl.FStar_Parser_AST.d with
                      | FStar_Parser_AST.Tycon
                          (uu____16529,(FStar_Parser_AST.TyconAbbrev
                                        (name,uu____16531,uu____16532,uu____16533),uu____16534)::[])
                          -> FStar_Ident.text_of_id name
                      | uu____16567 ->
                          failwith "Malformed effect member declaration."
                       in
                    let uu____16568 =
                      FStar_List.partition
                        (fun decl  ->
                           let uu____16580 = name_of_eff_decl decl  in
                           FStar_List.mem uu____16580 mandatory_members)
                        eff_decls
                       in
                    (match uu____16568 with
                     | (mandatory_members_decls,actions) ->
                         let uu____16597 =
                           FStar_All.pipe_right mandatory_members_decls
                             (FStar_List.fold_left
                                (fun uu____16626  ->
                                   fun decl  ->
                                     match uu____16626 with
                                     | (env2,out) ->
                                         let uu____16646 =
                                           desugar_decl env2 decl  in
                                         (match uu____16646 with
                                          | (env3,ses) ->
                                              let uu____16659 =
                                                let uu____16662 =
                                                  FStar_List.hd ses  in
                                                uu____16662 :: out  in
                                              (env3, uu____16659)))
                                (env1, []))
                            in
                         (match uu____16597 with
                          | (env2,decls) ->
                              let binders1 =
                                FStar_Syntax_Subst.close_binders binders  in
                              let actions_docs =
                                FStar_All.pipe_right actions
                                  (FStar_List.map
                                     (fun d1  ->
                                        match d1.FStar_Parser_AST.d with
                                        | FStar_Parser_AST.Tycon
                                            (uu____16730,(FStar_Parser_AST.TyconAbbrev
                                                          (name,action_params,uu____16733,
                                                           {
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Construct
                                                               (uu____16734,
                                                                (def,uu____16736)::
                                                                (cps_type,uu____16738)::[]);
                                                             FStar_Parser_AST.range
                                                               = uu____16739;
                                                             FStar_Parser_AST.level
                                                               = uu____16740;_}),doc1)::[])
                                            when Prims.op_Negation for_free
                                            ->
                                            let uu____16792 =
                                              desugar_binders env2
                                                action_params
                                               in
                                            (match uu____16792 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1
                                                    in
                                                 let uu____16812 =
                                                   let uu____16813 =
                                                     FStar_Syntax_DsEnv.qualify
                                                       env3 name
                                                      in
                                                   let uu____16814 =
                                                     let uu____16815 =
                                                       desugar_term env3 def
                                                        in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____16815
                                                      in
                                                   let uu____16820 =
                                                     let uu____16821 =
                                                       desugar_typ env3
                                                         cps_type
                                                        in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____16821
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____16813;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____16814;
                                                     FStar_Syntax_Syntax.action_typ
                                                       = uu____16820
                                                   }  in
                                                 (uu____16812, doc1))
                                        | FStar_Parser_AST.Tycon
                                            (uu____16828,(FStar_Parser_AST.TyconAbbrev
                                                          (name,action_params,uu____16831,defn),doc1)::[])
                                            when for_free ->
                                            let uu____16866 =
                                              desugar_binders env2
                                                action_params
                                               in
                                            (match uu____16866 with
                                             | (env3,action_params1) ->
                                                 let action_params2 =
                                                   FStar_Syntax_Subst.close_binders
                                                     action_params1
                                                    in
                                                 let uu____16886 =
                                                   let uu____16887 =
                                                     FStar_Syntax_DsEnv.qualify
                                                       env3 name
                                                      in
                                                   let uu____16888 =
                                                     let uu____16889 =
                                                       desugar_term env3 defn
                                                        in
                                                     FStar_Syntax_Subst.close
                                                       (FStar_List.append
                                                          binders1
                                                          action_params2)
                                                       uu____16889
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       = uu____16887;
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       = name;
                                                     FStar_Syntax_Syntax.action_univs
                                                       = [];
                                                     FStar_Syntax_Syntax.action_params
                                                       = action_params2;
                                                     FStar_Syntax_Syntax.action_defn
                                                       = uu____16888;
                                                     FStar_Syntax_Syntax.action_typ
                                                       =
                                                       FStar_Syntax_Syntax.tun
                                                   }  in
                                                 (uu____16886, doc1))
                                        | uu____16896 ->
                                            FStar_Errors.raise_error
                                              (FStar_Errors.Fatal_MalformedActionDeclaration,
                                                "Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples).")
                                              d1.FStar_Parser_AST.drange))
                                 in
                              let actions1 =
                                FStar_List.map FStar_Pervasives_Native.fst
                                  actions_docs
                                 in
                              let eff_t1 =
                                FStar_Syntax_Subst.close binders1 eff_t  in
                              let lookup1 s =
                                let l =
                                  FStar_Syntax_DsEnv.qualify env2
                                    (FStar_Ident.mk_ident
                                       (s, (d.FStar_Parser_AST.drange)))
                                   in
                                let uu____16926 =
                                  let uu____16927 =
                                    FStar_Syntax_DsEnv.fail_or env2
                                      (FStar_Syntax_DsEnv.try_lookup_definition
                                         env2) l
                                     in
                                  FStar_All.pipe_left
                                    (FStar_Syntax_Subst.close binders1)
                                    uu____16927
                                   in
                                ([], uu____16926)  in
                              let mname =
                                FStar_Syntax_DsEnv.qualify env0 eff_name  in
                              let qualifiers =
                                FStar_List.map
                                  (trans_qual d.FStar_Parser_AST.drange
                                     (FStar_Pervasives_Native.Some mname))
                                  quals
                                 in
                              let se =
                                if for_free
                                then
                                  let dummy_tscheme =
                                    let uu____16944 =
                                      FStar_Syntax_Syntax.mk
                                        FStar_Syntax_Syntax.Tm_unknown
                                        FStar_Pervasives_Native.None
                                        FStar_Range.dummyRange
                                       in
                                    ([], uu____16944)  in
                                  let uu____16951 =
                                    let uu____16952 =
                                      let uu____16953 =
                                        let uu____16954 = lookup1 "repr"  in
                                        FStar_Pervasives_Native.snd
                                          uu____16954
                                         in
                                      let uu____16963 = lookup1 "return"  in
                                      let uu____16964 = lookup1 "bind"  in
                                      {
                                        FStar_Syntax_Syntax.cattributes = [];
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
                                          uu____16953;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____16963;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____16964;
                                        FStar_Syntax_Syntax.actions =
                                          actions1
                                      }  in
                                    FStar_Syntax_Syntax.Sig_new_effect_for_free
                                      uu____16952
                                     in
                                  {
                                    FStar_Syntax_Syntax.sigel = uu____16951;
                                    FStar_Syntax_Syntax.sigrng =
                                      (d.FStar_Parser_AST.drange);
                                    FStar_Syntax_Syntax.sigquals = qualifiers;
                                    FStar_Syntax_Syntax.sigmeta =
                                      FStar_Syntax_Syntax.default_sigmeta;
                                    FStar_Syntax_Syntax.sigattrs = []
                                  }
                                else
                                  (let rr =
                                     FStar_Util.for_some
                                       (fun uu___107_16968  ->
                                          match uu___107_16968 with
                                          | FStar_Syntax_Syntax.Reifiable  ->
                                              true
                                          | FStar_Syntax_Syntax.Reflectable
                                              uu____16969 -> true
                                          | uu____16970 -> false) qualifiers
                                      in
                                   let un_ts = ([], FStar_Syntax_Syntax.tun)
                                      in
                                   let uu____16980 =
                                     let uu____16981 =
                                       let uu____16982 = lookup1 "return_wp"
                                          in
                                       let uu____16983 = lookup1 "bind_wp"
                                          in
                                       let uu____16984 =
                                         lookup1 "if_then_else"  in
                                       let uu____16985 = lookup1 "ite_wp"  in
                                       let uu____16986 = lookup1 "stronger"
                                          in
                                       let uu____16987 = lookup1 "close_wp"
                                          in
                                       let uu____16988 = lookup1 "assert_p"
                                          in
                                       let uu____16989 = lookup1 "assume_p"
                                          in
                                       let uu____16990 = lookup1 "null_wp"
                                          in
                                       let uu____16991 = lookup1 "trivial"
                                          in
                                       let uu____16992 =
                                         if rr
                                         then
                                           let uu____16993 = lookup1 "repr"
                                              in
                                           FStar_All.pipe_left
                                             FStar_Pervasives_Native.snd
                                             uu____16993
                                         else FStar_Syntax_Syntax.tun  in
                                       let uu____17009 =
                                         if rr
                                         then lookup1 "return"
                                         else un_ts  in
                                       let uu____17011 =
                                         if rr then lookup1 "bind" else un_ts
                                          in
                                       {
                                         FStar_Syntax_Syntax.cattributes = [];
                                         FStar_Syntax_Syntax.mname = mname;
                                         FStar_Syntax_Syntax.univs = [];
                                         FStar_Syntax_Syntax.binders =
                                           binders1;
                                         FStar_Syntax_Syntax.signature =
                                           eff_t1;
                                         FStar_Syntax_Syntax.ret_wp =
                                           uu____16982;
                                         FStar_Syntax_Syntax.bind_wp =
                                           uu____16983;
                                         FStar_Syntax_Syntax.if_then_else =
                                           uu____16984;
                                         FStar_Syntax_Syntax.ite_wp =
                                           uu____16985;
                                         FStar_Syntax_Syntax.stronger =
                                           uu____16986;
                                         FStar_Syntax_Syntax.close_wp =
                                           uu____16987;
                                         FStar_Syntax_Syntax.assert_p =
                                           uu____16988;
                                         FStar_Syntax_Syntax.assume_p =
                                           uu____16989;
                                         FStar_Syntax_Syntax.null_wp =
                                           uu____16990;
                                         FStar_Syntax_Syntax.trivial =
                                           uu____16991;
                                         FStar_Syntax_Syntax.repr =
                                           uu____16992;
                                         FStar_Syntax_Syntax.return_repr =
                                           uu____17009;
                                         FStar_Syntax_Syntax.bind_repr =
                                           uu____17011;
                                         FStar_Syntax_Syntax.actions =
                                           actions1
                                       }  in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____16981
                                      in
                                   {
                                     FStar_Syntax_Syntax.sigel = uu____16980;
                                     FStar_Syntax_Syntax.sigrng =
                                       (d.FStar_Parser_AST.drange);
                                     FStar_Syntax_Syntax.sigquals =
                                       qualifiers;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   })
                                 in
                              let env3 =
                                FStar_Syntax_DsEnv.push_sigelt env0 se  in
                              let env4 =
                                FStar_Syntax_DsEnv.push_doc env3 mname
                                  d.FStar_Parser_AST.doc
                                 in
                              let env5 =
                                FStar_All.pipe_right actions_docs
                                  (FStar_List.fold_left
                                     (fun env5  ->
                                        fun uu____17036  ->
                                          match uu____17036 with
                                          | (a,doc1) ->
                                              let env6 =
                                                let uu____17050 =
                                                  FStar_Syntax_Util.action_as_lb
                                                    mname a
                                                   in
                                                FStar_Syntax_DsEnv.push_sigelt
                                                  env5 uu____17050
                                                 in
                                              FStar_Syntax_DsEnv.push_doc
                                                env6
                                                a.FStar_Syntax_Syntax.action_name
                                                doc1) env4)
                                 in
                              let env6 =
                                push_reflect_effect env5 qualifiers mname
                                  d.FStar_Parser_AST.drange
                                 in
                              let env7 =
                                FStar_Syntax_DsEnv.push_doc env6 mname
                                  d.FStar_Parser_AST.doc
                                 in
                              (env7, [se])))

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
                (FStar_Syntax_DsEnv.env,FStar_Syntax_Syntax.sigelt Prims.list)
                  FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      fun trans_qual1  ->
        fun quals  ->
          fun eff_name  ->
            fun eff_binders  ->
              fun defn  ->
                let env0 = env  in
                let env1 = FStar_Syntax_DsEnv.enter_monad_scope env eff_name
                   in
                let uu____17074 = desugar_binders env1 eff_binders  in
                match uu____17074 with
                | (env2,binders) ->
                    let uu____17093 =
                      let uu____17112 = head_and_args defn  in
                      match uu____17112 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____17157 ->
                                let uu____17158 =
                                  let uu____17163 =
                                    let uu____17164 =
                                      let uu____17165 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.strcat uu____17165 " not found"
                                       in
                                    Prims.strcat "Effect " uu____17164  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____17163)
                                   in
                                FStar_Errors.raise_error uu____17158
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____17167 =
                            match FStar_List.rev args with
                            | (last_arg,uu____17197)::args_rev ->
                                let uu____17209 =
                                  let uu____17210 = unparen last_arg  in
                                  uu____17210.FStar_Parser_AST.tm  in
                                (match uu____17209 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____17238 -> ([], args))
                            | uu____17247 -> ([], args)  in
                          (match uu____17167 with
                           | (cattributes,args1) ->
                               let uu____17298 = desugar_args env2 args1  in
                               let uu____17307 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____17298, uu____17307))
                       in
                    (match uu____17093 with
                     | (ed_lid,ed,args,cattributes) ->
                         let binders1 =
                           FStar_Syntax_Subst.close_binders binders  in
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
                          (let uu____17363 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____17363 with
                           | (ed_binders,uu____17377,ed_binders_opening) ->
                               let sub1 uu____17388 =
                                 match uu____17388 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____17402 =
                                         FStar_Syntax_Subst.shift_subst
                                           (FStar_List.length us)
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____17402 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____17406 =
                                       let uu____17407 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____17407)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____17406
                                  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____17412 =
                                   let uu____17413 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____17413
                                    in
                                 let uu____17424 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____17425 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____17426 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____17427 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____17428 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____17429 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____17430 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____17431 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____17432 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____17433 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____17434 =
                                   let uu____17435 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____17435
                                    in
                                 let uu____17446 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____17447 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____17448 =
                                   FStar_List.map
                                     (fun action  ->
                                        let uu____17456 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____17457 =
                                          let uu____17458 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____17458
                                           in
                                        let uu____17469 =
                                          let uu____17470 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____17470
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____17456;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____17457;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____17469
                                        }) ed.FStar_Syntax_Syntax.actions
                                    in
                                 {
                                   FStar_Syntax_Syntax.cattributes =
                                     cattributes;
                                   FStar_Syntax_Syntax.mname = mname;
                                   FStar_Syntax_Syntax.univs =
                                     (ed.FStar_Syntax_Syntax.univs);
                                   FStar_Syntax_Syntax.binders = binders1;
                                   FStar_Syntax_Syntax.signature =
                                     uu____17412;
                                   FStar_Syntax_Syntax.ret_wp = uu____17424;
                                   FStar_Syntax_Syntax.bind_wp = uu____17425;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____17426;
                                   FStar_Syntax_Syntax.ite_wp = uu____17427;
                                   FStar_Syntax_Syntax.stronger = uu____17428;
                                   FStar_Syntax_Syntax.close_wp = uu____17429;
                                   FStar_Syntax_Syntax.assert_p = uu____17430;
                                   FStar_Syntax_Syntax.assume_p = uu____17431;
                                   FStar_Syntax_Syntax.null_wp = uu____17432;
                                   FStar_Syntax_Syntax.trivial = uu____17433;
                                   FStar_Syntax_Syntax.repr = uu____17434;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____17446;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____17447;
                                   FStar_Syntax_Syntax.actions = uu____17448
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____17483 =
                                     let uu____17484 =
                                       let uu____17491 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____17491
                                        in
                                     FStar_List.length uu____17484  in
                                   uu____17483 = (Prims.parse_int "1")  in
                                 let uu____17520 =
                                   let uu____17523 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____17523 quals  in
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
                                   FStar_Syntax_Syntax.sigquals = uu____17520;
                                   FStar_Syntax_Syntax.sigmeta =
                                     FStar_Syntax_Syntax.default_sigmeta;
                                   FStar_Syntax_Syntax.sigattrs = []
                                 }  in
                               let monad_env = env2  in
                               let env3 =
                                 FStar_Syntax_DsEnv.push_sigelt env0 se  in
                               let env4 =
                                 FStar_Syntax_DsEnv.push_doc env3 ed_lid
                                   d.FStar_Parser_AST.doc
                                  in
                               let env5 =
                                 FStar_All.pipe_right
                                   ed1.FStar_Syntax_Syntax.actions
                                   (FStar_List.fold_left
                                      (fun env5  ->
                                         fun a  ->
                                           let doc1 =
                                             FStar_Syntax_DsEnv.try_lookup_doc
                                               env5
                                               a.FStar_Syntax_Syntax.action_name
                                              in
                                           let env6 =
                                             let uu____17543 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____17543
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____17545 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____17545
                                 then
                                   let reflect_lid =
                                     FStar_All.pipe_right
                                       (FStar_Ident.id_of_text "reflect")
                                       (FStar_Syntax_DsEnv.qualify monad_env)
                                      in
                                   let quals1 =
                                     [FStar_Syntax_Syntax.Assumption;
                                     FStar_Syntax_Syntax.Reflectable mname]
                                      in
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
                                     }  in
                                   FStar_Syntax_DsEnv.push_sigelt env5
                                     refl_decl
                                 else env5  in
                               let env7 =
                                 FStar_Syntax_DsEnv.push_doc env6 mname
                                   d.FStar_Parser_AST.doc
                                  in
                               (env7, [se]))))

and (mk_comment_attr :
  FStar_Parser_AST.decl ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun d  ->
    let uu____17560 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____17560 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.strcat "  " (Prims.strcat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____17611 ->
              let uu____17612 =
                let uu____17613 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____17613
                 in
              Prims.strcat "\n  " uu____17612
          | uu____17614 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____17627  ->
               match uu____17627 with
               | (k,v1) ->
                   if (k <> "summary") && (k <> "type")
                   then
                     FStar_Pervasives_Native.Some
                       (Prims.strcat k (Prims.strcat ": " v1))
                   else FStar_Pervasives_Native.None) kv
           in
        let other1 =
          if other <> []
          then Prims.strcat (FStar_String.concat "\n" other) "\n"
          else ""  in
        let str =
          Prims.strcat summary (Prims.strcat pp (Prims.strcat other1 text))
           in
        let fv =
          let uu____17645 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____17645
            FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____17647 =
          let uu____17656 = FStar_Syntax_Syntax.as_arg arg  in [uu____17656]
           in
        FStar_Syntax_Util.mk_app fv uu____17647

and (desugar_decl :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      let uu____17663 = desugar_decl_noattrs env d  in
      match uu____17663 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____17683 = mk_comment_attr d  in uu____17683 :: attrs1  in
          let s =
            FStar_List.fold_left
              (fun s  ->
                 fun a  ->
                   let uu____17694 =
                     let uu____17695 = FStar_Syntax_Print.term_to_string a
                        in
                     Prims.strcat "; " uu____17695  in
                   Prims.strcat s uu____17694) "" attrs2
             in
          let uu____17696 =
            FStar_List.map
              (fun sigelt  ->
                 let uu___133_17702 = sigelt  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___133_17702.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___133_17702.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___133_17702.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___133_17702.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs = attrs2
                 }) sigelts
             in
          (env1, uu____17696)

and (desugar_decl_noattrs :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      let trans_qual1 = trans_qual d.FStar_Parser_AST.drange  in
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
            }  in
          (if p = FStar_Parser_AST.LightOff
           then FStar_Options.set_ml_ish ()
           else ();
           (env, [se]))
      | FStar_Parser_AST.Fsdoc uu____17728 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____17744 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____17744, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals  in
          let tcs1 =
            FStar_List.map
              (fun uu____17783  ->
                 match uu____17783 with | (x,uu____17791) -> x) tcs
             in
          let uu____17796 =
            FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals
             in
          desugar_tycon env d uu____17796 tcs1
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals  in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____17818;
                    FStar_Parser_AST.prange = uu____17819;_},uu____17820)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____17829;
                    FStar_Parser_AST.prange = uu____17830;_},uu____17831)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____17846;
                         FStar_Parser_AST.prange = uu____17847;_},uu____17848);
                    FStar_Parser_AST.prange = uu____17849;_},uu____17850)::[]
                   -> false
               | (p,uu____17866)::[] ->
                   let uu____17875 = is_app_pattern p  in
                   Prims.op_Negation uu____17875
               | uu____17876 -> false)
             in
          if Prims.op_Negation expand_toplevel_pattern
          then
            let lets1 =
              FStar_List.map (fun x  -> (FStar_Pervasives_Native.None, x))
                lets
               in
            let as_inner_let =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Let
                   (isrec, lets1,
                     (FStar_Parser_AST.mk_term
                        (FStar_Parser_AST.Const FStar_Const.Const_unit)
                        d.FStar_Parser_AST.drange FStar_Parser_AST.Expr)))
                d.FStar_Parser_AST.drange FStar_Parser_AST.Expr
               in
            let ds_lets = desugar_term_maybe_top true env as_inner_let  in
            let uu____17950 =
              let uu____17951 =
                FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets  in
              uu____17951.FStar_Syntax_Syntax.n  in
            (match uu____17950 with
             | FStar_Syntax_Syntax.Tm_let (lbs,uu____17959) ->
                 let fvs =
                   FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                     (FStar_List.map
                        (fun lb  ->
                           FStar_Util.right lb.FStar_Syntax_Syntax.lbname))
                    in
                 let quals1 =
                   match quals with
                   | uu____17992::uu____17993 ->
                       FStar_List.map
                         (trans_qual1 FStar_Pervasives_Native.None) quals
                   | uu____17996 ->
                       FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                         (FStar_List.collect
                            (fun uu___108_18010  ->
                               match uu___108_18010 with
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inl uu____18013;
                                   FStar_Syntax_Syntax.lbunivs = uu____18014;
                                   FStar_Syntax_Syntax.lbtyp = uu____18015;
                                   FStar_Syntax_Syntax.lbeff = uu____18016;
                                   FStar_Syntax_Syntax.lbdef = uu____18017;
                                   FStar_Syntax_Syntax.lbattrs = uu____18018;_}
                                   -> []
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inr fv;
                                   FStar_Syntax_Syntax.lbunivs = uu____18030;
                                   FStar_Syntax_Syntax.lbtyp = uu____18031;
                                   FStar_Syntax_Syntax.lbeff = uu____18032;
                                   FStar_Syntax_Syntax.lbdef = uu____18033;
                                   FStar_Syntax_Syntax.lbattrs = uu____18034;_}
                                   ->
                                   FStar_Syntax_DsEnv.lookup_letbinding_quals
                                     env
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                    in
                 let quals2 =
                   let uu____18048 =
                     FStar_All.pipe_right lets1
                       (FStar_Util.for_some
                          (fun uu____18079  ->
                             match uu____18079 with
                             | (uu____18092,(uu____18093,t)) ->
                                 t.FStar_Parser_AST.level =
                                   FStar_Parser_AST.Formula))
                      in
                   if uu____18048
                   then FStar_Syntax_Syntax.Logic :: quals1
                   else quals1  in
                 let lbs1 =
                   let uu____18117 =
                     FStar_All.pipe_right quals2
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                      in
                   if uu____18117
                   then
                     let uu____18126 =
                       FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                         (FStar_List.map
                            (fun lb  ->
                               let fv =
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               let uu___134_18140 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (FStar_Util.Inr
                                      (let uu___135_18142 = fv  in
                                       {
                                         FStar_Syntax_Syntax.fv_name =
                                           (uu___135_18142.FStar_Syntax_Syntax.fv_name);
                                         FStar_Syntax_Syntax.fv_delta =
                                           (FStar_Syntax_Syntax.Delta_abstract
                                              (fv.FStar_Syntax_Syntax.fv_delta));
                                         FStar_Syntax_Syntax.fv_qual =
                                           (uu___135_18142.FStar_Syntax_Syntax.fv_qual)
                                       }));
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___134_18140.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___134_18140.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___134_18140.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef =
                                   (uu___134_18140.FStar_Syntax_Syntax.lbdef);
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___134_18140.FStar_Syntax_Syntax.lbattrs)
                               }))
                        in
                     ((FStar_Pervasives_Native.fst lbs), uu____18126)
                   else lbs  in
                 let names1 =
                   FStar_All.pipe_right fvs
                     (FStar_List.map
                        (fun fv  ->
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                    in
                 let attrs =
                   FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs
                    in
                 let s =
                   {
                     FStar_Syntax_Syntax.sigel =
                       (FStar_Syntax_Syntax.Sig_let (lbs1, names1));
                     FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                     FStar_Syntax_Syntax.sigquals = quals2;
                     FStar_Syntax_Syntax.sigmeta =
                       FStar_Syntax_Syntax.default_sigmeta;
                     FStar_Syntax_Syntax.sigattrs = attrs
                   }  in
                 let env1 = FStar_Syntax_DsEnv.push_sigelt env s  in
                 let env2 =
                   FStar_List.fold_left
                     (fun env2  ->
                        fun id1  ->
                          FStar_Syntax_DsEnv.push_doc env2 id1
                            d.FStar_Parser_AST.doc) env1 names1
                    in
                 (env2, [s])
             | uu____18177 ->
                 failwith "Desugaring a let did not produce a let")
          else
            (let uu____18183 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____18202 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____18183 with
             | (pat,body) ->
                 let fresh_toplevel_name =
                   FStar_Ident.gen FStar_Range.dummyRange  in
                 let fresh_pat =
                   let var_pat =
                     FStar_Parser_AST.mk_pattern
                       (FStar_Parser_AST.PatVar
                          (fresh_toplevel_name, FStar_Pervasives_Native.None))
                       FStar_Range.dummyRange
                      in
                   match pat.FStar_Parser_AST.pat with
                   | FStar_Parser_AST.PatAscribed (pat1,ty) ->
                       let uu___136_18226 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___136_18226.FStar_Parser_AST.prange)
                       }
                   | uu____18227 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___137_18234 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___137_18234.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___137_18234.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___137_18234.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____18266 id1 =
                   match uu____18266 with
                   | (env1,ses) ->
                       let main =
                         let uu____18287 =
                           let uu____18288 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____18288  in
                         FStar_Parser_AST.mk_term uu____18287
                           FStar_Range.dummyRange FStar_Parser_AST.Expr
                          in
                       let lid = FStar_Ident.lid_of_ids [id1]  in
                       let projectee =
                         FStar_Parser_AST.mk_term (FStar_Parser_AST.Var lid)
                           FStar_Range.dummyRange FStar_Parser_AST.Expr
                          in
                       let body1 =
                         FStar_Parser_AST.mk_term
                           (FStar_Parser_AST.Match
                              (main,
                                [(pat, FStar_Pervasives_Native.None,
                                   projectee)])) FStar_Range.dummyRange
                           FStar_Parser_AST.Expr
                          in
                       let bv_pat =
                         FStar_Parser_AST.mk_pattern
                           (FStar_Parser_AST.PatVar
                              (id1, FStar_Pervasives_Native.None))
                           FStar_Range.dummyRange
                          in
                       let id_decl =
                         FStar_Parser_AST.mk_decl
                           (FStar_Parser_AST.TopLevelLet
                              (FStar_Parser_AST.NoLetQualifier,
                                [(bv_pat, body1)])) FStar_Range.dummyRange []
                          in
                       let uu____18338 = desugar_decl env1 id_decl  in
                       (match uu____18338 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____18356 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____18356 FStar_Util.set_elements
                    in
                 FStar_List.fold_left build_projection main_let bvs)
      | FStar_Parser_AST.Main t ->
          let e = desugar_term env t  in
          let se =
            {
              FStar_Syntax_Syntax.sigel = (FStar_Syntax_Syntax.Sig_main e);
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = [];
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          (env, [se])
      | FStar_Parser_AST.Assume (id1,t) ->
          let f = desugar_formula env t  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let env1 =
            FStar_Syntax_DsEnv.push_doc env lid d.FStar_Parser_AST.doc  in
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
      | FStar_Parser_AST.Val (id1,t) ->
          let quals = d.FStar_Parser_AST.quals  in
          let t1 =
            let uu____18387 = close_fun env t  in
            desugar_term env uu____18387  in
          let quals1 =
            let uu____18391 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____18391
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let se =
            let uu____18397 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____18397;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in
          let env2 =
            FStar_Syntax_DsEnv.push_doc env1 lid d.FStar_Parser_AST.doc  in
          (env2, [se])
      | FStar_Parser_AST.Exception (id1,FStar_Pervasives_Native.None ) ->
          let uu____18409 =
            FStar_Syntax_DsEnv.fail_or env
              (FStar_Syntax_DsEnv.try_lookup_lid env)
              FStar_Parser_Const.exn_lid
             in
          (match uu____18409 with
           | (t,uu____18423) ->
               let l = FStar_Syntax_DsEnv.qualify env id1  in
               let qual = [FStar_Syntax_Syntax.ExceptionConstructor]  in
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
                 }  in
               let se' =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_bundle ([se], [l]));
                   FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                   FStar_Syntax_Syntax.sigquals = qual;
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 }  in
               let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
               let env2 =
                 FStar_Syntax_DsEnv.push_doc env1 l d.FStar_Parser_AST.doc
                  in
               let data_ops = mk_data_projector_names [] env2 se  in
               let discs = mk_data_discriminators [] env2 [l]  in
               let env3 =
                 FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt env2
                   (FStar_List.append discs data_ops)
                  in
               (env3, (FStar_List.append (se' :: discs) data_ops)))
      | FStar_Parser_AST.Exception (id1,FStar_Pervasives_Native.Some term) ->
          let t = desugar_term env term  in
          let t1 =
            let uu____18457 =
              let uu____18464 = FStar_Syntax_Syntax.null_binder t  in
              [uu____18464]  in
            let uu____18465 =
              let uu____18468 =
                let uu____18469 =
                  FStar_Syntax_DsEnv.fail_or env
                    (FStar_Syntax_DsEnv.try_lookup_lid env)
                    FStar_Parser_Const.exn_lid
                   in
                FStar_Pervasives_Native.fst uu____18469  in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____18468
               in
            FStar_Syntax_Util.arrow uu____18457 uu____18465  in
          let l = FStar_Syntax_DsEnv.qualify env id1  in
          let qual = [FStar_Syntax_Syntax.ExceptionConstructor]  in
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
            }  in
          let se' =
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_bundle ([se], [l]));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = qual;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
          let env2 =
            FStar_Syntax_DsEnv.push_doc env1 l d.FStar_Parser_AST.doc  in
          let data_ops = mk_data_projector_names [] env2 se  in
          let discs = mk_data_discriminators [] env2 [l]  in
          let env3 =
            FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt env2
              (FStar_List.append discs data_ops)
             in
          (env3, (FStar_List.append (se' :: discs) data_ops))
      | FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect
          (eff_name,eff_binders,defn)) ->
          let quals = d.FStar_Parser_AST.quals  in
          desugar_redefine_effect env d trans_qual1 quals eff_name
            eff_binders defn
      | FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect
          (eff_name,eff_binders,eff_typ,eff_decls)) ->
          let quals = d.FStar_Parser_AST.quals  in
          desugar_effect env d quals eff_name eff_binders eff_typ eff_decls
      | FStar_Parser_AST.SubEffect l ->
          let lookup1 l1 =
            let uu____18531 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____18531 with
            | FStar_Pervasives_Native.None  ->
                let uu____18534 =
                  let uu____18539 =
                    let uu____18540 =
                      let uu____18541 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.strcat uu____18541 " not found"  in
                    Prims.strcat "Effect name " uu____18540  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____18539)  in
                FStar_Errors.raise_error uu____18534
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____18545 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____18587 =
                  let uu____18596 =
                    let uu____18603 = desugar_term env t  in
                    ([], uu____18603)  in
                  FStar_Pervasives_Native.Some uu____18596  in
                (uu____18587, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____18636 =
                  let uu____18645 =
                    let uu____18652 = desugar_term env wp  in
                    ([], uu____18652)  in
                  FStar_Pervasives_Native.Some uu____18645  in
                let uu____18661 =
                  let uu____18670 =
                    let uu____18677 = desugar_term env t  in
                    ([], uu____18677)  in
                  FStar_Pervasives_Native.Some uu____18670  in
                (uu____18636, uu____18661)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____18703 =
                  let uu____18712 =
                    let uu____18719 = desugar_term env t  in
                    ([], uu____18719)  in
                  FStar_Pervasives_Native.Some uu____18712  in
                (FStar_Pervasives_Native.None, uu____18703)
             in
          (match uu____18545 with
           | (lift_wp,lift) ->
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
                 }  in
               (env, [se]))

let (desugar_decls :
  env_t ->
    FStar_Parser_AST.decl Prims.list ->
      (env_t,FStar_Syntax_Syntax.sigelt Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun decls  ->
      let uu____18807 =
        FStar_List.fold_left
          (fun uu____18827  ->
             fun d  ->
               match uu____18827 with
               | (env1,sigelts) ->
                   let uu____18847 = desugar_decl env1 d  in
                   (match uu____18847 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____18807 with
      | (env1,sigelts) ->
          let rec forward acc uu___110_18888 =
            match uu___110_18888 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____18902,FStar_Syntax_Syntax.Sig_let uu____18903) ->
                     let uu____18916 =
                       let uu____18919 =
                         let uu___138_18920 = se2  in
                         let uu____18921 =
                           let uu____18924 =
                             FStar_List.filter
                               (fun uu___109_18938  ->
                                  match uu___109_18938 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____18942;
                                           FStar_Syntax_Syntax.vars =
                                             uu____18943;_},uu____18944);
                                      FStar_Syntax_Syntax.pos = uu____18945;
                                      FStar_Syntax_Syntax.vars = uu____18946;_}
                                      when
                                      let uu____18969 =
                                        let uu____18970 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____18970
                                         in
                                      uu____18969 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____18971 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____18924
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___138_18920.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___138_18920.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___138_18920.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___138_18920.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____18921
                         }  in
                       uu____18919 :: se1 :: acc  in
                     forward uu____18916 sigelts1
                 | uu____18976 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____18984 = forward [] sigelts  in (env1, uu____18984)
  
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
        (env_t,FStar_Syntax_Syntax.modul,Prims.bool)
          FStar_Pervasives_Native.tuple3)
  =
  fun curmod  ->
    fun env  ->
      fun m  ->
        let env1 =
          match (curmod, m) with
          | (FStar_Pervasives_Native.None ,uu____19035) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____19039;
               FStar_Syntax_Syntax.exports = uu____19040;
               FStar_Syntax_Syntax.is_interface = uu____19041;_},FStar_Parser_AST.Module
             (current_lid,uu____19043)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____19051) ->
              let uu____19054 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____19054
           in
        let uu____19059 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____19095 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____19095, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____19112 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____19112, mname, decls, false)
           in
        match uu____19059 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____19142 = desugar_decls env2 decls  in
            (match uu____19142 with
             | (env3,sigelts) ->
                 let modul =
                   {
                     FStar_Syntax_Syntax.name = mname;
                     FStar_Syntax_Syntax.declarations = sigelts;
                     FStar_Syntax_Syntax.exports = [];
                     FStar_Syntax_Syntax.is_interface = intf
                   }  in
                 (env3, modul, pop_when_done))
  
let (as_interface : FStar_Parser_AST.modul -> FStar_Parser_AST.modul) =
  fun m  ->
    match m with
    | FStar_Parser_AST.Module (mname,decls) ->
        FStar_Parser_AST.Interface (mname, decls, true)
    | i -> i
  
let (desugar_partial_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    env_t ->
      FStar_Parser_AST.modul ->
        (env_t,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2)
  =
  fun curmod  ->
    fun env  ->
      fun m  ->
        let m1 =
          let uu____19196 =
            (FStar_Options.interactive ()) &&
              (let uu____19198 =
                 let uu____19199 =
                   let uu____19200 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____19200  in
                 FStar_Util.get_file_extension uu____19199  in
               FStar_List.mem uu____19198 ["fsti"; "fsi"])
             in
          if uu____19196 then as_interface m else m  in
        let uu____19204 = desugar_modul_common curmod env m1  in
        match uu____19204 with
        | (x,y,pop_when_done) ->
            (if pop_when_done
             then (let uu____19219 = FStar_Syntax_DsEnv.pop ()  in ())
             else ();
             (x, y))
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul ->
      (env_t,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun m  ->
      let uu____19235 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____19235 with
      | (env1,modul,pop_when_done) ->
          let uu____19249 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____19249 with
           | (env2,modul1) ->
               ((let uu____19261 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____19261
                 then
                   let uu____19262 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____19262
                 else ());
                (let uu____19264 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____19264, modul1))))
  
let (ast_modul_to_modul :
  FStar_Parser_AST.modul ->
    FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun env  ->
      let uu____19278 = desugar_modul env modul  in
      match uu____19278 with | (env1,modul1) -> (modul1, env1)
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      let uu____19305 = desugar_decls env decls  in
      match uu____19305 with | (env1,sigelts) -> (sigelts, env1)
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        let uu____19343 = desugar_partial_modul modul env a_modul  in
        match uu____19343 with | (env1,modul1) -> (modul1, env1)
  
let (add_modul_to_env :
  FStar_Syntax_Syntax.modul ->
    FStar_Syntax_DsEnv.module_inclusion_info ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        Prims.unit FStar_Syntax_DsEnv.withenv)
  =
  fun m  ->
    fun mii  ->
      fun erase_univs  ->
        fun en  ->
          let erase_univs_ed ed =
            let erase_binders bs =
              match bs with
              | [] -> []
              | uu____19417 ->
                  let t =
                    let uu____19425 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____19425  in
                  let uu____19434 =
                    let uu____19435 = FStar_Syntax_Subst.compress t  in
                    uu____19435.FStar_Syntax_Syntax.n  in
                  (match uu____19434 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____19445,uu____19446)
                       -> bs1
                   | uu____19467 -> failwith "Impossible")
               in
            let uu____19474 =
              let uu____19481 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____19481
                FStar_Syntax_Syntax.t_unit
               in
            match uu____19474 with
            | (binders,uu____19483,binders_opening) ->
                let erase_term t =
                  let uu____19489 =
                    let uu____19490 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____19490  in
                  FStar_Syntax_Subst.close binders uu____19489  in
                let erase_tscheme uu____19506 =
                  match uu____19506 with
                  | (us,t) ->
                      let t1 =
                        let uu____19526 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____19526 t  in
                      let uu____19529 =
                        let uu____19530 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____19530  in
                      ([], uu____19529)
                   in
                let erase_action action =
                  let opening =
                    FStar_Syntax_Subst.shift_subst
                      (FStar_List.length
                         action.FStar_Syntax_Syntax.action_univs)
                      binders_opening
                     in
                  let erased_action_params =
                    match action.FStar_Syntax_Syntax.action_params with
                    | [] -> []
                    | uu____19559 ->
                        let bs =
                          let uu____19567 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____19567  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____19597 =
                          let uu____19598 =
                            let uu____19601 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____19601  in
                          uu____19598.FStar_Syntax_Syntax.n  in
                        (match uu____19597 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____19609,uu____19610) -> bs1
                         | uu____19631 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____19642 =
                      let uu____19643 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____19643  in
                    FStar_Syntax_Subst.close binders uu____19642  in
                  let uu___139_19644 = action  in
                  let uu____19645 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____19646 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___139_19644.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___139_19644.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____19645;
                    FStar_Syntax_Syntax.action_typ = uu____19646
                  }  in
                let uu___140_19647 = ed  in
                let uu____19648 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____19649 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____19650 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____19651 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____19652 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____19653 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____19654 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____19655 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____19656 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____19657 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____19658 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____19659 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____19660 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____19661 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____19662 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____19663 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___140_19647.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___140_19647.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____19648;
                  FStar_Syntax_Syntax.signature = uu____19649;
                  FStar_Syntax_Syntax.ret_wp = uu____19650;
                  FStar_Syntax_Syntax.bind_wp = uu____19651;
                  FStar_Syntax_Syntax.if_then_else = uu____19652;
                  FStar_Syntax_Syntax.ite_wp = uu____19653;
                  FStar_Syntax_Syntax.stronger = uu____19654;
                  FStar_Syntax_Syntax.close_wp = uu____19655;
                  FStar_Syntax_Syntax.assert_p = uu____19656;
                  FStar_Syntax_Syntax.assume_p = uu____19657;
                  FStar_Syntax_Syntax.null_wp = uu____19658;
                  FStar_Syntax_Syntax.trivial = uu____19659;
                  FStar_Syntax_Syntax.repr = uu____19660;
                  FStar_Syntax_Syntax.return_repr = uu____19661;
                  FStar_Syntax_Syntax.bind_repr = uu____19662;
                  FStar_Syntax_Syntax.actions = uu____19663
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___141_19675 = se  in
                  let uu____19676 =
                    let uu____19677 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____19677  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____19676;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___141_19675.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___141_19675.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___141_19675.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___141_19675.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___142_19681 = se  in
                  let uu____19682 =
                    let uu____19683 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____19683
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____19682;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___142_19681.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___142_19681.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___142_19681.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___142_19681.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____19685 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____19686 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____19686 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____19698 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____19698
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____19700 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____19700)
  