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
      | FStar_Parser_AST.VQuote uu____838 -> []
      | FStar_Parser_AST.Seq uu____839 -> []

let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term,(FStar_Parser_AST.term,FStar_Parser_AST.imp)
                             FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let rec aux args t1 =
      let uu____886 =
        let uu____887 = unparen t1  in uu____887.FStar_Parser_AST.tm  in
      match uu____886 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____929 -> (t1, args)  in
    aux [] t
  
let (close :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____949 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____949  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____967 =
                     let uu____968 =
                       let uu____973 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____973)  in
                     FStar_Parser_AST.TAnnotated uu____968  in
                   FStar_Parser_AST.mk_binder uu____967 x.FStar_Ident.idRange
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
        let uu____986 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____986  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1004 =
                     let uu____1005 =
                       let uu____1010 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____1010)  in
                     FStar_Parser_AST.TAnnotated uu____1005  in
                   FStar_Parser_AST.mk_binder uu____1004
                     x.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____1012 =
             let uu____1013 = unparen t  in uu____1013.FStar_Parser_AST.tm
              in
           match uu____1012 with
           | FStar_Parser_AST.Product uu____1014 -> t
           | uu____1021 ->
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
      | uu____1053 -> (bs, t)
  
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild  -> true
    | FStar_Parser_AST.PatTvar (uu____1059,uu____1060) -> true
    | FStar_Parser_AST.PatVar (uu____1065,uu____1066) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____1072) -> is_var_pattern p1
    | uu____1085 -> false
  
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____1090) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____1103;
           FStar_Parser_AST.prange = uu____1104;_},uu____1105)
        -> true
    | uu____1116 -> false
  
let (replace_unit_pattern :
  FStar_Parser_AST.pattern -> FStar_Parser_AST.pattern) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatConst (FStar_Const.Const_unit ) ->
        FStar_Parser_AST.mk_pattern
          (FStar_Parser_AST.PatAscribed
             ((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild
                 p.FStar_Parser_AST.prange),
               (unit_ty, FStar_Pervasives_Native.None)))
          p.FStar_Parser_AST.prange
    | uu____1128 -> p
  
let rec (destruct_app_pattern :
  FStar_Syntax_DsEnv.env ->
    Prims.bool ->
      FStar_Parser_AST.pattern ->
        ((FStar_Ident.ident,FStar_Ident.lident) FStar_Util.either,FStar_Parser_AST.pattern
                                                                    Prims.list,
          (FStar_Parser_AST.term,FStar_Parser_AST.term
                                   FStar_Pervasives_Native.option)
            FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun is_top_level1  ->
      fun p  ->
        match p.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatAscribed (p1,t) ->
            let uu____1192 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____1192 with
             | (name,args,uu____1235) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1285);
               FStar_Parser_AST.prange = uu____1286;_},args)
            when is_top_level1 ->
            let uu____1296 =
              let uu____1301 = FStar_Syntax_DsEnv.qualify env id1  in
              FStar_Util.Inr uu____1301  in
            (uu____1296, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1323);
               FStar_Parser_AST.prange = uu____1324;_},args)
            -> ((FStar_Util.Inl id1), args, FStar_Pervasives_Native.None)
        | uu____1354 -> failwith "Not an app pattern"
  
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
      | FStar_Parser_AST.PatConst uu____1398 -> acc
      | FStar_Parser_AST.PatVar
          (uu____1399,FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit
           ))
          -> acc
      | FStar_Parser_AST.PatName uu____1402 -> acc
      | FStar_Parser_AST.PatTvar uu____1403 -> acc
      | FStar_Parser_AST.PatOp uu____1410 -> acc
      | FStar_Parser_AST.PatApp (phead,pats) ->
          gather_pattern_bound_vars_from_list (phead :: pats)
      | FStar_Parser_AST.PatVar (x,uu____1418) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatTuple (pats,uu____1427) ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu____1442 =
            FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
          gather_pattern_bound_vars_from_list uu____1442
      | FStar_Parser_AST.PatAscribed (pat,uu____1450) ->
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
  | LetBinder of
  (FStar_Ident.lident,(FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term
                                                  FStar_Pervasives_Native.option)
                        FStar_Pervasives_Native.tuple2)
  FStar_Pervasives_Native.tuple2 [@@deriving show]
let (uu___is_LocalBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LocalBinder _0 -> true | uu____1506 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____1540 -> false
  
let (__proj__LetBinder__item___0 :
  bnd ->
    (FStar_Ident.lident,(FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term
                                                    FStar_Pervasives_Native.option)
                          FStar_Pervasives_Native.tuple2)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | LetBinder _0 -> _0 
let (binder_of_bnd :
  bnd ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2)
  =
  fun uu___86_1584  ->
    match uu___86_1584 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____1591 -> failwith "Impossible"
  
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
      fun uu___87_1616  ->
        match uu___87_1616 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____1632 = FStar_Syntax_Syntax.null_binder k  in
            (uu____1632, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____1637 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____1637 with
             | (env1,a1) ->
                 (((let uu___111_1657 = a1  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___111_1657.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___111_1657.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = k
                    }), (trans_aqual imp)), env1))
  
type env_t = FStar_Syntax_DsEnv.env[@@deriving show]
type lenv_t = FStar_Syntax_Syntax.bv Prims.list[@@deriving show]
let (mk_lb :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list,(FStar_Syntax_Syntax.bv,
                                                                    FStar_Syntax_Syntax.fv)
                                                                    FStar_Util.either,
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.term'
                                                           FStar_Syntax_Syntax.syntax,
    FStar_Range.range) FStar_Pervasives_Native.tuple5 ->
    FStar_Syntax_Syntax.letbinding)
  =
  fun uu____1684  ->
    match uu____1684 with
    | (attrs,n1,t,e,pos) ->
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
  fun bs  ->
    fun t  -> FStar_Syntax_Util.abs bs t FStar_Pervasives_Native.None
  
let (mk_ref_read :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____1752 =
        let uu____1767 =
          let uu____1768 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____1768  in
        let uu____1769 =
          let uu____1778 =
            let uu____1785 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____1785)  in
          [uu____1778]  in
        (uu____1767, uu____1769)  in
      FStar_Syntax_Syntax.Tm_app uu____1752  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____1818 =
        let uu____1833 =
          let uu____1834 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____1834  in
        let uu____1835 =
          let uu____1844 =
            let uu____1851 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____1851)  in
          [uu____1844]  in
        (uu____1833, uu____1835)  in
      FStar_Syntax_Syntax.Tm_app uu____1818  in
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
          let uu____1894 =
            let uu____1909 =
              let uu____1910 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____1910  in
            let uu____1911 =
              let uu____1920 =
                let uu____1927 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____1927)  in
              let uu____1930 =
                let uu____1939 =
                  let uu____1946 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____1946)  in
                [uu____1939]  in
              uu____1920 :: uu____1930  in
            (uu____1909, uu____1911)  in
          FStar_Syntax_Syntax.Tm_app uu____1894  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___88_1977  ->
    match uu___88_1977 with
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
    | uu____1978 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____1986 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____1986)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____2001 =
      let uu____2002 = unparen t  in uu____2002.FStar_Parser_AST.tm  in
    match uu____2001 with
    | FStar_Parser_AST.Wild  ->
        let uu____2007 =
          let uu____2008 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____2008  in
        FStar_Util.Inr uu____2007
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____2019)) ->
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
             let uu____2085 = sum_to_universe u n1  in
             FStar_Util.Inr uu____2085
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____2096 = sum_to_universe u n1  in
             FStar_Util.Inr uu____2096
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____2107 =
               let uu____2112 =
                 let uu____2113 = FStar_Parser_AST.term_to_string t  in
                 Prims.strcat
                   "This universe might contain a sum of two universe variables "
                   uu____2113
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____2112)
                in
             FStar_Errors.raise_error uu____2107 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____2118 ->
        let rec aux t1 univargs =
          let uu____2148 =
            let uu____2149 = unparen t1  in uu____2149.FStar_Parser_AST.tm
             in
          match uu____2148 with
          | FStar_Parser_AST.App (t2,targ,uu____2156) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___89_2180  ->
                     match uu___89_2180 with
                     | FStar_Util.Inr uu____2185 -> true
                     | uu____2186 -> false) univargs
              then
                let uu____2191 =
                  let uu____2192 =
                    FStar_List.map
                      (fun uu___90_2201  ->
                         match uu___90_2201 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____2192  in
                FStar_Util.Inr uu____2191
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___91_2218  ->
                        match uu___91_2218 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____2224 -> failwith "impossible")
                     univargs
                    in
                 let uu____2225 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____2225)
          | uu____2231 ->
              let uu____2232 =
                let uu____2237 =
                  let uu____2238 =
                    let uu____2239 = FStar_Parser_AST.term_to_string t1  in
                    Prims.strcat uu____2239 " in universe context"  in
                  Prims.strcat "Unexpected term " uu____2238  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____2237)  in
              FStar_Errors.raise_error uu____2232 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____2248 ->
        let uu____2249 =
          let uu____2254 =
            let uu____2255 =
              let uu____2256 = FStar_Parser_AST.term_to_string t  in
              Prims.strcat uu____2256 " in universe context"  in
            Prims.strcat "Unexpected term " uu____2255  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____2254)  in
        FStar_Errors.raise_error uu____2249 t.FStar_Parser_AST.range
  
let rec (desugar_universe :
  FStar_Parser_AST.term -> FStar_Syntax_Syntax.universe) =
  fun t  ->
    let u = desugar_maybe_non_constant_universe t  in
    match u with
    | FStar_Util.Inl n1 -> int_to_universe n1
    | FStar_Util.Inr u1 -> u1
  
let check_fields :
  'Auu____2275 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident,'Auu____2275) FStar_Pervasives_Native.tuple2
        Prims.list -> FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____2300 = FStar_List.hd fields  in
        match uu____2300 with
        | (f,uu____2310) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____2320 =
                match uu____2320 with
                | (f',uu____2326) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____2328 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____2328
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
              (let uu____2332 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____2332);
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
        let check_linear_pattern_variables pats r =
          let rec pat_vars p1 =
            match p1.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_dot_term uu____2561 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_wild uu____2568 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_constant uu____2569 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_var x ->
                FStar_Util.set_add x FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_cons (uu____2571,pats1) ->
                let aux out uu____2605 =
                  match uu____2605 with
                  | (p2,uu____2617) ->
                      let intersection =
                        let uu____2625 = pat_vars p2  in
                        FStar_Util.set_intersect uu____2625 out  in
                      let uu____2628 = FStar_Util.set_is_empty intersection
                         in
                      if uu____2628
                      then
                        let uu____2631 = pat_vars p2  in
                        FStar_Util.set_union out uu____2631
                      else
                        (let duplicate_bv =
                           let uu____2636 =
                             FStar_Util.set_elements intersection  in
                           FStar_List.hd uu____2636  in
                         let uu____2639 =
                           let uu____2644 =
                             FStar_Util.format1
                               "Non-linear patterns are not permitted. %s appears more than once in this pattern."
                               (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                              in
                           (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                             uu____2644)
                            in
                         FStar_Errors.raise_error uu____2639 r)
                   in
                FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
             in
          match pats with
          | [] -> ()
          | p1::[] ->
              let uu____2664 = pat_vars p1  in
              FStar_All.pipe_right uu____2664 FStar_Pervasives.ignore
          | p1::ps ->
              let pvars = pat_vars p1  in
              let aux p2 =
                let uu____2684 =
                  let uu____2685 = pat_vars p2  in
                  FStar_Util.set_eq pvars uu____2685  in
                if uu____2684
                then ()
                else
                  (let nonlinear_vars =
                     let uu____2692 = pat_vars p2  in
                     FStar_Util.set_symmetric_difference pvars uu____2692  in
                   let first_nonlinear_var =
                     let uu____2696 = FStar_Util.set_elements nonlinear_vars
                        in
                     FStar_List.hd uu____2696  in
                   let uu____2699 =
                     let uu____2704 =
                       FStar_Util.format1
                         "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                         (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                        in
                     (FStar_Errors.Fatal_IncoherentPatterns, uu____2704)  in
                   FStar_Errors.raise_error uu____2699 r)
                 in
              FStar_List.iter aux ps
           in
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false ,uu____2708) -> ()
         | (true ,FStar_Parser_AST.PatVar uu____2709) -> ()
         | (true ,uu____2716) ->
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_LetMutableForVariablesOnly,
                 "let-mutable is for variables only")
               p.FStar_Parser_AST.prange);
        (let push_bv_maybe_mut =
           if is_mut
           then FStar_Syntax_DsEnv.push_bv_mutable
           else FStar_Syntax_DsEnv.push_bv  in
         let resolvex l e x =
           let uu____2751 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText))
              in
           match uu____2751 with
           | FStar_Pervasives_Native.Some y -> (l, e, y)
           | uu____2765 ->
               let uu____2768 = push_bv_maybe_mut e x  in
               (match uu____2768 with | (e1,x1) -> ((x1 :: l), e1, x1))
            in
         let rec aux' top loc env1 p1 =
           let pos q =
             FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange  in
           let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
           let orig = p1  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr uu____2855 -> failwith "impossible"
           | FStar_Parser_AST.PatOp op ->
               let uu____2871 =
                 let uu____2872 =
                   let uu____2873 =
                     let uu____2880 =
                       let uu____2881 =
                         let uu____2886 =
                           FStar_Parser_AST.compile_op (Prims.parse_int "0")
                             op.FStar_Ident.idText op.FStar_Ident.idRange
                            in
                         (uu____2886, (op.FStar_Ident.idRange))  in
                       FStar_Ident.mk_ident uu____2881  in
                     (uu____2880, FStar_Pervasives_Native.None)  in
                   FStar_Parser_AST.PatVar uu____2873  in
                 {
                   FStar_Parser_AST.pat = uu____2872;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 }  in
               aux loc env1 uu____2871
           | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
               ((match tacopt with
                 | FStar_Pervasives_Native.None  -> ()
                 | FStar_Pervasives_Native.Some uu____2903 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                         "Type ascriptions within patterns are cannot be associated with a tactic")
                       orig.FStar_Parser_AST.prange);
                (let uu____2904 = aux loc env1 p2  in
                 match uu____2904 with
                 | (loc1,env',binder,p3,imp) ->
                     let annot_pat_var p4 t1 =
                       match p4.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let uu___112_2958 = p4  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var
                                  (let uu___113_2963 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___113_2963.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___113_2963.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }));
                             FStar_Syntax_Syntax.p =
                               (uu___112_2958.FStar_Syntax_Syntax.p)
                           }
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let uu___114_2965 = p4  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild
                                  (let uu___115_2970 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___115_2970.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___115_2970.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }));
                             FStar_Syntax_Syntax.p =
                               (uu___114_2965.FStar_Syntax_Syntax.p)
                           }
                       | uu____2971 when top -> p4
                       | uu____2972 ->
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                               "Type ascriptions within patterns are only allowed on variables")
                             orig.FStar_Parser_AST.prange
                        in
                     let uu____2975 =
                       match binder with
                       | LetBinder uu____2988 -> failwith "impossible"
                       | LocalBinder (x,aq) ->
                           let t1 =
                             let uu____3008 = close_fun env1 t  in
                             desugar_term env1 uu____3008  in
                           (if
                              (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                               with
                               | FStar_Syntax_Syntax.Tm_unknown  -> false
                               | uu____3010 -> true)
                            then
                              (let uu____3011 =
                                 let uu____3016 =
                                   let uu____3017 =
                                     FStar_Syntax_Print.bv_to_string x  in
                                   let uu____3018 =
                                     FStar_Syntax_Print.term_to_string
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____3019 =
                                     FStar_Syntax_Print.term_to_string t1  in
                                   FStar_Util.format3
                                     "Multiple ascriptions for %s in pattern, type %s was shadowed by %s\n"
                                     uu____3017 uu____3018 uu____3019
                                    in
                                 (FStar_Errors.Warning_MultipleAscriptions,
                                   uu____3016)
                                  in
                               FStar_Errors.log_issue
                                 orig.FStar_Parser_AST.prange uu____3011)
                            else ();
                            (let uu____3021 = annot_pat_var p3 t1  in
                             (uu____3021,
                               (LocalBinder
                                  ((let uu___116_3027 = x  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___116_3027.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___116_3027.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    }), aq)))))
                        in
                     (match uu____2975 with
                      | (p4,binder1) -> (loc1, env', binder1, p4, imp))))
           | FStar_Parser_AST.PatWild  ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____3049 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____3049, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____3060 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____3060, false)
           | FStar_Parser_AST.PatTvar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual aq  in
               let uu____3081 = resolvex loc env1 x  in
               (match uu____3081 with
                | (loc1,env2,xbv) ->
                    let uu____3103 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____3103, imp))
           | FStar_Parser_AST.PatVar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual aq  in
               let uu____3124 = resolvex loc env1 x  in
               (match uu____3124 with
                | (loc1,env2,xbv) ->
                    let uu____3146 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____3146, imp))
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
               let uu____3158 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, []))
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____3158, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____3182;_},args)
               ->
               let uu____3188 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____3229  ->
                        match uu____3229 with
                        | (loc1,env2,args1) ->
                            let uu____3277 = aux loc1 env2 arg  in
                            (match uu____3277 with
                             | (loc2,env3,uu____3306,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, [])
                  in
               (match uu____3188 with
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
                    let uu____3376 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                       in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)),
                      uu____3376, false))
           | FStar_Parser_AST.PatApp uu____3393 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                 p1.FStar_Parser_AST.prange
           | FStar_Parser_AST.PatList pats ->
               let uu____3415 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____3448  ->
                        match uu____3448 with
                        | (loc1,env2,pats1) ->
                            let uu____3480 = aux loc1 env2 pat  in
                            (match uu____3480 with
                             | (loc2,env3,uu____3505,pat1,uu____3507) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, [])
                  in
               (match uu____3415 with
                | (loc1,env2,pats1) ->
                    let pat =
                      let uu____3550 =
                        let uu____3553 =
                          let uu____3558 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange
                             in
                          pos_r uu____3558  in
                        let uu____3559 =
                          let uu____3560 =
                            let uu____3573 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Parser_Const.nil_lid
                                FStar_Syntax_Syntax.Delta_constant
                                (FStar_Pervasives_Native.Some
                                   FStar_Syntax_Syntax.Data_ctor)
                               in
                            (uu____3573, [])  in
                          FStar_Syntax_Syntax.Pat_cons uu____3560  in
                        FStar_All.pipe_left uu____3553 uu____3559  in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p
                                in
                             let uu____3605 =
                               let uu____3606 =
                                 let uu____3619 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.cons_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Data_ctor)
                                    in
                                 (uu____3619, [(hd1, false); (tl1, false)])
                                  in
                               FStar_Syntax_Syntax.Pat_cons uu____3606  in
                             FStar_All.pipe_left (pos_r r) uu____3605) pats1
                        uu____3550
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
               let uu____3663 =
                 FStar_List.fold_left
                   (fun uu____3703  ->
                      fun p2  ->
                        match uu____3703 with
                        | (loc1,env2,pats) ->
                            let uu____3752 = aux loc1 env2 p2  in
                            (match uu____3752 with
                             | (loc2,env3,uu____3781,pat,uu____3783) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args
                  in
               (match uu____3663 with
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
                    let uu____3878 =
                      FStar_Syntax_DsEnv.fail_or env2
                        (FStar_Syntax_DsEnv.try_lookup_lid env2) l
                       in
                    (match uu____3878 with
                     | (constr,uu____3900) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____3903 -> failwith "impossible"  in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (FStar_Pervasives_Native.Some
                                (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun
                            in
                         let uu____3905 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                            in
                         (loc1, env2,
                           (LocalBinder (x, FStar_Pervasives_Native.None)),
                           uu____3905, false)))
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
                      (fun uu____3976  ->
                         match uu____3976 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2)))
                  in
               let args =
                 FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                   (FStar_List.map
                      (fun uu____4006  ->
                         match uu____4006 with
                         | (f,uu____4012) ->
                             let uu____4013 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____4039  ->
                                       match uu____4039 with
                                       | (g,uu____4045) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText))
                                in
                             (match uu____4013 with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
                              | FStar_Pervasives_Native.Some (uu____4050,p2)
                                  -> p2)))
                  in
               let app =
                 let uu____4057 =
                   let uu____4058 =
                     let uu____4065 =
                       let uu____4066 =
                         let uu____4067 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                                [record.FStar_Syntax_DsEnv.constrname])
                            in
                         FStar_Parser_AST.PatName uu____4067  in
                       FStar_Parser_AST.mk_pattern uu____4066
                         p1.FStar_Parser_AST.prange
                        in
                     (uu____4065, args)  in
                   FStar_Parser_AST.PatApp uu____4058  in
                 FStar_Parser_AST.mk_pattern uu____4057
                   p1.FStar_Parser_AST.prange
                  in
               let uu____4070 = aux loc env1 app  in
               (match uu____4070 with
                | (env2,e,b,p2,uu____4099) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____4127 =
                            let uu____4128 =
                              let uu____4141 =
                                let uu___117_4142 = fv  in
                                let uu____4143 =
                                  let uu____4146 =
                                    let uu____4147 =
                                      let uu____4154 =
                                        FStar_All.pipe_right
                                          record.FStar_Syntax_DsEnv.fields
                                          (FStar_List.map
                                             FStar_Pervasives_Native.fst)
                                         in
                                      ((record.FStar_Syntax_DsEnv.typename),
                                        uu____4154)
                                       in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____4147
                                     in
                                  FStar_Pervasives_Native.Some uu____4146  in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___117_4142.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___117_4142.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____4143
                                }  in
                              (uu____4141, args1)  in
                            FStar_Syntax_Syntax.Pat_cons uu____4128  in
                          FStar_All.pipe_left pos uu____4127
                      | uu____4181 -> p2  in
                    (env2, e, b, p3, false))
         
         and aux loc env1 p1 = aux' false loc env1 p1
          in
         let aux_maybe_or env1 p1 =
           let loc = []  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____4231 = aux' true loc env1 p2  in
               (match uu____4231 with
                | (loc1,env2,var,p3,uu____4258) ->
                    let uu____4263 =
                      FStar_List.fold_left
                        (fun uu____4295  ->
                           fun p4  ->
                             match uu____4295 with
                             | (loc2,env3,ps1) ->
                                 let uu____4328 = aux' true loc2 env3 p4  in
                                 (match uu____4328 with
                                  | (loc3,env4,uu____4353,p5,uu____4355) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps
                       in
                    (match uu____4263 with
                     | (loc2,env3,ps1) ->
                         let pats = p3 :: (FStar_List.rev ps1)  in
                         (env3, var, pats)))
           | uu____4406 ->
               let uu____4407 = aux' true loc env1 p1  in
               (match uu____4407 with
                | (loc1,env2,vars,pat,b) -> (env2, vars, [pat]))
            in
         let uu____4447 = aux_maybe_or env p  in
         match uu____4447 with
         | (env1,b,pats) ->
             (check_linear_pattern_variables pats p.FStar_Parser_AST.prange;
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
            let uu____4506 =
              let uu____4507 =
                let uu____4518 = FStar_Syntax_DsEnv.qualify env x  in
                (uu____4518,
                  (FStar_Syntax_Syntax.tun, FStar_Pervasives_Native.None))
                 in
              LetBinder uu____4507  in
            (env, uu____4506, [])  in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____4546 =
                  let uu____4547 =
                    let uu____4552 =
                      FStar_Parser_AST.compile_op (Prims.parse_int "0")
                        x.FStar_Ident.idText x.FStar_Ident.idRange
                       in
                    (uu____4552, (x.FStar_Ident.idRange))  in
                  FStar_Ident.mk_ident uu____4547  in
                mklet uu____4546
            | FStar_Parser_AST.PatVar (x,uu____4554) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____4560);
                   FStar_Parser_AST.prange = uu____4561;_},(t,tacopt))
                ->
                let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)
                   in
                let uu____4581 =
                  let uu____4582 =
                    let uu____4593 = FStar_Syntax_DsEnv.qualify env x  in
                    let uu____4594 =
                      let uu____4601 = desugar_term env t  in
                      (uu____4601, tacopt1)  in
                    (uu____4593, uu____4594)  in
                  LetBinder uu____4582  in
                (env, uu____4581, [])
            | uu____4612 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_UnexpectedPattern,
                    "Unexpected pattern at the top-level")
                  p.FStar_Parser_AST.prange
          else
            (let uu____4622 = desugar_data_pat env p is_mut  in
             match uu____4622 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1 with
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                         uu____4651;
                       FStar_Syntax_Syntax.p = uu____4652;_}::[] -> []
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                         uu____4657;
                       FStar_Syntax_Syntax.p = uu____4658;_}::[] -> []
                   | uu____4663 -> p1  in
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
  fun uu____4670  ->
    fun env  ->
      fun pat  ->
        let uu____4673 = desugar_data_pat env pat false  in
        match uu____4673 with | (env1,uu____4689,pat1) -> (env1, pat1)

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
      fun uu____4707  ->
        fun range  ->
          match uu____4707 with
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
              ((let uu____4717 =
                  let uu____4718 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____4718  in
                if uu____4717
                then
                  let uu____4719 =
                    let uu____4724 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____4724)  in
                  FStar_Errors.log_issue range uu____4719
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
                  let uu____4732 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____4732 with
                  | FStar_Pervasives_Native.Some (intro_term,uu____4742) ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             FStar_Ident.lid_of_path
                               (FStar_Ident.path_of_text private_intro_nm)
                               range
                              in
                           let private_fv =
                             let uu____4752 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____4752 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___118_4753 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___118_4753.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___118_4753.FStar_Syntax_Syntax.vars)
                           }
                       | uu____4754 ->
                           failwith
                             (Prims.strcat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____4761 =
                        let uu____4766 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____4766)
                         in
                      FStar_Errors.raise_error uu____4761 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____4782 =
                  let uu____4785 =
                    let uu____4786 =
                      let uu____4801 =
                        let uu____4810 =
                          let uu____4817 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____4817)  in
                        [uu____4810]  in
                      (lid1, uu____4801)  in
                    FStar_Syntax_Syntax.Tm_app uu____4786  in
                  FStar_Syntax_Syntax.mk uu____4785  in
                uu____4782 FStar_Pervasives_Native.None range))

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
            let uu____4856 =
              FStar_Syntax_DsEnv.fail_or env
                ((if resolve
                  then FStar_Syntax_DsEnv.try_lookup_lid_with_attributes
                  else
                    FStar_Syntax_DsEnv.try_lookup_lid_with_attributes_no_resolve)
                   env) l
               in
            match uu____4856 with
            | (tm,mut,attrs) ->
                let warn_if_deprecated attrs1 =
                  FStar_List.iter
                    (fun a  ->
                       match a.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_app
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____4902;
                              FStar_Syntax_Syntax.vars = uu____4903;_},args)
                           when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____4926 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____4926 " is deprecated"  in
                           let msg1 =
                             if
                               (FStar_List.length args) >
                                 (Prims.parse_int "0")
                             then
                               let uu____4934 =
                                 let uu____4935 =
                                   let uu____4938 = FStar_List.hd args  in
                                   FStar_Pervasives_Native.fst uu____4938  in
                                 uu____4935.FStar_Syntax_Syntax.n  in
                               match uu____4934 with
                               | FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_string (s,uu____4954))
                                   when
                                   Prims.op_Negation
                                     ((FStar_Util.trim_string s) = "")
                                   ->
                                   Prims.strcat msg
                                     (Prims.strcat ", use "
                                        (Prims.strcat s " instead"))
                               | uu____4955 -> msg
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
                             let uu____4959 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____4959 " is deprecated"  in
                           FStar_Errors.log_issue
                             (FStar_Ident.range_of_lid l)
                             (FStar_Errors.Warning_DeprecatedDefinition, msg)
                       | uu____4960 -> ()) attrs1
                   in
                (warn_if_deprecated attrs;
                 (let tm1 = setpos tm  in
                  if mut
                  then
                    let uu____4965 =
                      let uu____4966 =
                        let uu____4973 = mk_ref_read tm1  in
                        (uu____4973,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Mutable_rval))
                         in
                      FStar_Syntax_Syntax.Tm_meta uu____4966  in
                    FStar_All.pipe_left mk1 uu____4965
                  else tm1))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____4989 =
          let uu____4990 = unparen t  in uu____4990.FStar_Parser_AST.tm  in
        match uu____4989 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____4991; FStar_Ident.ident = uu____4992;
              FStar_Ident.nsstr = uu____4993; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____4996 ->
            let uu____4997 =
              let uu____5002 =
                let uu____5003 = FStar_Parser_AST.term_to_string t  in
                Prims.strcat "Unknown attribute " uu____5003  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____5002)  in
            FStar_Errors.raise_error uu____4997 t.FStar_Parser_AST.range
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
          let uu___119_5023 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___119_5023.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___119_5023.FStar_Syntax_Syntax.vars)
          }  in
        let uu____5026 =
          let uu____5027 = unparen top  in uu____5027.FStar_Parser_AST.tm  in
        match uu____5026 with
        | FStar_Parser_AST.Wild  -> setpos FStar_Syntax_Syntax.tun
        | FStar_Parser_AST.Labeled uu____5028 -> desugar_formula env top
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
        | FStar_Parser_AST.Op (op_star,uu____5079::uu____5080::[]) when
            ((FStar_Ident.text_of_id op_star) = "*") &&
              (let uu____5084 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____5084 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____5097;_},t1::t2::[])
                  ->
                  let uu____5102 = flatten1 t1  in
                  FStar_List.append uu____5102 [t2]
              | uu____5105 -> [t]  in
            let targs =
              let uu____5109 =
                let uu____5112 = unparen top  in flatten1 uu____5112  in
              FStar_All.pipe_right uu____5109
                (FStar_List.map
                   (fun t  ->
                      let uu____5120 = desugar_typ env t  in
                      FStar_Syntax_Syntax.as_arg uu____5120))
               in
            let uu____5121 =
              let uu____5126 =
                FStar_Parser_Const.mk_tuple_lid (FStar_List.length targs)
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_DsEnv.fail_or env
                (FStar_Syntax_DsEnv.try_lookup_lid env) uu____5126
               in
            (match uu____5121 with
             | (tup,uu____5132) ->
                 mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs)))
        | FStar_Parser_AST.Tvar a ->
            let uu____5136 =
              let uu____5139 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_Pervasives_Native.fst uu____5139  in
            FStar_All.pipe_left setpos uu____5136
        | FStar_Parser_AST.Uvar u ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedUniverseVariable,
                (Prims.strcat "Unexpected universe variable "
                   (Prims.strcat (FStar_Ident.text_of_id u)
                      " in non-universe context")))
              top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____5159 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____5159 with
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
                             let uu____5191 = desugar_term env t  in
                             (uu____5191, FStar_Pervasives_Native.None)))
                      in
                   mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))
                 else op)
        | FStar_Parser_AST.Construct (n1,(a,uu____5205)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____5220 =
              let uu___120_5221 = top  in
              let uu____5222 =
                let uu____5223 =
                  let uu____5230 =
                    let uu___121_5231 = top  in
                    let uu____5232 =
                      let uu____5233 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____5233  in
                    {
                      FStar_Parser_AST.tm = uu____5232;
                      FStar_Parser_AST.range =
                        (uu___121_5231.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___121_5231.FStar_Parser_AST.level)
                    }  in
                  (uu____5230, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____5223  in
              {
                FStar_Parser_AST.tm = uu____5222;
                FStar_Parser_AST.range =
                  (uu___120_5221.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___120_5221.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____5220
        | FStar_Parser_AST.Construct (n1,(a,uu____5236)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____5252 =
                let uu___122_5253 = top  in
                let uu____5254 =
                  let uu____5255 =
                    let uu____5262 =
                      let uu___123_5263 = top  in
                      let uu____5264 =
                        let uu____5265 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____5265  in
                      {
                        FStar_Parser_AST.tm = uu____5264;
                        FStar_Parser_AST.range =
                          (uu___123_5263.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___123_5263.FStar_Parser_AST.level)
                      }  in
                    (uu____5262, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____5255  in
                {
                  FStar_Parser_AST.tm = uu____5254;
                  FStar_Parser_AST.range =
                    (uu___122_5253.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___122_5253.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____5252))
        | FStar_Parser_AST.Construct (n1,(a,uu____5268)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____5283 =
              let uu___124_5284 = top  in
              let uu____5285 =
                let uu____5286 =
                  let uu____5293 =
                    let uu___125_5294 = top  in
                    let uu____5295 =
                      let uu____5296 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____5296  in
                    {
                      FStar_Parser_AST.tm = uu____5295;
                      FStar_Parser_AST.range =
                        (uu___125_5294.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___125_5294.FStar_Parser_AST.level)
                    }  in
                  (uu____5293, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____5286  in
              {
                FStar_Parser_AST.tm = uu____5285;
                FStar_Parser_AST.range =
                  (uu___124_5284.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___124_5284.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____5283
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5297; FStar_Ident.ident = uu____5298;
              FStar_Ident.nsstr = uu____5299; FStar_Ident.str = "Type0";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5302; FStar_Ident.ident = uu____5303;
              FStar_Ident.nsstr = uu____5304; FStar_Ident.str = "Type";_}
            ->
            mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____5307; FStar_Ident.ident = uu____5308;
               FStar_Ident.nsstr = uu____5309; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____5327 =
              let uu____5328 = desugar_universe t  in
              FStar_Syntax_Syntax.Tm_type uu____5328  in
            mk1 uu____5327
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5329; FStar_Ident.ident = uu____5330;
              FStar_Ident.nsstr = uu____5331; FStar_Ident.str = "Effect";_}
            -> mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5334; FStar_Ident.ident = uu____5335;
              FStar_Ident.nsstr = uu____5336; FStar_Ident.str = "True";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5339; FStar_Ident.ident = uu____5340;
              FStar_Ident.nsstr = uu____5341; FStar_Ident.str = "False";_}
            ->
            FStar_Syntax_Syntax.fvar
              (FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                 top.FStar_Parser_AST.range)
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____5346;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____5348 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____5348 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  FStar_Syntax_Syntax.fvar lid
                    (FStar_Syntax_Syntax.Delta_defined_at_level
                       (Prims.parse_int "1")) FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.None  ->
                  let uu____5353 =
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      (FStar_Ident.text_of_lid eff_name) txt
                     in
                  failwith uu____5353))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             desugar_name mk1 setpos env true l)
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             desugar_name mk1 setpos env true l)
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____5368 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____5368 with
                | FStar_Pervasives_Native.Some uu____5377 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____5382 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____5382 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____5396 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____5409 =
                    FStar_Syntax_Util.mk_field_projector_name_from_ident
                      new_name i
                     in
                  desugar_name mk1 setpos env resolve uu____5409
              | uu____5410 ->
                  let uu____5417 =
                    let uu____5422 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____5422)  in
                  FStar_Errors.raise_error uu____5417
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____5425 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____5425 with
              | FStar_Pervasives_Native.None  ->
                  let uu____5428 =
                    let uu____5433 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____5433)
                     in
                  FStar_Errors.raise_error uu____5428
                    top.FStar_Parser_AST.range
              | uu____5434 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  desugar_name mk1 setpos env true lid'))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____5453 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____5453 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> head2
                   | uu____5464 ->
                       let uu____5471 =
                         FStar_Util.take
                           (fun uu____5495  ->
                              match uu____5495 with
                              | (uu____5500,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____5471 with
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
                                (fun uu____5564  ->
                                   match uu____5564 with
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
                    let uu____5605 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____5605 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.strcat "Constructor "
                             (Prims.strcat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____5612 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.strcat "Effect "
                             (Prims.strcat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____5619 =
              FStar_List.fold_left
                (fun uu____5664  ->
                   fun b  ->
                     match uu____5664 with
                     | (env1,tparams,typs) ->
                         let uu____5721 = desugar_binder env1 b  in
                         (match uu____5721 with
                          | (xopt,t1) ->
                              let uu____5750 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____5759 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____5759)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____5750 with
                               | (env2,x) ->
                                   let uu____5779 =
                                     let uu____5782 =
                                       let uu____5785 =
                                         let uu____5786 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____5786
                                          in
                                       [uu____5785]  in
                                     FStar_List.append typs uu____5782  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___126_5812 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___126_5812.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___126_5812.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____5779)))) (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      FStar_Pervasives_Native.None])
               in
            (match uu____5619 with
             | (env1,uu____5836,targs) ->
                 let uu____5858 =
                   let uu____5863 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____5863
                    in
                 (match uu____5858 with
                  | (tup,uu____5869) ->
                      FStar_All.pipe_left mk1
                        (FStar_Syntax_Syntax.Tm_app (tup, targs))))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____5880 = uncurry binders t  in
            (match uu____5880 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___92_5912 =
                   match uu___92_5912 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1  in
                       let uu____5926 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____5926
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____5948 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____5948 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 aux env [] bs)
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____5963 = desugar_binder env b  in
            (match uu____5963 with
             | (FStar_Pervasives_Native.None ,uu____5970) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____5980 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____5980 with
                  | ((x,uu____5986),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____5993 = FStar_Syntax_Util.refine x f1  in
                      FStar_All.pipe_left setpos uu____5993))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern)
               in
            let uu____6013 =
              FStar_List.fold_left
                (fun uu____6033  ->
                   fun pat  ->
                     match uu____6033 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed
                              (uu____6059,(t,FStar_Pervasives_Native.None ))
                              ->
                              let uu____6069 =
                                let uu____6072 = free_type_vars env1 t  in
                                FStar_List.append uu____6072 ftvs  in
                              (env1, uu____6069)
                          | FStar_Parser_AST.PatAscribed
                              (uu____6077,(t,FStar_Pervasives_Native.Some
                                           tac))
                              ->
                              let uu____6088 =
                                let uu____6091 = free_type_vars env1 t  in
                                let uu____6094 =
                                  let uu____6097 = free_type_vars env1 tac
                                     in
                                  FStar_List.append uu____6097 ftvs  in
                                FStar_List.append uu____6091 uu____6094  in
                              (env1, uu____6088)
                          | uu____6102 -> (env1, ftvs))) (env, []) binders1
               in
            (match uu____6013 with
             | (uu____6107,ftv) ->
                 let ftv1 = sort_ftv ftv  in
                 let binders2 =
                   let uu____6119 =
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
                   FStar_List.append uu____6119 binders1  in
                 let rec aux env1 bs sc_pat_opt uu___93_6160 =
                   match uu___93_6160 with
                   | [] ->
                       let body1 = desugar_term env1 body  in
                       let body2 =
                         match sc_pat_opt with
                         | FStar_Pervasives_Native.Some (sc,pat) ->
                             let body2 =
                               let uu____6198 =
                                 let uu____6199 =
                                   FStar_Syntax_Syntax.pat_bvs pat  in
                                 FStar_All.pipe_right uu____6199
                                   (FStar_List.map
                                      FStar_Syntax_Syntax.mk_binder)
                                  in
                               FStar_Syntax_Subst.close uu____6198 body1  in
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_match
                                  (sc,
                                    [(pat, FStar_Pervasives_Native.None,
                                       body2)])) FStar_Pervasives_Native.None
                               body2.FStar_Syntax_Syntax.pos
                         | FStar_Pervasives_Native.None  -> body1  in
                       let uu____6252 =
                         no_annot_abs (FStar_List.rev bs) body2  in
                       setpos uu____6252
                   | p::rest ->
                       let uu____6263 = desugar_binding_pat env1 p  in
                       (match uu____6263 with
                        | (env2,b,pat) ->
                            let pat1 =
                              match pat with
                              | [] -> FStar_Pervasives_Native.None
                              | p1::[] -> FStar_Pervasives_Native.Some p1
                              | uu____6287 ->
                                  FStar_Errors.raise_error
                                    (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                      "Disjunctive patterns are not supported in abstractions")
                                    p.FStar_Parser_AST.prange
                               in
                            let uu____6292 =
                              match b with
                              | LetBinder uu____6325 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat1, sc_pat_opt) with
                                    | (FStar_Pervasives_Native.None
                                       ,uu____6381) -> sc_pat_opt
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.None ) ->
                                        let uu____6417 =
                                          let uu____6422 =
                                            FStar_Syntax_Syntax.bv_to_name x
                                             in
                                          (uu____6422, p1)  in
                                        FStar_Pervasives_Native.Some
                                          uu____6417
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.Some
                                       (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____6458,uu____6459) ->
                                             let tup2 =
                                               let uu____6461 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____6461
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____6465 =
                                                 let uu____6468 =
                                                   let uu____6469 =
                                                     let uu____6484 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2)
                                                        in
                                                     let uu____6487 =
                                                       let uu____6490 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc
                                                          in
                                                       let uu____6491 =
                                                         let uu____6494 =
                                                           let uu____6495 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x
                                                              in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____6495
                                                            in
                                                         [uu____6494]  in
                                                       uu____6490 ::
                                                         uu____6491
                                                        in
                                                     (uu____6484, uu____6487)
                                                      in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____6469
                                                    in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____6468
                                                  in
                                               uu____6465
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Parser_AST.range
                                                in
                                             let p2 =
                                               let uu____6506 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p1, false)]))
                                                 uu____6506
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____6537,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____6539,pats)) ->
                                             let tupn =
                                               let uu____6578 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____6578
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____6588 =
                                                 let uu____6589 =
                                                   let uu____6604 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn)
                                                      in
                                                   let uu____6607 =
                                                     let uu____6616 =
                                                       let uu____6625 =
                                                         let uu____6626 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____6626
                                                          in
                                                       [uu____6625]  in
                                                     FStar_List.append args
                                                       uu____6616
                                                      in
                                                   (uu____6604, uu____6607)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____6589
                                                  in
                                               mk1 uu____6588  in
                                             let p2 =
                                               let uu____6646 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p1, false)])))
                                                 uu____6646
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | uu____6681 ->
                                             failwith "Impossible")
                                     in
                                  ((x, aq), sc_pat_opt1)
                               in
                            (match uu____6292 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest))
                    in
                 aux env [] FStar_Pervasives_Native.None binders2)
        | FStar_Parser_AST.App
            (uu____6748,uu____6749,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____6763 =
                let uu____6764 = unparen e  in uu____6764.FStar_Parser_AST.tm
                 in
              match uu____6763 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____6770 ->
                  let head1 = desugar_term env e  in
                  mk1 (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
               in
            aux [] top
        | FStar_Parser_AST.App uu____6774 ->
            let rec aux args e =
              let uu____6806 =
                let uu____6807 = unparen e  in uu____6807.FStar_Parser_AST.tm
                 in
              match uu____6806 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let arg =
                    let uu____6820 = desugar_term env t  in
                    FStar_All.pipe_left (arg_withimp_e imp) uu____6820  in
                  aux (arg :: args) e1
              | uu____6833 ->
                  let head1 = desugar_term env e  in
                  mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))
               in
            aux [] top
        | FStar_Parser_AST.Bind (x,t1,t2) ->
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
            let uu____6860 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term env uu____6860
        | FStar_Parser_AST.Seq (t1,t2) ->
            let uu____6863 =
              let uu____6864 =
                let uu____6871 =
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
                (uu____6871,
                  (FStar_Syntax_Syntax.Meta_desugared
                     FStar_Syntax_Syntax.Sequence))
                 in
              FStar_Syntax_Syntax.Tm_meta uu____6864  in
            mk1 uu____6863
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____6923 =
              let uu____6928 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____6928 then desugar_typ else desugar_term  in
            uu____6923 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____6971 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____7114  ->
                        match uu____7114 with
                        | (attr_opt,(p,def)) ->
                            let uu____7172 = is_app_pattern p  in
                            if uu____7172
                            then
                              let uu____7203 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____7203, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____7285 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____7285, def1)
                               | uu____7330 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____7368);
                                           FStar_Parser_AST.prange =
                                             uu____7369;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____7417 =
                                            let uu____7438 =
                                              let uu____7443 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____7443  in
                                            (uu____7438, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____7417, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____7534) ->
                                        if top_level
                                        then
                                          let uu____7569 =
                                            let uu____7590 =
                                              let uu____7595 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____7595  in
                                            (uu____7590, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____7569, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____7685 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____7716 =
                FStar_List.fold_left
                  (fun uu____7789  ->
                     fun uu____7790  ->
                       match (uu____7789, uu____7790) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____7898,uu____7899),uu____7900))
                           ->
                           let uu____8017 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____8043 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____8043 with
                                  | (env2,xx) ->
                                      let uu____8062 =
                                        let uu____8065 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____8065 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx), uu____8062))
                             | FStar_Util.Inr l ->
                                 let uu____8073 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.Delta_equational
                                    in
                                 (uu____8073, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____8017 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____7716 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____8211 =
                    match uu____8211 with
                    | (attrs_opt,(uu____8247,args,result_t),def) ->
                        let args1 =
                          FStar_All.pipe_right args
                            (FStar_List.map replace_unit_pattern)
                           in
                        let pos = def.FStar_Parser_AST.range  in
                        let def1 =
                          match result_t with
                          | FStar_Pervasives_Native.None  -> def
                          | FStar_Pervasives_Native.Some (t,tacopt) ->
                              let t1 =
                                let uu____8335 = is_comp_type env1 t  in
                                if uu____8335
                                then
                                  ((let uu____8337 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____8347 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____8347))
                                       in
                                    match uu____8337 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____8350 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____8352 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____8352))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____8350
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t)
                                 in
                              let uu____8356 =
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range
                                 in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed (def, t1, tacopt))
                                uu____8356 FStar_Parser_AST.Expr
                           in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____8360 ->
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
                              let uu____8375 =
                                let uu____8376 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____8376
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____8375
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
                          (attrs, lbname1, FStar_Syntax_Syntax.tun, body2,
                            pos)
                     in
                  let lbs1 =
                    FStar_List.map2
                      (desugar_one_def (if is_rec then env' else env))
                      fnames1 funs
                     in
                  let body1 = desugar_term env' body  in
                  let uu____8436 =
                    let uu____8437 =
                      let uu____8450 =
                        FStar_Syntax_Subst.close rec_bindings1 body1  in
                      ((is_rec, lbs1), uu____8450)  in
                    FStar_Syntax_Syntax.Tm_let uu____8437  in
                  FStar_All.pipe_left mk1 uu____8436
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
              let uu____8504 =
                desugar_binding_pat_maybe_top top_level env pat is_mutable
                 in
              match uu____8504 with
              | (env1,binder,pat1) ->
                  let tm =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let body1 = desugar_term env1 t2  in
                        let fv =
                          let uu____8542 =
                            FStar_Syntax_Util.incr_delta_qualifier t12  in
                          FStar_Syntax_Syntax.lid_as_fv l uu____8542
                            FStar_Pervasives_Native.None
                           in
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_let
                             ((false,
                                [mk_lb
                                   (attrs, (FStar_Util.Inr fv), t, t12,
                                     (t12.FStar_Syntax_Syntax.pos))]), body1))
                    | LocalBinder (x,uu____8562) ->
                        let body1 = desugar_term env1 t2  in
                        let body2 =
                          match pat1 with
                          | [] -> body1
                          | {
                              FStar_Syntax_Syntax.v =
                                FStar_Syntax_Syntax.Pat_wild uu____8565;
                              FStar_Syntax_Syntax.p = uu____8566;_}::[] ->
                              body1
                          | uu____8571 ->
                              let uu____8574 =
                                let uu____8577 =
                                  let uu____8578 =
                                    let uu____8601 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    let uu____8602 =
                                      desugar_disjunctive_pattern pat1
                                        FStar_Pervasives_Native.None body1
                                       in
                                    (uu____8601, uu____8602)  in
                                  FStar_Syntax_Syntax.Tm_match uu____8578  in
                                FStar_Syntax_Syntax.mk uu____8577  in
                              uu____8574 FStar_Pervasives_Native.None
                                top.FStar_Parser_AST.range
                           in
                        let uu____8612 =
                          let uu____8613 =
                            let uu____8626 =
                              let uu____8627 =
                                let uu____8628 =
                                  FStar_Syntax_Syntax.mk_binder x  in
                                [uu____8628]  in
                              FStar_Syntax_Subst.close uu____8627 body2  in
                            ((false,
                               [mk_lb
                                  (attrs, (FStar_Util.Inl x),
                                    (x.FStar_Syntax_Syntax.sort), t12,
                                    (t12.FStar_Syntax_Syntax.pos))]),
                              uu____8626)
                             in
                          FStar_Syntax_Syntax.Tm_let uu____8613  in
                        FStar_All.pipe_left mk1 uu____8612
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
            let uu____8656 = FStar_List.hd lbs  in
            (match uu____8656 with
             | (attrs,(head_pat,defn)) ->
                 let uu____8696 = is_rec || (is_app_pattern head_pat)  in
                 if uu____8696
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____8705 =
                let uu____8706 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.Delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____8706  in
              mk1 uu____8705  in
            let uu____8707 =
              let uu____8708 =
                let uu____8731 =
                  let uu____8734 = desugar_term env t1  in
                  FStar_Syntax_Util.ascribe uu____8734
                    ((FStar_Util.Inl t_bool1), FStar_Pervasives_Native.None)
                   in
                let uu____8755 =
                  let uu____8770 =
                    let uu____8783 =
                      FStar_Syntax_Syntax.withinfo
                        (FStar_Syntax_Syntax.Pat_constant
                           (FStar_Const.Const_bool true))
                        t2.FStar_Parser_AST.range
                       in
                    let uu____8786 = desugar_term env t2  in
                    (uu____8783, FStar_Pervasives_Native.None, uu____8786)
                     in
                  let uu____8795 =
                    let uu____8810 =
                      let uu____8823 =
                        FStar_Syntax_Syntax.withinfo
                          (FStar_Syntax_Syntax.Pat_wild x)
                          t3.FStar_Parser_AST.range
                         in
                      let uu____8826 = desugar_term env t3  in
                      (uu____8823, FStar_Pervasives_Native.None, uu____8826)
                       in
                    [uu____8810]  in
                  uu____8770 :: uu____8795  in
                (uu____8731, uu____8755)  in
              FStar_Syntax_Syntax.Tm_match uu____8708  in
            mk1 uu____8707
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
            let desugar_branch uu____8967 =
              match uu____8967 with
              | (pat,wopt,b) ->
                  let uu____8985 = desugar_match_pat env pat  in
                  (match uu____8985 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____9006 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____9006
                          in
                       let b1 = desugar_term env1 b  in
                       desugar_disjunctive_pattern pat1 wopt1 b1)
               in
            let uu____9008 =
              let uu____9009 =
                let uu____9032 = desugar_term env e  in
                let uu____9033 = FStar_List.collect desugar_branch branches
                   in
                (uu____9032, uu____9033)  in
              FStar_Syntax_Syntax.Tm_match uu____9009  in
            FStar_All.pipe_left mk1 uu____9008
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____9062 = is_comp_type env t  in
              if uu____9062
              then
                let uu____9069 = desugar_comp t.FStar_Parser_AST.range env t
                   in
                FStar_Util.Inr uu____9069
              else
                (let uu____9075 = desugar_term env t  in
                 FStar_Util.Inl uu____9075)
               in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)  in
            let uu____9081 =
              let uu____9082 =
                let uu____9109 = desugar_term env e  in
                (uu____9109, (annot, tac_opt1), FStar_Pervasives_Native.None)
                 in
              FStar_Syntax_Syntax.Tm_ascribed uu____9082  in
            FStar_All.pipe_left mk1 uu____9081
        | FStar_Parser_AST.Record (uu____9134,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____9171 = FStar_List.hd fields  in
              match uu____9171 with | (f,uu____9183) -> f.FStar_Ident.ns  in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____9225  ->
                        match uu____9225 with
                        | (g,uu____9231) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____9237,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____9251 =
                         let uu____9256 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____9256)
                          in
                       FStar_Errors.raise_error uu____9251
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
                  let uu____9264 =
                    let uu____9275 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____9306  ->
                              match uu____9306 with
                              | (f,uu____9316) ->
                                  let uu____9317 =
                                    let uu____9318 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____9318
                                     in
                                  (uu____9317, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____9275)  in
                  FStar_Parser_AST.Construct uu____9264
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____9336 =
                      let uu____9337 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____9337  in
                    FStar_Parser_AST.mk_term uu____9336 x.FStar_Ident.idRange
                      FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____9339 =
                      let uu____9352 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____9382  ->
                                match uu____9382 with
                                | (f,uu____9392) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____9352)  in
                    FStar_Parser_AST.Record uu____9339  in
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
                    FStar_Syntax_Syntax.pos = uu____9454;
                    FStar_Syntax_Syntax.vars = uu____9455;_},args)
                 ->
                 let uu____9477 =
                   let uu____9478 =
                     let uu____9493 =
                       let uu____9494 =
                         let uu____9497 =
                           let uu____9498 =
                             let uu____9505 =
                               FStar_All.pipe_right
                                 record.FStar_Syntax_DsEnv.fields
                                 (FStar_List.map FStar_Pervasives_Native.fst)
                                in
                             ((record.FStar_Syntax_DsEnv.typename),
                               uu____9505)
                              in
                           FStar_Syntax_Syntax.Record_ctor uu____9498  in
                         FStar_Pervasives_Native.Some uu____9497  in
                       FStar_Syntax_Syntax.fvar
                         (FStar_Ident.set_lid_range
                            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                            e.FStar_Syntax_Syntax.pos)
                         FStar_Syntax_Syntax.Delta_constant uu____9494
                        in
                     (uu____9493, args)  in
                   FStar_Syntax_Syntax.Tm_app uu____9478  in
                 FStar_All.pipe_left mk1 uu____9477
             | uu____9532 -> e)
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____9536 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____9536 with
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
                  let uu____9555 =
                    let uu____9556 =
                      let uu____9571 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range projname
                             (FStar_Ident.range_of_lid f))
                          FStar_Syntax_Syntax.Delta_equational qual
                         in
                      let uu____9572 =
                        let uu____9575 = FStar_Syntax_Syntax.as_arg e1  in
                        [uu____9575]  in
                      (uu____9571, uu____9572)  in
                    FStar_Syntax_Syntax.Tm_app uu____9556  in
                  FStar_All.pipe_left mk1 uu____9555))
        | FStar_Parser_AST.NamedTyp (uu____9580,e) -> desugar_term env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____9585 =
              let uu____9586 = FStar_Syntax_Subst.compress tm  in
              uu____9586.FStar_Syntax_Syntax.n  in
            (match uu____9585 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu___127_9590 =
                   let uu____9591 =
                     let uu____9592 = FStar_Syntax_Syntax.lid_of_fv fv  in
                     FStar_Ident.string_of_lid uu____9592  in
                   FStar_Syntax_Util.exp_string uu____9591  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___127_9590.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                   FStar_Syntax_Syntax.vars =
                     (uu___127_9590.FStar_Syntax_Syntax.vars)
                 }
             | uu____9593 ->
                 let uu____9594 =
                   let uu____9599 =
                     let uu____9600 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.strcat "VQuote, expected an fvar, got: "
                       uu____9600
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____9599)  in
                 FStar_Errors.raise_error uu____9594
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,qi) ->
            let qi1 =
              match qi with
              | FStar_Parser_AST.Static  ->
                  {
                    FStar_Syntax_Syntax.qkind =
                      FStar_Syntax_Syntax.Quote_static
                  }
              | FStar_Parser_AST.Dynamic  ->
                  {
                    FStar_Syntax_Syntax.qkind =
                      FStar_Syntax_Syntax.Quote_dynamic
                  }
               in
            let uu____9604 =
              let uu____9605 =
                let uu____9612 = desugar_term env e  in (uu____9612, qi1)  in
              FStar_Syntax_Syntax.Tm_quoted uu____9605  in
            FStar_All.pipe_left mk1 uu____9604
        | uu____9615 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            desugar_formula env top
        | uu____9616 ->
            let uu____9617 =
              let uu____9622 =
                let uu____9623 = FStar_Parser_AST.term_to_string top  in
                Prims.strcat "Unexpected term: " uu____9623  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____9622)  in
            FStar_Errors.raise_error uu____9617 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____9625 -> false
    | uu____9634 -> true

and (is_synth_by_tactic :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (l,r,FStar_Parser_AST.Hash ) ->
          is_synth_by_tactic e l
      | FStar_Parser_AST.Var lid ->
          let uu____9640 =
            FStar_Syntax_DsEnv.resolve_to_fully_qualified_name e lid  in
          (match uu____9640 with
           | FStar_Pervasives_Native.Some lid1 ->
               FStar_Ident.lid_equals lid1 FStar_Parser_Const.synth_lid
           | FStar_Pervasives_Native.None  -> false)
      | uu____9644 -> false

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
           (fun uu____9681  ->
              match uu____9681 with
              | (a,imp) ->
                  let uu____9694 = desugar_term env a  in
                  arg_withimp_e imp uu____9694))

and (desugar_comp :
  FStar_Range.range ->
    FStar_Syntax_DsEnv.env ->
      FStar_Parser_AST.term ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun r  ->
    fun env  ->
      fun t  ->
        let fail1 a err = FStar_Errors.raise_error err r  in
        let is_requires uu____9720 =
          match uu____9720 with
          | (t1,uu____9726) ->
              let uu____9727 =
                let uu____9728 = unparen t1  in
                uu____9728.FStar_Parser_AST.tm  in
              (match uu____9727 with
               | FStar_Parser_AST.Requires uu____9729 -> true
               | uu____9736 -> false)
           in
        let is_ensures uu____9744 =
          match uu____9744 with
          | (t1,uu____9750) ->
              let uu____9751 =
                let uu____9752 = unparen t1  in
                uu____9752.FStar_Parser_AST.tm  in
              (match uu____9751 with
               | FStar_Parser_AST.Ensures uu____9753 -> true
               | uu____9760 -> false)
           in
        let is_app head1 uu____9771 =
          match uu____9771 with
          | (t1,uu____9777) ->
              let uu____9778 =
                let uu____9779 = unparen t1  in
                uu____9779.FStar_Parser_AST.tm  in
              (match uu____9778 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____9781;
                      FStar_Parser_AST.level = uu____9782;_},uu____9783,uu____9784)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____9785 -> false)
           in
        let is_smt_pat uu____9793 =
          match uu____9793 with
          | (t1,uu____9799) ->
              let uu____9800 =
                let uu____9801 = unparen t1  in
                uu____9801.FStar_Parser_AST.tm  in
              (match uu____9800 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____9804);
                             FStar_Parser_AST.range = uu____9805;
                             FStar_Parser_AST.level = uu____9806;_},uu____9807)::uu____9808::[])
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
                             FStar_Parser_AST.range = uu____9847;
                             FStar_Parser_AST.level = uu____9848;_},uu____9849)::uu____9850::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
               | uu____9875 -> false)
           in
        let is_decreases = is_app "decreases"  in
        let pre_process_comp_typ t1 =
          let uu____9903 = head_and_args t1  in
          match uu____9903 with
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
                   let thunk_ens uu____9997 =
                     match uu____9997 with
                     | (e,i) ->
                         let uu____10008 = thunk_ens_ e  in (uu____10008, i)
                      in
                   let fail_lemma uu____10018 =
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
                         let uu____10098 =
                           let uu____10105 =
                             let uu____10112 = thunk_ens ens  in
                             [uu____10112; nil_pat]  in
                           req_true :: uu____10105  in
                         unit_tm :: uu____10098
                     | req::ens::[] when
                         (is_requires req) && (is_ensures ens) ->
                         let uu____10159 =
                           let uu____10166 =
                             let uu____10173 = thunk_ens ens  in
                             [uu____10173; nil_pat]  in
                           req :: uu____10166  in
                         unit_tm :: uu____10159
                     | ens::smtpat::[] when
                         (((let uu____10222 = is_requires ens  in
                            Prims.op_Negation uu____10222) &&
                             (let uu____10224 = is_smt_pat ens  in
                              Prims.op_Negation uu____10224))
                            &&
                            (let uu____10226 = is_decreases ens  in
                             Prims.op_Negation uu____10226))
                           && (is_smt_pat smtpat)
                         ->
                         let uu____10227 =
                           let uu____10234 =
                             let uu____10241 = thunk_ens ens  in
                             [uu____10241; smtpat]  in
                           req_true :: uu____10234  in
                         unit_tm :: uu____10227
                     | ens::dec::[] when
                         (is_ensures ens) && (is_decreases dec) ->
                         let uu____10288 =
                           let uu____10295 =
                             let uu____10302 = thunk_ens ens  in
                             [uu____10302; nil_pat; dec]  in
                           req_true :: uu____10295  in
                         unit_tm :: uu____10288
                     | ens::dec::smtpat::[] when
                         ((is_ensures ens) && (is_decreases dec)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____10362 =
                           let uu____10369 =
                             let uu____10376 = thunk_ens ens  in
                             [uu____10376; smtpat; dec]  in
                           req_true :: uu____10369  in
                         unit_tm :: uu____10362
                     | req::ens::dec::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_decreases dec)
                         ->
                         let uu____10436 =
                           let uu____10443 =
                             let uu____10450 = thunk_ens ens  in
                             [uu____10450; nil_pat; dec]  in
                           req :: uu____10443  in
                         unit_tm :: uu____10436
                     | req::ens::smtpat::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____10510 =
                           let uu____10517 =
                             let uu____10524 = thunk_ens ens  in
                             [uu____10524; smtpat]  in
                           req :: uu____10517  in
                         unit_tm :: uu____10510
                     | req::ens::dec::smtpat::[] when
                         (((is_requires req) && (is_ensures ens)) &&
                            (is_smt_pat smtpat))
                           && (is_decreases dec)
                         ->
                         let uu____10589 =
                           let uu____10596 =
                             let uu____10603 = thunk_ens ens  in
                             [uu____10603; dec; smtpat]  in
                           req :: uu____10596  in
                         unit_tm :: uu____10589
                     | _other -> fail_lemma ()  in
                   let head_and_attributes =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) lemma
                      in
                   (head_and_attributes, args1)
               | FStar_Parser_AST.Name l when
                   FStar_Syntax_DsEnv.is_effect_name env l ->
                   let uu____10665 =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) l
                      in
                   (uu____10665, args)
               | FStar_Parser_AST.Name l when
                   (let uu____10693 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____10693
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Parser_Const.effect_Tot_lid
                        head1.FStar_Parser_AST.range), []), args)
               | FStar_Parser_AST.Name l when
                   (let uu____10711 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____10711
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
               | uu____10749 ->
                   let default_effect =
                     let uu____10751 = FStar_Options.ml_ish ()  in
                     if uu____10751
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____10754 =
                           FStar_Options.warn_default_effects ()  in
                         if uu____10754
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
        let uu____10778 = pre_process_comp_typ t  in
        match uu____10778 with
        | ((eff,cattributes),args) ->
            (Obj.magic
               (if (FStar_List.length args) = (Prims.parse_int "0")
                then
                  Obj.repr
                    (let uu____10827 =
                       let uu____10832 =
                         let uu____10833 =
                           FStar_Syntax_Print.lid_to_string eff  in
                         FStar_Util.format1 "Not enough args to effect %s"
                           uu____10833
                          in
                       (FStar_Errors.Fatal_NotEnoughArgsToEffect,
                         uu____10832)
                        in
                     fail1 () uu____10827)
                else Obj.repr ());
             (let is_universe uu____10842 =
                match uu____10842 with
                | (uu____10847,imp) -> imp = FStar_Parser_AST.UnivApp  in
              let uu____10849 = FStar_Util.take is_universe args  in
              match uu____10849 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____10908  ->
                         match uu____10908 with
                         | (u,imp) -> desugar_universe u) universes
                     in
                  let uu____10915 =
                    let uu____10930 = FStar_List.hd args1  in
                    let uu____10939 = FStar_List.tl args1  in
                    (uu____10930, uu____10939)  in
                  (match uu____10915 with
                   | (result_arg,rest) ->
                       let result_typ =
                         desugar_typ env
                           (FStar_Pervasives_Native.fst result_arg)
                          in
                       let rest1 = desugar_args env rest  in
                       let uu____10994 =
                         let is_decrease uu____11030 =
                           match uu____11030 with
                           | (t1,uu____11040) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.pos = uu____11050;
                                       FStar_Syntax_Syntax.vars = uu____11051;_},uu____11052::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.decreases_lid
                                | uu____11083 -> false)
                            in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease)
                          in
                       (match uu____10994 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____11197  ->
                                      match uu____11197 with
                                      | (t1,uu____11207) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____11216,(arg,uu____11218)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____11247 -> failwith "impos")))
                               in
                            let no_additional_args =
                              let is_empty a l =
                                match l with
                                | [] -> true
                                | uu____11260 -> false  in
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
                                           | uu____11400 -> pat  in
                                         let uu____11401 =
                                           let uu____11412 =
                                             let uu____11423 =
                                               let uu____11432 =
                                                 FStar_Syntax_Syntax.mk
                                                   (FStar_Syntax_Syntax.Tm_meta
                                                      (pat1,
                                                        (FStar_Syntax_Syntax.Meta_desugared
                                                           FStar_Syntax_Syntax.Meta_smt_pat)))
                                                   FStar_Pervasives_Native.None
                                                   pat1.FStar_Syntax_Syntax.pos
                                                  in
                                               (uu____11432, aq)  in
                                             [uu____11423]  in
                                           ens :: uu____11412  in
                                         req :: uu____11401
                                     | uu____11473 -> rest2
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
        | uu____11495 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___128_11512 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___128_11512.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___128_11512.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___129_11546 = b  in
             {
               FStar_Parser_AST.b = (uu___129_11546.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___129_11546.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___129_11546.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____11605 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____11605)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____11618 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____11618 with
             | (env1,a1) ->
                 let a2 =
                   let uu___130_11628 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___130_11628.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___130_11628.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____11650 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____11664 =
                     let uu____11667 =
                       let uu____11668 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____11668]  in
                     no_annot_abs uu____11667 body2  in
                   FStar_All.pipe_left setpos uu____11664  in
                 let uu____11673 =
                   let uu____11674 =
                     let uu____11689 =
                       FStar_Syntax_Syntax.fvar
                         (FStar_Ident.set_lid_range q
                            b.FStar_Parser_AST.brange)
                         (FStar_Syntax_Syntax.Delta_defined_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____11690 =
                       let uu____11693 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____11693]  in
                     (uu____11689, uu____11690)  in
                   FStar_Syntax_Syntax.Tm_app uu____11674  in
                 FStar_All.pipe_left mk1 uu____11673)
        | uu____11698 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____11770 = q (rest, pats, body)  in
              let uu____11777 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____11770 uu____11777
                FStar_Parser_AST.Formula
               in
            let uu____11778 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____11778 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____11787 -> failwith "impossible"  in
      let uu____11790 =
        let uu____11791 = unparen f  in uu____11791.FStar_Parser_AST.tm  in
      match uu____11790 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____11798,uu____11799) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____11810,uu____11811) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____11842 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____11842
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____11878 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____11878
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____11921 -> desugar_term env f

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
      let uu____11926 =
        FStar_List.fold_left
          (fun uu____11962  ->
             fun b  ->
               match uu____11962 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___131_12014 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___131_12014.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___131_12014.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___131_12014.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____12031 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____12031 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___132_12051 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___132_12051.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___132_12051.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____12068 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____11926 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

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
          let uu____12155 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____12155)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____12160 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____12160)
      | FStar_Parser_AST.TVariable x ->
          let uu____12164 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____12164)
      | FStar_Parser_AST.NoName t ->
          let uu____12172 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____12172)
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
               (fun uu___94_12205  ->
                  match uu___94_12205 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____12206 -> false))
           in
        let quals2 q =
          let uu____12217 =
            (let uu____12220 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____12220) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____12217
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____12233 =
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
                  FStar_Syntax_Syntax.sigquals = uu____12233;
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
            let uu____12264 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____12294  ->
                        match uu____12294 with
                        | (x,uu____12302) ->
                            let uu____12303 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____12303 with
                             | (field_name,uu____12311) ->
                                 let only_decl =
                                   ((let uu____12315 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____12315)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____12317 =
                                        let uu____12318 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____12318.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____12317)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____12332 =
                                       FStar_List.filter
                                         (fun uu___95_12336  ->
                                            match uu___95_12336 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____12337 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____12332
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___96_12350  ->
                                             match uu___96_12350 with
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____12351 -> false))
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
                                      let uu____12359 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____12359
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          FStar_Syntax_Syntax.Delta_equational
                                      else
                                        FStar_Syntax_Syntax.Delta_equational
                                       in
                                    let lb =
                                      let uu____12364 =
                                        let uu____12369 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____12369  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____12364;
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
                                      }  in
                                    let impl =
                                      let uu____12373 =
                                        let uu____12374 =
                                          let uu____12381 =
                                            let uu____12384 =
                                              let uu____12385 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____12385
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____12384]  in
                                          ((false, [lb]), uu____12381)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____12374
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____12373;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____12264 FStar_List.flatten
  
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
            (lid,uu____12429,t,uu____12431,n1,uu____12433) when
            Prims.op_Negation
              (FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid)
            ->
            let uu____12438 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____12438 with
             | (formals,uu____12454) ->
                 (match formals with
                  | [] -> []
                  | uu____12477 ->
                      let filter_records uu___97_12489 =
                        match uu___97_12489 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____12492,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____12504 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____12506 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____12506 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Syntax_Syntax.Data_ctor
                        | FStar_Pervasives_Native.Some q -> q  in
                      let iquals1 =
                        if
                          FStar_List.contains FStar_Syntax_Syntax.Abstract
                            iquals
                        then FStar_Syntax_Syntax.Private :: iquals
                        else iquals  in
                      let uu____12516 = FStar_Util.first_N n1 formals  in
                      (match uu____12516 with
                       | (uu____12539,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____12565 -> []
  
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
                    let uu____12615 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____12615
                    then
                      let uu____12618 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____12618
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____12621 =
                      let uu____12626 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____12626  in
                    let uu____12627 =
                      let uu____12630 = FStar_Syntax_Syntax.mk_Total k  in
                      FStar_Syntax_Util.arrow typars uu____12630  in
                    let uu____12633 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____12621;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____12627;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____12633;
                      FStar_Syntax_Syntax.lbattrs = [];
                      FStar_Syntax_Syntax.lbpos = rng
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
          let tycon_id uu___98_12680 =
            match uu___98_12680 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____12682,uu____12683) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____12693,uu____12694,uu____12695) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____12705,uu____12706,uu____12707) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____12737,uu____12738,uu____12739) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____12781) ->
                let uu____12782 =
                  let uu____12783 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____12783  in
                FStar_Parser_AST.mk_term uu____12782 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____12785 =
                  let uu____12786 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____12786  in
                FStar_Parser_AST.mk_term uu____12785 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____12788) ->
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
              | uu____12811 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____12817 =
                     let uu____12818 =
                       let uu____12825 = binder_to_term b  in
                       (out, uu____12825, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____12818  in
                   FStar_Parser_AST.mk_term uu____12817
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___99_12835 =
            match uu___99_12835 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____12890  ->
                       match uu____12890 with
                       | (x,t,uu____12901) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated
                                ((FStar_Syntax_Util.mangle_field_name x), t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____12907 =
                    let uu____12908 =
                      let uu____12909 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____12909  in
                    FStar_Parser_AST.mk_term uu____12908
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____12907 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let uu____12913 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____12940  ->
                          match uu____12940 with
                          | (x,uu____12950,uu____12951) ->
                              FStar_Syntax_Util.unmangle_field_name x))
                   in
                ((FStar_Parser_AST.TyconVariant
                    (id1, parms, kopt,
                      [(constrName, (FStar_Pervasives_Native.Some constrTyp),
                         FStar_Pervasives_Native.None, false)])),
                  uu____12913)
            | uu____13004 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___100_13035 =
            match uu___100_13035 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____13059 = typars_of_binders _env binders  in
                (match uu____13059 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____13105 =
                         let uu____13106 =
                           let uu____13107 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____13107  in
                         FStar_Parser_AST.mk_term uu____13106
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____13105 binders  in
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
            | uu____13120 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____13164 =
              FStar_List.fold_left
                (fun uu____13204  ->
                   fun uu____13205  ->
                     match (uu____13204, uu____13205) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____13296 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____13296 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____13164 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____13409 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____13409
                | uu____13410 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____13418 = desugar_abstract_tc quals env [] tc  in
              (match uu____13418 with
               | (uu____13431,uu____13432,se,uu____13434) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____13437,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____13454 =
                                 let uu____13455 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____13455  in
                               if uu____13454
                               then
                                 let uu____13456 =
                                   let uu____13461 =
                                     let uu____13462 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____13462
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____13461)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____13456
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
                           | uu____13469 ->
                               let uu____13470 =
                                 let uu____13473 =
                                   let uu____13474 =
                                     let uu____13487 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____13487)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____13474
                                    in
                                 FStar_Syntax_Syntax.mk uu____13473  in
                               uu____13470 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___133_13491 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___133_13491.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___133_13491.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___133_13491.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____13494 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____13497 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____13497
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____13512 = typars_of_binders env binders  in
              (match uu____13512 with
               | (env',typars) ->
                   let k =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____13548 =
                           FStar_Util.for_some
                             (fun uu___101_13550  ->
                                match uu___101_13550 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____13551 -> false) quals
                            in
                         if uu____13548
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Util.ktype
                     | FStar_Pervasives_Native.Some k -> desugar_term env' k
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____13558 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___102_13562  ->
                               match uu___102_13562 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____13563 -> false))
                        in
                     if uu____13558
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____13572 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____13572
                     then
                       let uu____13575 =
                         let uu____13582 =
                           let uu____13583 = unparen t  in
                           uu____13583.FStar_Parser_AST.tm  in
                         match uu____13582 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____13604 =
                               match FStar_List.rev args with
                               | (last_arg,uu____13634)::args_rev ->
                                   let uu____13646 =
                                     let uu____13647 = unparen last_arg  in
                                     uu____13647.FStar_Parser_AST.tm  in
                                   (match uu____13646 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____13675 -> ([], args))
                               | uu____13684 -> ([], args)  in
                             (match uu____13604 with
                              | (cattributes,args1) ->
                                  let uu____13723 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____13723))
                         | uu____13734 -> (t, [])  in
                       match uu____13575 with
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
                                  (fun uu___103_13756  ->
                                     match uu___103_13756 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____13757 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____13768)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____13792 = tycon_record_as_variant trec  in
              (match uu____13792 with
               | (t,fs) ->
                   let uu____13809 =
                     let uu____13812 =
                       let uu____13813 =
                         let uu____13822 =
                           let uu____13825 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____13825  in
                         (uu____13822, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____13813  in
                     uu____13812 :: quals  in
                   desugar_tycon env d uu____13809 [t])
          | uu____13830::uu____13831 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____13992 = et  in
                match uu____13992 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____14217 ->
                         let trec = tc  in
                         let uu____14241 = tycon_record_as_variant trec  in
                         (match uu____14241 with
                          | (t,fs) ->
                              let uu____14300 =
                                let uu____14303 =
                                  let uu____14304 =
                                    let uu____14313 =
                                      let uu____14316 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____14316  in
                                    (uu____14313, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____14304
                                   in
                                uu____14303 :: quals1  in
                              collect_tcs uu____14300 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____14403 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____14403 with
                          | (env2,uu____14463,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____14612 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____14612 with
                          | (env2,uu____14672,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____14797 ->
                         failwith "Unrecognized mutual type definition")
                 in
              let uu____14844 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____14844 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___105_15355  ->
                             match uu___105_15355 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____15422,uu____15423);
                                    FStar_Syntax_Syntax.sigrng = uu____15424;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____15425;
                                    FStar_Syntax_Syntax.sigmeta = uu____15426;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____15427;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____15488 =
                                     typars_of_binders env1 binders  in
                                   match uu____15488 with
                                   | (env2,tpars1) ->
                                       let uu____15519 =
                                         push_tparams env2 tpars1  in
                                       (match uu____15519 with
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
                                 let uu____15552 =
                                   let uu____15573 =
                                     mk_typ_abbrev id1 uvs tpars k t1 
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____15573)
                                    in
                                 [uu____15552]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____15641);
                                    FStar_Syntax_Syntax.sigrng = uu____15642;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____15644;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____15645;_},constrs,tconstr,quals1)
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
                                 let uu____15741 = push_tparams env1 tpars
                                    in
                                 (match uu____15741 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____15818  ->
                                             match uu____15818 with
                                             | (x,uu____15832) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____15840 =
                                        let uu____15869 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____15983  ->
                                                  match uu____15983 with
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
                                                        let uu____16039 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____16039
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
                                                                uu___104_16050
                                                                 ->
                                                                match uu___104_16050
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____16062
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____16070 =
                                                        let uu____16091 =
                                                          let uu____16092 =
                                                            let uu____16093 =
                                                              let uu____16108
                                                                =
                                                                let uu____16111
                                                                  =
                                                                  let uu____16114
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____16114
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____16111
                                                                 in
                                                              (name, univs1,
                                                                uu____16108,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____16093
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____16092;
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
                                                          uu____16091)
                                                         in
                                                      (name, uu____16070)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____15869
                                         in
                                      (match uu____15840 with
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
                             | uu____16353 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____16485  ->
                             match uu____16485 with
                             | (name_doc,uu____16513,uu____16514) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____16594  ->
                             match uu____16594 with
                             | (uu____16615,uu____16616,se) -> se))
                      in
                   let uu____16646 =
                     let uu____16653 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____16653 rng
                      in
                   (match uu____16646 with
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
                               (fun uu____16719  ->
                                  match uu____16719 with
                                  | (uu____16742,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____16793,tps,k,uu____16796,constrs)
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
                                  | uu____16815 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____16832  ->
                                 match uu____16832 with
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
      let uu____16867 =
        FStar_List.fold_left
          (fun uu____16890  ->
             fun b  ->
               match uu____16890 with
               | (env1,binders1) ->
                   let uu____16910 = desugar_binder env1 b  in
                   (match uu____16910 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____16927 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____16927 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____16944 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____16867 with
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
          let uu____16989 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___106_16994  ->
                    match uu___106_16994 with
                    | FStar_Syntax_Syntax.Reflectable uu____16995 -> true
                    | uu____16996 -> false))
             in
          if uu____16989
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
                FStar_Parser_AST.term Prims.list ->
                  (FStar_Syntax_DsEnv.env,FStar_Syntax_Syntax.sigelt
                                            Prims.list)
                    FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      fun quals  ->
        fun eff_name  ->
          fun eff_binders  ->
            fun eff_typ  ->
              fun eff_decls  ->
                fun attrs  ->
                  let env0 = env  in
                  let monad_env =
                    FStar_Syntax_DsEnv.enter_monad_scope env eff_name  in
                  let uu____17102 = desugar_binders monad_env eff_binders  in
                  match uu____17102 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let for_free =
                        let uu____17123 =
                          let uu____17124 =
                            let uu____17131 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____17131  in
                          FStar_List.length uu____17124  in
                        uu____17123 = (Prims.parse_int "1")  in
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
                            (uu____17173,(FStar_Parser_AST.TyconAbbrev
                                          (name,uu____17175,uu____17176,uu____17177),uu____17178)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____17211 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____17212 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____17224 = name_of_eff_decl decl  in
                             FStar_List.mem uu____17224 mandatory_members)
                          eff_decls
                         in
                      (match uu____17212 with
                       | (mandatory_members_decls,actions) ->
                           let uu____17241 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____17270  ->
                                     fun decl  ->
                                       match uu____17270 with
                                       | (env2,out) ->
                                           let uu____17290 =
                                             desugar_decl env2 decl  in
                                           (match uu____17290 with
                                            | (env3,ses) ->
                                                let uu____17303 =
                                                  let uu____17306 =
                                                    FStar_List.hd ses  in
                                                  uu____17306 :: out  in
                                                (env3, uu____17303)))
                                  (env1, []))
                              in
                           (match uu____17241 with
                            | (env2,decls) ->
                                let binders1 =
                                  FStar_Syntax_Subst.close_binders binders
                                   in
                                let actions_docs =
                                  FStar_All.pipe_right actions
                                    (FStar_List.map
                                       (fun d1  ->
                                          match d1.FStar_Parser_AST.d with
                                          | FStar_Parser_AST.Tycon
                                              (uu____17374,(FStar_Parser_AST.TyconAbbrev
                                                            (name,action_params,uu____17377,
                                                             {
                                                               FStar_Parser_AST.tm
                                                                 =
                                                                 FStar_Parser_AST.Construct
                                                                 (uu____17378,
                                                                  (def,uu____17380)::
                                                                  (cps_type,uu____17382)::[]);
                                                               FStar_Parser_AST.range
                                                                 =
                                                                 uu____17383;
                                                               FStar_Parser_AST.level
                                                                 =
                                                                 uu____17384;_}),doc1)::[])
                                              when Prims.op_Negation for_free
                                              ->
                                              let uu____17436 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____17436 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____17456 =
                                                     let uu____17457 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____17458 =
                                                       let uu____17459 =
                                                         desugar_term env3
                                                           def
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____17459
                                                        in
                                                     let uu____17464 =
                                                       let uu____17465 =
                                                         desugar_typ env3
                                                           cps_type
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____17465
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____17457;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____17458;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____17464
                                                     }  in
                                                   (uu____17456, doc1))
                                          | FStar_Parser_AST.Tycon
                                              (uu____17472,(FStar_Parser_AST.TyconAbbrev
                                                            (name,action_params,uu____17475,defn),doc1)::[])
                                              when for_free ->
                                              let uu____17510 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____17510 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____17530 =
                                                     let uu____17531 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____17532 =
                                                       let uu____17533 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____17533
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____17531;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____17532;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____17530, doc1))
                                          | uu____17540 ->
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
                                  let uu____17570 =
                                    let uu____17571 =
                                      FStar_Syntax_DsEnv.fail_or env2
                                        (FStar_Syntax_DsEnv.try_lookup_definition
                                           env2) l
                                       in
                                    FStar_All.pipe_left
                                      (FStar_Syntax_Subst.close binders1)
                                      uu____17571
                                     in
                                  ([], uu____17570)  in
                                let mname =
                                  FStar_Syntax_DsEnv.qualify env0 eff_name
                                   in
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
                                      let uu____17588 =
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      ([], uu____17588)  in
                                    let uu____17595 =
                                      let uu____17596 =
                                        let uu____17597 =
                                          let uu____17598 = lookup1 "repr"
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____17598
                                           in
                                        let uu____17607 = lookup1 "return"
                                           in
                                        let uu____17608 = lookup1 "bind"  in
                                        let uu____17609 =
                                          FStar_List.map (desugar_term env2)
                                            attrs
                                           in
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
                                            uu____17597;
                                          FStar_Syntax_Syntax.return_repr =
                                            uu____17607;
                                          FStar_Syntax_Syntax.bind_repr =
                                            uu____17608;
                                          FStar_Syntax_Syntax.actions =
                                            actions1;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            uu____17609
                                        }  in
                                      FStar_Syntax_Syntax.Sig_new_effect_for_free
                                        uu____17596
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____17595;
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
                                         (fun uu___107_17615  ->
                                            match uu___107_17615 with
                                            | FStar_Syntax_Syntax.Reifiable 
                                                -> true
                                            | FStar_Syntax_Syntax.Reflectable
                                                uu____17616 -> true
                                            | uu____17617 -> false)
                                         qualifiers
                                        in
                                     let un_ts =
                                       ([], FStar_Syntax_Syntax.tun)  in
                                     let uu____17627 =
                                       let uu____17628 =
                                         let uu____17629 =
                                           lookup1 "return_wp"  in
                                         let uu____17630 = lookup1 "bind_wp"
                                            in
                                         let uu____17631 =
                                           lookup1 "if_then_else"  in
                                         let uu____17632 = lookup1 "ite_wp"
                                            in
                                         let uu____17633 = lookup1 "stronger"
                                            in
                                         let uu____17634 = lookup1 "close_wp"
                                            in
                                         let uu____17635 = lookup1 "assert_p"
                                            in
                                         let uu____17636 = lookup1 "assume_p"
                                            in
                                         let uu____17637 = lookup1 "null_wp"
                                            in
                                         let uu____17638 = lookup1 "trivial"
                                            in
                                         let uu____17639 =
                                           if rr
                                           then
                                             let uu____17640 = lookup1 "repr"
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.snd
                                               uu____17640
                                           else FStar_Syntax_Syntax.tun  in
                                         let uu____17656 =
                                           if rr
                                           then lookup1 "return"
                                           else un_ts  in
                                         let uu____17658 =
                                           if rr
                                           then lookup1 "bind"
                                           else un_ts  in
                                         let uu____17660 =
                                           FStar_List.map (desugar_term env2)
                                             attrs
                                            in
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
                                             uu____17629;
                                           FStar_Syntax_Syntax.bind_wp =
                                             uu____17630;
                                           FStar_Syntax_Syntax.if_then_else =
                                             uu____17631;
                                           FStar_Syntax_Syntax.ite_wp =
                                             uu____17632;
                                           FStar_Syntax_Syntax.stronger =
                                             uu____17633;
                                           FStar_Syntax_Syntax.close_wp =
                                             uu____17634;
                                           FStar_Syntax_Syntax.assert_p =
                                             uu____17635;
                                           FStar_Syntax_Syntax.assume_p =
                                             uu____17636;
                                           FStar_Syntax_Syntax.null_wp =
                                             uu____17637;
                                           FStar_Syntax_Syntax.trivial =
                                             uu____17638;
                                           FStar_Syntax_Syntax.repr =
                                             uu____17639;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____17656;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____17658;
                                           FStar_Syntax_Syntax.actions =
                                             actions1;
                                           FStar_Syntax_Syntax.eff_attrs =
                                             uu____17660
                                         }  in
                                       FStar_Syntax_Syntax.Sig_new_effect
                                         uu____17628
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         uu____17627;
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
                                          fun uu____17686  ->
                                            match uu____17686 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____17700 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____17700
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
                let uu____17724 = desugar_binders env1 eff_binders  in
                match uu____17724 with
                | (env2,binders) ->
                    let uu____17743 =
                      let uu____17762 = head_and_args defn  in
                      match uu____17762 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____17807 ->
                                let uu____17808 =
                                  let uu____17813 =
                                    let uu____17814 =
                                      let uu____17815 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.strcat uu____17815 " not found"
                                       in
                                    Prims.strcat "Effect " uu____17814  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____17813)
                                   in
                                FStar_Errors.raise_error uu____17808
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____17817 =
                            match FStar_List.rev args with
                            | (last_arg,uu____17847)::args_rev ->
                                let uu____17859 =
                                  let uu____17860 = unparen last_arg  in
                                  uu____17860.FStar_Parser_AST.tm  in
                                (match uu____17859 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____17888 -> ([], args))
                            | uu____17897 -> ([], args)  in
                          (match uu____17817 with
                           | (cattributes,args1) ->
                               let uu____17948 = desugar_args env2 args1  in
                               let uu____17957 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____17948, uu____17957))
                       in
                    (match uu____17743 with
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
                          (let uu____18013 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____18013 with
                           | (ed_binders,uu____18027,ed_binders_opening) ->
                               let sub1 uu____18038 =
                                 match uu____18038 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____18052 =
                                         FStar_Syntax_Subst.shift_subst
                                           (FStar_List.length us)
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____18052 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____18056 =
                                       let uu____18057 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____18057)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____18056
                                  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____18062 =
                                   let uu____18063 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____18063
                                    in
                                 let uu____18074 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____18075 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____18076 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____18077 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____18078 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____18079 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____18080 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____18081 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____18082 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____18083 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____18084 =
                                   let uu____18085 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____18085
                                    in
                                 let uu____18096 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____18097 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____18098 =
                                   FStar_List.map
                                     (fun action  ->
                                        let uu____18106 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____18107 =
                                          let uu____18108 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____18108
                                           in
                                        let uu____18119 =
                                          let uu____18120 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____18120
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____18106;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____18107;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____18119
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
                                     uu____18062;
                                   FStar_Syntax_Syntax.ret_wp = uu____18074;
                                   FStar_Syntax_Syntax.bind_wp = uu____18075;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____18076;
                                   FStar_Syntax_Syntax.ite_wp = uu____18077;
                                   FStar_Syntax_Syntax.stronger = uu____18078;
                                   FStar_Syntax_Syntax.close_wp = uu____18079;
                                   FStar_Syntax_Syntax.assert_p = uu____18080;
                                   FStar_Syntax_Syntax.assume_p = uu____18081;
                                   FStar_Syntax_Syntax.null_wp = uu____18082;
                                   FStar_Syntax_Syntax.trivial = uu____18083;
                                   FStar_Syntax_Syntax.repr = uu____18084;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____18096;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____18097;
                                   FStar_Syntax_Syntax.actions = uu____18098;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____18133 =
                                     let uu____18134 =
                                       let uu____18141 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____18141
                                        in
                                     FStar_List.length uu____18134  in
                                   uu____18133 = (Prims.parse_int "1")  in
                                 let uu____18170 =
                                   let uu____18173 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____18173 quals  in
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
                                   FStar_Syntax_Syntax.sigquals = uu____18170;
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
                                             let uu____18193 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____18193
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____18195 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____18195
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
    let uu____18210 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____18210 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.strcat "  " (Prims.strcat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____18261 ->
              let uu____18262 =
                let uu____18263 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____18263
                 in
              Prims.strcat "\n  " uu____18262
          | uu____18264 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____18277  ->
               match uu____18277 with
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
          let uu____18295 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____18295
            FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____18297 =
          let uu____18306 = FStar_Syntax_Syntax.as_arg arg  in [uu____18306]
           in
        FStar_Syntax_Util.mk_app fv uu____18297

and (desugar_decl :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      let uu____18313 = desugar_decl_noattrs env d  in
      match uu____18313 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____18333 = mk_comment_attr d  in uu____18333 :: attrs1  in
          let s =
            FStar_List.fold_left
              (fun s  ->
                 fun a  ->
                   let uu____18344 =
                     let uu____18345 = FStar_Syntax_Print.term_to_string a
                        in
                     Prims.strcat "; " uu____18345  in
                   Prims.strcat s uu____18344) "" attrs2
             in
          let uu____18346 =
            FStar_List.map
              (fun sigelt  ->
                 let uu___134_18352 = sigelt  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___134_18352.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___134_18352.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___134_18352.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___134_18352.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs = attrs2
                 }) sigelts
             in
          (env1, uu____18346)

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
      | FStar_Parser_AST.Fsdoc uu____18378 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____18394 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____18394, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals  in
          let tcs1 =
            FStar_List.map
              (fun uu____18433  ->
                 match uu____18433 with | (x,uu____18441) -> x) tcs
             in
          let uu____18446 =
            FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals
             in
          desugar_tycon env d uu____18446 tcs1
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals  in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____18468;
                    FStar_Parser_AST.prange = uu____18469;_},uu____18470)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____18479;
                    FStar_Parser_AST.prange = uu____18480;_},uu____18481)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____18496;
                         FStar_Parser_AST.prange = uu____18497;_},uu____18498);
                    FStar_Parser_AST.prange = uu____18499;_},uu____18500)::[]
                   -> false
               | (p,uu____18528)::[] ->
                   let uu____18537 = is_app_pattern p  in
                   Prims.op_Negation uu____18537
               | uu____18538 -> false)
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
            let uu____18612 =
              let uu____18613 =
                FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets  in
              uu____18613.FStar_Syntax_Syntax.n  in
            (match uu____18612 with
             | FStar_Syntax_Syntax.Tm_let (lbs,uu____18621) ->
                 let fvs =
                   FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                     (FStar_List.map
                        (fun lb  ->
                           FStar_Util.right lb.FStar_Syntax_Syntax.lbname))
                    in
                 let quals1 =
                   match quals with
                   | uu____18654::uu____18655 ->
                       FStar_List.map
                         (trans_qual1 FStar_Pervasives_Native.None) quals
                   | uu____18658 ->
                       FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                         (FStar_List.collect
                            (fun uu___108_18673  ->
                               match uu___108_18673 with
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inl uu____18676;
                                   FStar_Syntax_Syntax.lbunivs = uu____18677;
                                   FStar_Syntax_Syntax.lbtyp = uu____18678;
                                   FStar_Syntax_Syntax.lbeff = uu____18679;
                                   FStar_Syntax_Syntax.lbdef = uu____18680;
                                   FStar_Syntax_Syntax.lbattrs = uu____18681;
                                   FStar_Syntax_Syntax.lbpos = uu____18682;_}
                                   -> []
                               | {
                                   FStar_Syntax_Syntax.lbname =
                                     FStar_Util.Inr fv;
                                   FStar_Syntax_Syntax.lbunivs = uu____18694;
                                   FStar_Syntax_Syntax.lbtyp = uu____18695;
                                   FStar_Syntax_Syntax.lbeff = uu____18696;
                                   FStar_Syntax_Syntax.lbdef = uu____18697;
                                   FStar_Syntax_Syntax.lbattrs = uu____18698;
                                   FStar_Syntax_Syntax.lbpos = uu____18699;_}
                                   ->
                                   FStar_Syntax_DsEnv.lookup_letbinding_quals
                                     env
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                    in
                 let quals2 =
                   let uu____18713 =
                     FStar_All.pipe_right lets1
                       (FStar_Util.for_some
                          (fun uu____18744  ->
                             match uu____18744 with
                             | (uu____18757,(uu____18758,t)) ->
                                 t.FStar_Parser_AST.level =
                                   FStar_Parser_AST.Formula))
                      in
                   if uu____18713
                   then FStar_Syntax_Syntax.Logic :: quals1
                   else quals1  in
                 let lbs1 =
                   let uu____18782 =
                     FStar_All.pipe_right quals2
                       (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                      in
                   if uu____18782
                   then
                     let uu____18791 =
                       FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                         (FStar_List.map
                            (fun lb  ->
                               let fv =
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               let uu___135_18805 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname =
                                   (FStar_Util.Inr
                                      (let uu___136_18807 = fv  in
                                       {
                                         FStar_Syntax_Syntax.fv_name =
                                           (uu___136_18807.FStar_Syntax_Syntax.fv_name);
                                         FStar_Syntax_Syntax.fv_delta =
                                           (FStar_Syntax_Syntax.Delta_abstract
                                              (fv.FStar_Syntax_Syntax.fv_delta));
                                         FStar_Syntax_Syntax.fv_qual =
                                           (uu___136_18807.FStar_Syntax_Syntax.fv_qual)
                                       }));
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___135_18805.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (uu___135_18805.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___135_18805.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef =
                                   (uu___135_18805.FStar_Syntax_Syntax.lbdef);
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___135_18805.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___135_18805.FStar_Syntax_Syntax.lbpos)
                               }))
                        in
                     ((FStar_Pervasives_Native.fst lbs), uu____18791)
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
             | uu____18842 ->
                 failwith "Desugaring a let did not produce a let")
          else
            (let uu____18848 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____18867 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____18848 with
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
                       let uu___137_18903 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___137_18903.FStar_Parser_AST.prange)
                       }
                   | uu____18910 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___138_18917 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___138_18917.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___138_18917.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___138_18917.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____18949 id1 =
                   match uu____18949 with
                   | (env1,ses) ->
                       let main =
                         let uu____18970 =
                           let uu____18971 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____18971  in
                         FStar_Parser_AST.mk_term uu____18970
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
                       let uu____19021 = desugar_decl env1 id_decl  in
                       (match uu____19021 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____19039 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____19039 FStar_Util.set_elements
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
            let uu____19070 = close_fun env t  in
            desugar_term env uu____19070  in
          let quals1 =
            let uu____19074 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____19074
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let se =
            let uu____19080 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____19080;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in
          let env2 =
            FStar_Syntax_DsEnv.push_doc env1 lid d.FStar_Parser_AST.doc  in
          (env2, [se])
      | FStar_Parser_AST.Exception (id1,FStar_Pervasives_Native.None ) ->
          let uu____19092 =
            FStar_Syntax_DsEnv.fail_or env
              (FStar_Syntax_DsEnv.try_lookup_lid env)
              FStar_Parser_Const.exn_lid
             in
          (match uu____19092 with
           | (t,uu____19106) ->
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
            let uu____19140 =
              let uu____19147 = FStar_Syntax_Syntax.null_binder t  in
              [uu____19147]  in
            let uu____19148 =
              let uu____19151 =
                let uu____19152 =
                  FStar_Syntax_DsEnv.fail_or env
                    (FStar_Syntax_DsEnv.try_lookup_lid env)
                    FStar_Parser_Const.exn_lid
                   in
                FStar_Pervasives_Native.fst uu____19152  in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____19151
               in
            FStar_Syntax_Util.arrow uu____19140 uu____19148  in
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
          let attrs = d.FStar_Parser_AST.attrs  in
          desugar_effect env d quals eff_name eff_binders eff_typ eff_decls
            attrs
      | FStar_Parser_AST.SubEffect l ->
          let lookup1 l1 =
            let uu____19215 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____19215 with
            | FStar_Pervasives_Native.None  ->
                let uu____19218 =
                  let uu____19223 =
                    let uu____19224 =
                      let uu____19225 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.strcat uu____19225 " not found"  in
                    Prims.strcat "Effect name " uu____19224  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____19223)  in
                FStar_Errors.raise_error uu____19218
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____19229 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____19271 =
                  let uu____19280 =
                    let uu____19287 = desugar_term env t  in
                    ([], uu____19287)  in
                  FStar_Pervasives_Native.Some uu____19280  in
                (uu____19271, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____19320 =
                  let uu____19329 =
                    let uu____19336 = desugar_term env wp  in
                    ([], uu____19336)  in
                  FStar_Pervasives_Native.Some uu____19329  in
                let uu____19345 =
                  let uu____19354 =
                    let uu____19361 = desugar_term env t  in
                    ([], uu____19361)  in
                  FStar_Pervasives_Native.Some uu____19354  in
                (uu____19320, uu____19345)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____19387 =
                  let uu____19396 =
                    let uu____19403 = desugar_term env t  in
                    ([], uu____19403)  in
                  FStar_Pervasives_Native.Some uu____19396  in
                (FStar_Pervasives_Native.None, uu____19387)
             in
          (match uu____19229 with
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
      | FStar_Parser_AST.Splice t ->
          let t1 = desugar_term env t  in
          let se =
            {
              FStar_Syntax_Syntax.sigel = (FStar_Syntax_Syntax.Sig_splice t1);
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = [];
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          (env, [se])

let (desugar_decls :
  env_t ->
    FStar_Parser_AST.decl Prims.list ->
      (env_t,FStar_Syntax_Syntax.sigelt Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun decls  ->
      let uu____19496 =
        FStar_List.fold_left
          (fun uu____19516  ->
             fun d  ->
               match uu____19516 with
               | (env1,sigelts) ->
                   let uu____19536 = desugar_decl env1 d  in
                   (match uu____19536 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____19496 with
      | (env1,sigelts) ->
          let rec forward acc uu___110_19577 =
            match uu___110_19577 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____19591,FStar_Syntax_Syntax.Sig_let uu____19592) ->
                     let uu____19605 =
                       let uu____19608 =
                         let uu___139_19609 = se2  in
                         let uu____19610 =
                           let uu____19613 =
                             FStar_List.filter
                               (fun uu___109_19627  ->
                                  match uu___109_19627 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____19631;
                                           FStar_Syntax_Syntax.vars =
                                             uu____19632;_},uu____19633);
                                      FStar_Syntax_Syntax.pos = uu____19634;
                                      FStar_Syntax_Syntax.vars = uu____19635;_}
                                      when
                                      let uu____19658 =
                                        let uu____19659 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____19659
                                         in
                                      uu____19658 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____19660 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____19613
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___139_19609.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___139_19609.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___139_19609.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___139_19609.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____19610
                         }  in
                       uu____19608 :: se1 :: acc  in
                     forward uu____19605 sigelts1
                 | uu____19665 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____19673 = forward [] sigelts  in (env1, uu____19673)
  
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
          | (FStar_Pervasives_Native.None ,uu____19724) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____19728;
               FStar_Syntax_Syntax.exports = uu____19729;
               FStar_Syntax_Syntax.is_interface = uu____19730;_},FStar_Parser_AST.Module
             (current_lid,uu____19732)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____19740) ->
              let uu____19743 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____19743
           in
        let uu____19748 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____19784 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____19784, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____19801 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____19801, mname, decls, false)
           in
        match uu____19748 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____19831 = desugar_decls env2 decls  in
            (match uu____19831 with
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
          let uu____19885 =
            (FStar_Options.interactive ()) &&
              (let uu____19887 =
                 let uu____19888 =
                   let uu____19889 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____19889  in
                 FStar_Util.get_file_extension uu____19888  in
               FStar_List.mem uu____19887 ["fsti"; "fsi"])
             in
          if uu____19885 then as_interface m else m  in
        let uu____19893 = desugar_modul_common curmod env m1  in
        match uu____19893 with
        | (x,y,pop_when_done) ->
            (if pop_when_done
             then (let uu____19908 = FStar_Syntax_DsEnv.pop ()  in ())
             else ();
             (x, y))
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul ->
      (env_t,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun m  ->
      let uu____19924 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____19924 with
      | (env1,modul,pop_when_done) ->
          let uu____19938 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____19938 with
           | (env2,modul1) ->
               ((let uu____19950 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____19950
                 then
                   let uu____19951 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____19951
                 else ());
                (let uu____19953 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____19953, modul1))))
  
let (ast_modul_to_modul :
  FStar_Parser_AST.modul ->
    FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun env  ->
      let uu____19967 = desugar_modul env modul  in
      match uu____19967 with | (env1,modul1) -> (modul1, env1)
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      let uu____19994 = desugar_decls env decls  in
      match uu____19994 with | (env1,sigelts) -> (sigelts, env1)
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        let uu____20032 = desugar_partial_modul modul env a_modul  in
        match uu____20032 with | (env1,modul1) -> (modul1, env1)
  
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
              | uu____20106 ->
                  let t =
                    let uu____20114 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____20114  in
                  let uu____20123 =
                    let uu____20124 = FStar_Syntax_Subst.compress t  in
                    uu____20124.FStar_Syntax_Syntax.n  in
                  (match uu____20123 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____20134,uu____20135)
                       -> bs1
                   | uu____20156 -> failwith "Impossible")
               in
            let uu____20163 =
              let uu____20170 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____20170
                FStar_Syntax_Syntax.t_unit
               in
            match uu____20163 with
            | (binders,uu____20172,binders_opening) ->
                let erase_term t =
                  let uu____20178 =
                    let uu____20179 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____20179  in
                  FStar_Syntax_Subst.close binders uu____20178  in
                let erase_tscheme uu____20195 =
                  match uu____20195 with
                  | (us,t) ->
                      let t1 =
                        let uu____20215 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____20215 t  in
                      let uu____20218 =
                        let uu____20219 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____20219  in
                      ([], uu____20218)
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
                    | uu____20248 ->
                        let bs =
                          let uu____20256 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____20256  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____20286 =
                          let uu____20287 =
                            let uu____20290 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____20290  in
                          uu____20287.FStar_Syntax_Syntax.n  in
                        (match uu____20286 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____20298,uu____20299) -> bs1
                         | uu____20320 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____20331 =
                      let uu____20332 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____20332  in
                    FStar_Syntax_Subst.close binders uu____20331  in
                  let uu___140_20333 = action  in
                  let uu____20334 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____20335 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___140_20333.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___140_20333.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____20334;
                    FStar_Syntax_Syntax.action_typ = uu____20335
                  }  in
                let uu___141_20336 = ed  in
                let uu____20337 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____20338 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____20339 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____20340 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____20341 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____20342 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____20343 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____20344 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____20345 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____20346 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____20347 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____20348 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____20349 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____20350 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____20351 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____20352 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___141_20336.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___141_20336.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____20337;
                  FStar_Syntax_Syntax.signature = uu____20338;
                  FStar_Syntax_Syntax.ret_wp = uu____20339;
                  FStar_Syntax_Syntax.bind_wp = uu____20340;
                  FStar_Syntax_Syntax.if_then_else = uu____20341;
                  FStar_Syntax_Syntax.ite_wp = uu____20342;
                  FStar_Syntax_Syntax.stronger = uu____20343;
                  FStar_Syntax_Syntax.close_wp = uu____20344;
                  FStar_Syntax_Syntax.assert_p = uu____20345;
                  FStar_Syntax_Syntax.assume_p = uu____20346;
                  FStar_Syntax_Syntax.null_wp = uu____20347;
                  FStar_Syntax_Syntax.trivial = uu____20348;
                  FStar_Syntax_Syntax.repr = uu____20349;
                  FStar_Syntax_Syntax.return_repr = uu____20350;
                  FStar_Syntax_Syntax.bind_repr = uu____20351;
                  FStar_Syntax_Syntax.actions = uu____20352;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___141_20336.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___142_20364 = se  in
                  let uu____20365 =
                    let uu____20366 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____20366  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____20365;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___142_20364.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___142_20364.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___142_20364.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___142_20364.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___143_20370 = se  in
                  let uu____20371 =
                    let uu____20372 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____20372
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____20371;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___143_20370.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___143_20370.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___143_20370.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___143_20370.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____20374 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____20375 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____20375 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____20387 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____20387
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____20389 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____20389)
  