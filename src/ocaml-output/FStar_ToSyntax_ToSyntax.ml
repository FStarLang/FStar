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
  
let (check_no_aq : FStar_Syntax_Syntax.antiquotations -> Prims.unit) =
  fun aq  ->
    match aq with
    | [] -> ()
    | (bv,b,e)::uu____2285 ->
        let uu____2308 =
          let uu____2313 =
            let uu____2314 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format2 "Unexpected antiquotation: %s(%s)"
              (if b then "`@" else "`#") uu____2314
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____2313)  in
        FStar_Errors.raise_error uu____2308 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'Auu____2320 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident,'Auu____2320) FStar_Pervasives_Native.tuple2
        Prims.list -> FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____2345 = FStar_List.hd fields  in
        match uu____2345 with
        | (f,uu____2355) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____2365 =
                match uu____2365 with
                | (f',uu____2371) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____2373 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____2373
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
              (let uu____2377 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____2377);
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
            | FStar_Syntax_Syntax.Pat_dot_term uu____2626 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_wild uu____2633 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_constant uu____2634 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_var x ->
                FStar_Util.set_add x FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_cons (uu____2636,pats1) ->
                let aux out uu____2670 =
                  match uu____2670 with
                  | (p2,uu____2682) ->
                      let intersection =
                        let uu____2690 = pat_vars p2  in
                        FStar_Util.set_intersect uu____2690 out  in
                      let uu____2693 = FStar_Util.set_is_empty intersection
                         in
                      if uu____2693
                      then
                        let uu____2696 = pat_vars p2  in
                        FStar_Util.set_union out uu____2696
                      else
                        (let duplicate_bv =
                           let uu____2701 =
                             FStar_Util.set_elements intersection  in
                           FStar_List.hd uu____2701  in
                         let uu____2704 =
                           let uu____2709 =
                             FStar_Util.format1
                               "Non-linear patterns are not permitted. %s appears more than once in this pattern."
                               (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                              in
                           (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                             uu____2709)
                            in
                         FStar_Errors.raise_error uu____2704 r)
                   in
                FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
             in
          match pats with
          | [] -> ()
          | p1::[] ->
              let uu____2729 = pat_vars p1  in
              FStar_All.pipe_right uu____2729 FStar_Pervasives.ignore
          | p1::ps ->
              let pvars = pat_vars p1  in
              let aux p2 =
                let uu____2749 =
                  let uu____2750 = pat_vars p2  in
                  FStar_Util.set_eq pvars uu____2750  in
                if uu____2749
                then ()
                else
                  (let nonlinear_vars =
                     let uu____2757 = pat_vars p2  in
                     FStar_Util.set_symmetric_difference pvars uu____2757  in
                   let first_nonlinear_var =
                     let uu____2761 = FStar_Util.set_elements nonlinear_vars
                        in
                     FStar_List.hd uu____2761  in
                   let uu____2764 =
                     let uu____2769 =
                       FStar_Util.format1
                         "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                         (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                        in
                     (FStar_Errors.Fatal_IncoherentPatterns, uu____2769)  in
                   FStar_Errors.raise_error uu____2764 r)
                 in
              FStar_List.iter aux ps
           in
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false ,uu____2773) -> ()
         | (true ,FStar_Parser_AST.PatVar uu____2774) -> ()
         | (true ,uu____2781) ->
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_LetMutableForVariablesOnly,
                 "let-mutable is for variables only")
               p.FStar_Parser_AST.prange);
        (let push_bv_maybe_mut =
           if is_mut
           then FStar_Syntax_DsEnv.push_bv_mutable
           else FStar_Syntax_DsEnv.push_bv  in
         let resolvex l e x =
           let uu____2816 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText))
              in
           match uu____2816 with
           | FStar_Pervasives_Native.Some y -> (l, e, y)
           | uu____2830 ->
               let uu____2833 = push_bv_maybe_mut e x  in
               (match uu____2833 with | (e1,x1) -> ((x1 :: l), e1, x1))
            in
         let rec aux' top loc env1 p1 =
           let pos q =
             FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange  in
           let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
           let orig = p1  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr uu____2920 -> failwith "impossible"
           | FStar_Parser_AST.PatOp op ->
               let uu____2936 =
                 let uu____2937 =
                   let uu____2938 =
                     let uu____2945 =
                       let uu____2946 =
                         let uu____2951 =
                           FStar_Parser_AST.compile_op (Prims.parse_int "0")
                             op.FStar_Ident.idText op.FStar_Ident.idRange
                            in
                         (uu____2951, (op.FStar_Ident.idRange))  in
                       FStar_Ident.mk_ident uu____2946  in
                     (uu____2945, FStar_Pervasives_Native.None)  in
                   FStar_Parser_AST.PatVar uu____2938  in
                 {
                   FStar_Parser_AST.pat = uu____2937;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 }  in
               aux loc env1 uu____2936
           | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
               ((match tacopt with
                 | FStar_Pervasives_Native.None  -> ()
                 | FStar_Pervasives_Native.Some uu____2968 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                         "Type ascriptions within patterns are cannot be associated with a tactic")
                       orig.FStar_Parser_AST.prange);
                (let uu____2969 = aux loc env1 p2  in
                 match uu____2969 with
                 | (loc1,env',binder,p3,imp) ->
                     let annot_pat_var p4 t1 =
                       match p4.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let uu___112_3023 = p4  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var
                                  (let uu___113_3028 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___113_3028.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___113_3028.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }));
                             FStar_Syntax_Syntax.p =
                               (uu___112_3023.FStar_Syntax_Syntax.p)
                           }
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let uu___114_3030 = p4  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild
                                  (let uu___115_3035 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___115_3035.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___115_3035.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }));
                             FStar_Syntax_Syntax.p =
                               (uu___114_3030.FStar_Syntax_Syntax.p)
                           }
                       | uu____3036 when top -> p4
                       | uu____3037 ->
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                               "Type ascriptions within patterns are only allowed on variables")
                             orig.FStar_Parser_AST.prange
                        in
                     let uu____3040 =
                       match binder with
                       | LetBinder uu____3053 -> failwith "impossible"
                       | LocalBinder (x,aq) ->
                           let t1 =
                             let uu____3073 = close_fun env1 t  in
                             desugar_term env1 uu____3073  in
                           (if
                              (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                               with
                               | FStar_Syntax_Syntax.Tm_unknown  -> false
                               | uu____3075 -> true)
                            then
                              (let uu____3076 =
                                 let uu____3081 =
                                   let uu____3082 =
                                     FStar_Syntax_Print.bv_to_string x  in
                                   let uu____3083 =
                                     FStar_Syntax_Print.term_to_string
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____3084 =
                                     FStar_Syntax_Print.term_to_string t1  in
                                   FStar_Util.format3
                                     "Multiple ascriptions for %s in pattern, type %s was shadowed by %s\n"
                                     uu____3082 uu____3083 uu____3084
                                    in
                                 (FStar_Errors.Warning_MultipleAscriptions,
                                   uu____3081)
                                  in
                               FStar_Errors.log_issue
                                 orig.FStar_Parser_AST.prange uu____3076)
                            else ();
                            (let uu____3086 = annot_pat_var p3 t1  in
                             (uu____3086,
                               (LocalBinder
                                  ((let uu___116_3092 = x  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___116_3092.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___116_3092.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    }), aq)))))
                        in
                     (match uu____3040 with
                      | (p4,binder1) -> (loc1, env', binder1, p4, imp))))
           | FStar_Parser_AST.PatWild  ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____3114 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____3114, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____3125 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____3125, false)
           | FStar_Parser_AST.PatTvar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual aq  in
               let uu____3146 = resolvex loc env1 x  in
               (match uu____3146 with
                | (loc1,env2,xbv) ->
                    let uu____3168 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____3168, imp))
           | FStar_Parser_AST.PatVar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual aq  in
               let uu____3189 = resolvex loc env1 x  in
               (match uu____3189 with
                | (loc1,env2,xbv) ->
                    let uu____3211 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____3211, imp))
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
               let uu____3223 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, []))
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____3223, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____3247;_},args)
               ->
               let uu____3253 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____3294  ->
                        match uu____3294 with
                        | (loc1,env2,args1) ->
                            let uu____3342 = aux loc1 env2 arg  in
                            (match uu____3342 with
                             | (loc2,env3,uu____3371,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, [])
                  in
               (match uu____3253 with
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
                    let uu____3441 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                       in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)),
                      uu____3441, false))
           | FStar_Parser_AST.PatApp uu____3458 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                 p1.FStar_Parser_AST.prange
           | FStar_Parser_AST.PatList pats ->
               let uu____3480 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____3513  ->
                        match uu____3513 with
                        | (loc1,env2,pats1) ->
                            let uu____3545 = aux loc1 env2 pat  in
                            (match uu____3545 with
                             | (loc2,env3,uu____3570,pat1,uu____3572) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, [])
                  in
               (match uu____3480 with
                | (loc1,env2,pats1) ->
                    let pat =
                      let uu____3615 =
                        let uu____3618 =
                          let uu____3623 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange
                             in
                          pos_r uu____3623  in
                        let uu____3624 =
                          let uu____3625 =
                            let uu____3638 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Parser_Const.nil_lid
                                FStar_Syntax_Syntax.Delta_constant
                                (FStar_Pervasives_Native.Some
                                   FStar_Syntax_Syntax.Data_ctor)
                               in
                            (uu____3638, [])  in
                          FStar_Syntax_Syntax.Pat_cons uu____3625  in
                        FStar_All.pipe_left uu____3618 uu____3624  in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p
                                in
                             let uu____3670 =
                               let uu____3671 =
                                 let uu____3684 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.cons_lid
                                     FStar_Syntax_Syntax.Delta_constant
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Data_ctor)
                                    in
                                 (uu____3684, [(hd1, false); (tl1, false)])
                                  in
                               FStar_Syntax_Syntax.Pat_cons uu____3671  in
                             FStar_All.pipe_left (pos_r r) uu____3670) pats1
                        uu____3615
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
               let uu____3728 =
                 FStar_List.fold_left
                   (fun uu____3768  ->
                      fun p2  ->
                        match uu____3768 with
                        | (loc1,env2,pats) ->
                            let uu____3817 = aux loc1 env2 p2  in
                            (match uu____3817 with
                             | (loc2,env3,uu____3846,pat,uu____3848) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args
                  in
               (match uu____3728 with
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
                    let uu____3943 =
                      FStar_Syntax_DsEnv.fail_or env2
                        (FStar_Syntax_DsEnv.try_lookup_lid env2) l
                       in
                    (match uu____3943 with
                     | (constr,uu____3965) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____3968 -> failwith "impossible"  in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (FStar_Pervasives_Native.Some
                                (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun
                            in
                         let uu____3970 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                            in
                         (loc1, env2,
                           (LocalBinder (x, FStar_Pervasives_Native.None)),
                           uu____3970, false)))
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
                      (fun uu____4041  ->
                         match uu____4041 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2)))
                  in
               let args =
                 FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                   (FStar_List.map
                      (fun uu____4071  ->
                         match uu____4071 with
                         | (f,uu____4077) ->
                             let uu____4078 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____4104  ->
                                       match uu____4104 with
                                       | (g,uu____4110) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText))
                                in
                             (match uu____4078 with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
                              | FStar_Pervasives_Native.Some (uu____4115,p2)
                                  -> p2)))
                  in
               let app =
                 let uu____4122 =
                   let uu____4123 =
                     let uu____4130 =
                       let uu____4131 =
                         let uu____4132 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                                [record.FStar_Syntax_DsEnv.constrname])
                            in
                         FStar_Parser_AST.PatName uu____4132  in
                       FStar_Parser_AST.mk_pattern uu____4131
                         p1.FStar_Parser_AST.prange
                        in
                     (uu____4130, args)  in
                   FStar_Parser_AST.PatApp uu____4123  in
                 FStar_Parser_AST.mk_pattern uu____4122
                   p1.FStar_Parser_AST.prange
                  in
               let uu____4135 = aux loc env1 app  in
               (match uu____4135 with
                | (env2,e,b,p2,uu____4164) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____4192 =
                            let uu____4193 =
                              let uu____4206 =
                                let uu___117_4207 = fv  in
                                let uu____4208 =
                                  let uu____4211 =
                                    let uu____4212 =
                                      let uu____4219 =
                                        FStar_All.pipe_right
                                          record.FStar_Syntax_DsEnv.fields
                                          (FStar_List.map
                                             FStar_Pervasives_Native.fst)
                                         in
                                      ((record.FStar_Syntax_DsEnv.typename),
                                        uu____4219)
                                       in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____4212
                                     in
                                  FStar_Pervasives_Native.Some uu____4211  in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___117_4207.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___117_4207.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____4208
                                }  in
                              (uu____4206, args1)  in
                            FStar_Syntax_Syntax.Pat_cons uu____4193  in
                          FStar_All.pipe_left pos uu____4192
                      | uu____4246 -> p2  in
                    (env2, e, b, p3, false))
         
         and aux loc env1 p1 = aux' false loc env1 p1
          in
         let aux_maybe_or env1 p1 =
           let loc = []  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____4296 = aux' true loc env1 p2  in
               (match uu____4296 with
                | (loc1,env2,var,p3,uu____4323) ->
                    let uu____4328 =
                      FStar_List.fold_left
                        (fun uu____4360  ->
                           fun p4  ->
                             match uu____4360 with
                             | (loc2,env3,ps1) ->
                                 let uu____4393 = aux' true loc2 env3 p4  in
                                 (match uu____4393 with
                                  | (loc3,env4,uu____4418,p5,uu____4420) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps
                       in
                    (match uu____4328 with
                     | (loc2,env3,ps1) ->
                         let pats = p3 :: (FStar_List.rev ps1)  in
                         (env3, var, pats)))
           | uu____4471 ->
               let uu____4472 = aux' true loc env1 p1  in
               (match uu____4472 with
                | (loc1,env2,vars,pat,b) -> (env2, vars, [pat]))
            in
         let uu____4512 = aux_maybe_or env p  in
         match uu____4512 with
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
            let uu____4571 =
              let uu____4572 =
                let uu____4583 = FStar_Syntax_DsEnv.qualify env x  in
                (uu____4583,
                  (FStar_Syntax_Syntax.tun, FStar_Pervasives_Native.None))
                 in
              LetBinder uu____4572  in
            (env, uu____4571, [])  in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____4611 =
                  let uu____4612 =
                    let uu____4617 =
                      FStar_Parser_AST.compile_op (Prims.parse_int "0")
                        x.FStar_Ident.idText x.FStar_Ident.idRange
                       in
                    (uu____4617, (x.FStar_Ident.idRange))  in
                  FStar_Ident.mk_ident uu____4612  in
                mklet uu____4611
            | FStar_Parser_AST.PatVar (x,uu____4619) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____4625);
                   FStar_Parser_AST.prange = uu____4626;_},(t,tacopt))
                ->
                let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)
                   in
                let uu____4646 =
                  let uu____4647 =
                    let uu____4658 = FStar_Syntax_DsEnv.qualify env x  in
                    let uu____4659 =
                      let uu____4666 = desugar_term env t  in
                      (uu____4666, tacopt1)  in
                    (uu____4658, uu____4659)  in
                  LetBinder uu____4647  in
                (env, uu____4646, [])
            | uu____4677 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_UnexpectedPattern,
                    "Unexpected pattern at the top-level")
                  p.FStar_Parser_AST.prange
          else
            (let uu____4687 = desugar_data_pat env p is_mut  in
             match uu____4687 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1 with
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                         uu____4716;
                       FStar_Syntax_Syntax.p = uu____4717;_}::[] -> []
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                         uu____4722;
                       FStar_Syntax_Syntax.p = uu____4723;_}::[] -> []
                   | uu____4728 -> p1  in
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
  fun uu____4735  ->
    fun env  ->
      fun pat  ->
        let uu____4738 = desugar_data_pat env pat false  in
        match uu____4738 with | (env1,uu____4754,pat1) -> (env1, pat1)

and (desugar_match_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern ->
      (env_t,FStar_Syntax_Syntax.pat Prims.list)
        FStar_Pervasives_Native.tuple2)
  = fun env  -> fun p  -> desugar_match_pat_maybe_top false env p

and (desugar_term_aq :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.antiquotations)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun e  ->
      let env1 = FStar_Syntax_DsEnv.set_expect_typ env false  in
      desugar_term_maybe_top false env1 e

and (desugar_term :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let uu____4773 = desugar_term_aq env e  in
      match uu____4773 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_typ_aq :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.antiquotations)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun e  ->
      let env1 = FStar_Syntax_DsEnv.set_expect_typ env true  in
      desugar_term_maybe_top false env1 e

and (desugar_typ :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let uu____4790 = desugar_typ_aq env e  in
      match uu____4790 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness,FStar_Const.width)
        FStar_Pervasives_Native.tuple2 ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____4800  ->
        fun range  ->
          match uu____4800 with
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
              ((let uu____4810 =
                  let uu____4811 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____4811  in
                if uu____4810
                then
                  let uu____4812 =
                    let uu____4817 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____4817)  in
                  FStar_Errors.log_issue range uu____4812
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
                  let uu____4825 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____4825 with
                  | FStar_Pervasives_Native.Some (intro_term,uu____4835) ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             FStar_Ident.lid_of_path
                               (FStar_Ident.path_of_text private_intro_nm)
                               range
                              in
                           let private_fv =
                             let uu____4845 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____4845 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___118_4846 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___118_4846.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___118_4846.FStar_Syntax_Syntax.vars)
                           }
                       | uu____4847 ->
                           failwith
                             (Prims.strcat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____4854 =
                        let uu____4859 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____4859)
                         in
                      FStar_Errors.raise_error uu____4854 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____4875 =
                  let uu____4878 =
                    let uu____4879 =
                      let uu____4894 =
                        let uu____4903 =
                          let uu____4910 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____4910)  in
                        [uu____4903]  in
                      (lid1, uu____4894)  in
                    FStar_Syntax_Syntax.Tm_app uu____4879  in
                  FStar_Syntax_Syntax.mk uu____4878  in
                uu____4875 FStar_Pervasives_Native.None range))

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
            let uu____4949 =
              FStar_Syntax_DsEnv.fail_or env
                ((if resolve
                  then FStar_Syntax_DsEnv.try_lookup_lid_with_attributes
                  else
                    FStar_Syntax_DsEnv.try_lookup_lid_with_attributes_no_resolve)
                   env) l
               in
            match uu____4949 with
            | (tm,mut,attrs) ->
                let warn_if_deprecated attrs1 =
                  FStar_List.iter
                    (fun a  ->
                       match a.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_app
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____4995;
                              FStar_Syntax_Syntax.vars = uu____4996;_},args)
                           when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____5019 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____5019 " is deprecated"  in
                           let msg1 =
                             if
                               (FStar_List.length args) >
                                 (Prims.parse_int "0")
                             then
                               let uu____5027 =
                                 let uu____5028 =
                                   let uu____5031 = FStar_List.hd args  in
                                   FStar_Pervasives_Native.fst uu____5031  in
                                 uu____5028.FStar_Syntax_Syntax.n  in
                               match uu____5027 with
                               | FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_string (s,uu____5047))
                                   when
                                   Prims.op_Negation
                                     ((FStar_Util.trim_string s) = "")
                                   ->
                                   Prims.strcat msg
                                     (Prims.strcat ", use "
                                        (Prims.strcat s " instead"))
                               | uu____5048 -> msg
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
                             let uu____5052 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____5052 " is deprecated"  in
                           FStar_Errors.log_issue
                             (FStar_Ident.range_of_lid l)
                             (FStar_Errors.Warning_DeprecatedDefinition, msg)
                       | uu____5053 -> ()) attrs1
                   in
                (warn_if_deprecated attrs;
                 (let tm1 = setpos tm  in
                  if mut
                  then
                    let uu____5058 =
                      let uu____5059 =
                        let uu____5066 = mk_ref_read tm1  in
                        (uu____5066,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Mutable_rval))
                         in
                      FStar_Syntax_Syntax.Tm_meta uu____5059  in
                    FStar_All.pipe_left mk1 uu____5058
                  else tm1))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____5082 =
          let uu____5083 = unparen t  in uu____5083.FStar_Parser_AST.tm  in
        match uu____5082 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____5084; FStar_Ident.ident = uu____5085;
              FStar_Ident.nsstr = uu____5086; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____5089 ->
            let uu____5090 =
              let uu____5095 =
                let uu____5096 = FStar_Parser_AST.term_to_string t  in
                Prims.strcat "Unknown attribute " uu____5096  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____5095)  in
            FStar_Errors.raise_error uu____5090 t.FStar_Parser_AST.range
         in
      FStar_List.map desugar_attribute cattributes

and (desugar_term_maybe_top :
  Prims.bool ->
    env_t ->
      FStar_Parser_AST.term ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.antiquotations)
          FStar_Pervasives_Native.tuple2)
  =
  fun top_level  ->
    fun env  ->
      fun top  ->
        let mk1 e =
          FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
            top.FStar_Parser_AST.range
           in
        let noaqs = []  in
        let join_aqs aqs = FStar_List.flatten aqs  in
        let setpos e =
          let uu___119_5185 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___119_5185.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___119_5185.FStar_Syntax_Syntax.vars)
          }  in
        let uu____5188 =
          let uu____5189 = unparen top  in uu____5189.FStar_Parser_AST.tm  in
        match uu____5188 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____5206 ->
            let uu____5213 = desugar_formula env top  in (uu____5213, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____5230 = desugar_formula env t  in (uu____5230, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____5247 = desugar_formula env t  in (uu____5247, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____5281 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____5281, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____5293 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____5293, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Op ((FStar_Ident.mk_ident ("==", r)), args))
                top.FStar_Parser_AST.range top.FStar_Parser_AST.level
               in
            desugar_term_aq env
              (FStar_Parser_AST.mk_term
                 (FStar_Parser_AST.Op ((FStar_Ident.mk_ident ("~", r)), [e]))
                 top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
        | FStar_Parser_AST.Op (op_star,uu____5320::uu____5321::[]) when
            ((FStar_Ident.text_of_id op_star) = "*") &&
              (let uu____5325 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____5325 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____5338;_},t1::t2::[])
                  ->
                  let uu____5343 = flatten1 t1  in
                  FStar_List.append uu____5343 [t2]
              | uu____5346 -> [t]  in
            let uu____5347 =
              let uu____5356 =
                let uu____5363 =
                  let uu____5366 = unparen top  in flatten1 uu____5366  in
                FStar_All.pipe_right uu____5363
                  (FStar_List.map
                     (fun t  ->
                        let uu____5385 = desugar_typ_aq env t  in
                        match uu____5385 with
                        | (t',aq) ->
                            let uu____5396 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____5396, aq)))
                 in
              FStar_All.pipe_right uu____5356 FStar_List.unzip  in
            (match uu____5347 with
             | (targs,aqs) ->
                 let uu____5425 =
                   let uu____5430 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____5430
                    in
                 (match uu____5425 with
                  | (tup,uu____5440) ->
                      let uu____5441 =
                        mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                      (uu____5441, (join_aqs aqs))))
        | FStar_Parser_AST.Tvar a ->
            let uu____5459 =
              let uu____5462 =
                let uu____5465 =
                  FStar_Syntax_DsEnv.fail_or2
                    (FStar_Syntax_DsEnv.try_lookup_id env) a
                   in
                FStar_Pervasives_Native.fst uu____5465  in
              FStar_All.pipe_left setpos uu____5462  in
            (uu____5459, noaqs)
        | FStar_Parser_AST.Uvar u ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedUniverseVariable,
                (Prims.strcat "Unexpected universe variable "
                   (Prims.strcat (FStar_Ident.text_of_id u)
                      " in non-universe context")))
              top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____5501 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____5501 with
             | FStar_Pervasives_Native.None  ->
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     (Prims.strcat "Unexpected or unbound operator: "
                        (FStar_Ident.text_of_id s)))
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let uu____5517 =
                     let uu____5532 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____5574 = desugar_term_aq env t  in
                               match uu____5574 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____5532 FStar_List.unzip  in
                   (match uu____5517 with
                    | (args1,aqs) ->
                        let uu____5657 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____5657, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____5693)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____5708 =
              let uu___120_5709 = top  in
              let uu____5710 =
                let uu____5711 =
                  let uu____5718 =
                    let uu___121_5719 = top  in
                    let uu____5720 =
                      let uu____5721 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____5721  in
                    {
                      FStar_Parser_AST.tm = uu____5720;
                      FStar_Parser_AST.range =
                        (uu___121_5719.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___121_5719.FStar_Parser_AST.level)
                    }  in
                  (uu____5718, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____5711  in
              {
                FStar_Parser_AST.tm = uu____5710;
                FStar_Parser_AST.range =
                  (uu___120_5709.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___120_5709.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____5708
        | FStar_Parser_AST.Construct (n1,(a,uu____5724)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____5740 =
                let uu___122_5741 = top  in
                let uu____5742 =
                  let uu____5743 =
                    let uu____5750 =
                      let uu___123_5751 = top  in
                      let uu____5752 =
                        let uu____5753 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____5753  in
                      {
                        FStar_Parser_AST.tm = uu____5752;
                        FStar_Parser_AST.range =
                          (uu___123_5751.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___123_5751.FStar_Parser_AST.level)
                      }  in
                    (uu____5750, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____5743  in
                {
                  FStar_Parser_AST.tm = uu____5742;
                  FStar_Parser_AST.range =
                    (uu___122_5741.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___122_5741.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____5740))
        | FStar_Parser_AST.Construct (n1,(a,uu____5756)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____5771 =
              let uu___124_5772 = top  in
              let uu____5773 =
                let uu____5774 =
                  let uu____5781 =
                    let uu___125_5782 = top  in
                    let uu____5783 =
                      let uu____5784 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____5784  in
                    {
                      FStar_Parser_AST.tm = uu____5783;
                      FStar_Parser_AST.range =
                        (uu___125_5782.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___125_5782.FStar_Parser_AST.level)
                    }  in
                  (uu____5781, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____5774  in
              {
                FStar_Parser_AST.tm = uu____5773;
                FStar_Parser_AST.range =
                  (uu___124_5772.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___124_5772.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____5771
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5785; FStar_Ident.ident = uu____5786;
              FStar_Ident.nsstr = uu____5787; FStar_Ident.str = "Type0";_}
            ->
            let uu____5790 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____5790, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5805; FStar_Ident.ident = uu____5806;
              FStar_Ident.nsstr = uu____5807; FStar_Ident.str = "Type";_}
            ->
            let uu____5810 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____5810, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____5825; FStar_Ident.ident = uu____5826;
               FStar_Ident.nsstr = uu____5827; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____5845 =
              let uu____5848 =
                let uu____5849 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____5849  in
              mk1 uu____5848  in
            (uu____5845, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5862; FStar_Ident.ident = uu____5863;
              FStar_Ident.nsstr = uu____5864; FStar_Ident.str = "Effect";_}
            ->
            let uu____5867 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____5867, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5882; FStar_Ident.ident = uu____5883;
              FStar_Ident.nsstr = uu____5884; FStar_Ident.str = "True";_}
            ->
            let uu____5887 =
              FStar_Syntax_Syntax.fvar
                (FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                   top.FStar_Parser_AST.range)
                FStar_Syntax_Syntax.Delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____5887, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____5898; FStar_Ident.ident = uu____5899;
              FStar_Ident.nsstr = uu____5900; FStar_Ident.str = "False";_}
            ->
            let uu____5903 =
              FStar_Syntax_Syntax.fvar
                (FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                   top.FStar_Parser_AST.range)
                FStar_Syntax_Syntax.Delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____5903, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____5916;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____5918 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____5918 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____5927 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_defined_at_level
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None
                     in
                  (uu____5927, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____5938 =
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      (FStar_Ident.text_of_lid eff_name) txt
                     in
                  failwith uu____5938))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____5945 = desugar_name mk1 setpos env true l  in
              (uu____5945, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____5958 = desugar_name mk1 setpos env true l  in
              (uu____5958, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____5979 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____5979 with
                | FStar_Pervasives_Native.Some uu____5988 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____5993 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____5993 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____6007 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____6024 =
                    let uu____6025 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____6025  in
                  (uu____6024, noaqs)
              | uu____6036 ->
                  let uu____6043 =
                    let uu____6048 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____6048)  in
                  FStar_Errors.raise_error uu____6043
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____6055 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____6055 with
              | FStar_Pervasives_Native.None  ->
                  let uu____6062 =
                    let uu____6067 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____6067)
                     in
                  FStar_Errors.raise_error uu____6062
                    top.FStar_Parser_AST.range
              | uu____6072 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____6076 = desugar_name mk1 setpos env true lid'  in
                  (uu____6076, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____6102 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____6102 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____6133 ->
                       let uu____6140 =
                         FStar_Util.take
                           (fun uu____6164  ->
                              match uu____6164 with
                              | (uu____6169,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____6140 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____6214 =
                              let uu____6229 =
                                FStar_List.map
                                  (fun uu____6262  ->
                                     match uu____6262 with
                                     | (t,imp) ->
                                         let uu____6279 =
                                           desugar_term_aq env t  in
                                         (match uu____6279 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____6229
                                FStar_List.unzip
                               in
                            (match uu____6214 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____6372 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____6372, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____6402 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____6402 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.strcat "Constructor "
                             (Prims.strcat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____6409 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.strcat "Effect "
                             (Prims.strcat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____6420 =
              FStar_List.fold_left
                (fun uu____6465  ->
                   fun b  ->
                     match uu____6465 with
                     | (env1,tparams,typs) ->
                         let uu____6522 = desugar_binder env1 b  in
                         (match uu____6522 with
                          | (xopt,t1) ->
                              let uu____6551 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____6560 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____6560)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____6551 with
                               | (env2,x) ->
                                   let uu____6580 =
                                     let uu____6583 =
                                       let uu____6586 =
                                         let uu____6587 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____6587
                                          in
                                       [uu____6586]  in
                                     FStar_List.append typs uu____6583  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___126_6613 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___126_6613.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___126_6613.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____6580)))) (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      FStar_Pervasives_Native.None])
               in
            (match uu____6420 with
             | (env1,uu____6641,targs) ->
                 let uu____6663 =
                   let uu____6668 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____6668
                    in
                 (match uu____6663 with
                  | (tup,uu____6678) ->
                      let uu____6679 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_app (tup, targs))
                         in
                      (uu____6679, noaqs)))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____6704 = uncurry binders t  in
            (match uu____6704 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___92_6740 =
                   match uu___92_6740 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1  in
                       let uu____6754 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____6754
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____6776 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____6776 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____6785 = aux env [] bs  in (uu____6785, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____6806 = desugar_binder env b  in
            (match uu____6806 with
             | (FStar_Pervasives_Native.None ,uu____6817) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____6831 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____6831 with
                  | ((x,uu____6841),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____6848 =
                        let uu____6851 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____6851  in
                      (uu____6848, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern)
               in
            let uu____6883 =
              FStar_List.fold_left
                (fun uu____6903  ->
                   fun pat  ->
                     match uu____6903 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed
                              (uu____6929,(t,FStar_Pervasives_Native.None ))
                              ->
                              let uu____6939 =
                                let uu____6942 = free_type_vars env1 t  in
                                FStar_List.append uu____6942 ftvs  in
                              (env1, uu____6939)
                          | FStar_Parser_AST.PatAscribed
                              (uu____6947,(t,FStar_Pervasives_Native.Some
                                           tac))
                              ->
                              let uu____6958 =
                                let uu____6961 = free_type_vars env1 t  in
                                let uu____6964 =
                                  let uu____6967 = free_type_vars env1 tac
                                     in
                                  FStar_List.append uu____6967 ftvs  in
                                FStar_List.append uu____6961 uu____6964  in
                              (env1, uu____6958)
                          | uu____6972 -> (env1, ftvs))) (env, []) binders1
               in
            (match uu____6883 with
             | (uu____6981,ftv) ->
                 let ftv1 = sort_ftv ftv  in
                 let binders2 =
                   let uu____6993 =
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
                   FStar_List.append uu____6993 binders1  in
                 let rec aux env1 bs sc_pat_opt uu___93_7038 =
                   match uu___93_7038 with
                   | [] ->
                       let uu____7061 = desugar_term_aq env1 body  in
                       (match uu____7061 with
                        | (body1,aq) ->
                            let body2 =
                              match sc_pat_opt with
                              | FStar_Pervasives_Native.Some (sc,pat) ->
                                  let body2 =
                                    let uu____7092 =
                                      let uu____7093 =
                                        FStar_Syntax_Syntax.pat_bvs pat  in
                                      FStar_All.pipe_right uu____7093
                                        (FStar_List.map
                                           FStar_Syntax_Syntax.mk_binder)
                                       in
                                    FStar_Syntax_Subst.close uu____7092 body1
                                     in
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_match
                                       (sc,
                                         [(pat, FStar_Pervasives_Native.None,
                                            body2)]))
                                    FStar_Pervasives_Native.None
                                    body2.FStar_Syntax_Syntax.pos
                              | FStar_Pervasives_Native.None  -> body1  in
                            let uu____7146 =
                              let uu____7149 =
                                no_annot_abs (FStar_List.rev bs) body2  in
                              setpos uu____7149  in
                            (uu____7146, aq))
                   | p::rest ->
                       let uu____7162 = desugar_binding_pat env1 p  in
                       (match uu____7162 with
                        | (env2,b,pat) ->
                            let pat1 =
                              match pat with
                              | [] -> FStar_Pervasives_Native.None
                              | p1::[] -> FStar_Pervasives_Native.Some p1
                              | uu____7190 ->
                                  FStar_Errors.raise_error
                                    (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                      "Disjunctive patterns are not supported in abstractions")
                                    p.FStar_Parser_AST.prange
                               in
                            let uu____7195 =
                              match b with
                              | LetBinder uu____7228 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat1, sc_pat_opt) with
                                    | (FStar_Pervasives_Native.None
                                       ,uu____7284) -> sc_pat_opt
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.None ) ->
                                        let uu____7320 =
                                          let uu____7325 =
                                            FStar_Syntax_Syntax.bv_to_name x
                                             in
                                          (uu____7325, p1)  in
                                        FStar_Pervasives_Native.Some
                                          uu____7320
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.Some
                                       (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____7361,uu____7362) ->
                                             let tup2 =
                                               let uu____7364 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____7364
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____7368 =
                                                 let uu____7371 =
                                                   let uu____7372 =
                                                     let uu____7387 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2)
                                                        in
                                                     let uu____7390 =
                                                       let uu____7393 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc
                                                          in
                                                       let uu____7394 =
                                                         let uu____7397 =
                                                           let uu____7398 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x
                                                              in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____7398
                                                            in
                                                         [uu____7397]  in
                                                       uu____7393 ::
                                                         uu____7394
                                                        in
                                                     (uu____7387, uu____7390)
                                                      in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____7372
                                                    in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____7371
                                                  in
                                               uu____7368
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Parser_AST.range
                                                in
                                             let p2 =
                                               let uu____7409 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p1, false)]))
                                                 uu____7409
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____7440,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____7442,pats)) ->
                                             let tupn =
                                               let uu____7481 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____7481
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____7491 =
                                                 let uu____7492 =
                                                   let uu____7507 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn)
                                                      in
                                                   let uu____7510 =
                                                     let uu____7519 =
                                                       let uu____7528 =
                                                         let uu____7529 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____7529
                                                          in
                                                       [uu____7528]  in
                                                     FStar_List.append args
                                                       uu____7519
                                                      in
                                                   (uu____7507, uu____7510)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____7492
                                                  in
                                               mk1 uu____7491  in
                                             let p2 =
                                               let uu____7549 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p1, false)])))
                                                 uu____7549
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | uu____7584 ->
                                             failwith "Impossible")
                                     in
                                  ((x, aq), sc_pat_opt1)
                               in
                            (match uu____7195 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest))
                    in
                 aux env [] FStar_Pervasives_Native.None binders2)
        | FStar_Parser_AST.App
            (uu____7655,uu____7656,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____7674 =
                let uu____7675 = unparen e  in uu____7675.FStar_Parser_AST.tm
                 in
              match uu____7674 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____7685 ->
                  let uu____7686 = desugar_term_aq env e  in
                  (match uu____7686 with
                   | (head1,aq) ->
                       let uu____7699 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____7699, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____7706 ->
            let rec aux args aqs e =
              let uu____7759 =
                let uu____7760 = unparen e  in uu____7760.FStar_Parser_AST.tm
                 in
              match uu____7759 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____7780 = desugar_term_aq env t  in
                  (match uu____7780 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____7816 ->
                  let uu____7817 = desugar_term_aq env e  in
                  (match uu____7817 with
                   | (head1,aq) ->
                       let uu____7840 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____7840, (join_aqs (aq :: aqs))))
               in
            aux [] [] top
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
            let uu____7880 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____7880
        | FStar_Parser_AST.Seq (t1,t2) ->
            let t =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Let
                   (FStar_Parser_AST.NoLetQualifier,
                     [(FStar_Pervasives_Native.None,
                        ((FStar_Parser_AST.mk_pattern
                            FStar_Parser_AST.PatWild
                            t1.FStar_Parser_AST.range), t1))], t2))
                top.FStar_Parser_AST.range FStar_Parser_AST.Expr
               in
            let uu____7932 = desugar_term_aq env t  in
            (match uu____7932 with
             | (tm,s) ->
                 let uu____7943 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____7943, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____7951 =
              let uu____7960 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____7960 then desugar_typ_aq else desugar_term_aq  in
            uu____7951 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____8011 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____8154  ->
                        match uu____8154 with
                        | (attr_opt,(p,def)) ->
                            let uu____8212 = is_app_pattern p  in
                            if uu____8212
                            then
                              let uu____8243 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____8243, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____8325 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____8325, def1)
                               | uu____8370 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____8408);
                                           FStar_Parser_AST.prange =
                                             uu____8409;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____8457 =
                                            let uu____8478 =
                                              let uu____8483 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____8483  in
                                            (uu____8478, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____8457, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____8574) ->
                                        if top_level
                                        then
                                          let uu____8609 =
                                            let uu____8630 =
                                              let uu____8635 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____8635  in
                                            (uu____8630, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____8609, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____8725 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____8756 =
                FStar_List.fold_left
                  (fun uu____8829  ->
                     fun uu____8830  ->
                       match (uu____8829, uu____8830) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____8938,uu____8939),uu____8940))
                           ->
                           let uu____9057 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____9083 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____9083 with
                                  | (env2,xx) ->
                                      let uu____9102 =
                                        let uu____9105 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____9105 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx), uu____9102))
                             | FStar_Util.Inr l ->
                                 let uu____9113 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.Delta_equational
                                    in
                                 (uu____9113, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____9057 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____8756 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____9255 =
                    match uu____9255 with
                    | (attrs_opt,(uu____9291,args,result_t),def) ->
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
                                let uu____9379 = is_comp_type env1 t  in
                                if uu____9379
                                then
                                  ((let uu____9381 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____9391 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____9391))
                                       in
                                    match uu____9381 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____9394 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____9396 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____9396))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____9394
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t)
                                 in
                              let uu____9400 =
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range
                                 in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed (def, t1, tacopt))
                                uu____9400 FStar_Parser_AST.Expr
                           in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____9404 ->
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
                              let uu____9419 =
                                let uu____9420 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____9420
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____9419
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
                  let uu____9479 = desugar_term_aq env' body  in
                  (match uu____9479 with
                   | (body1,aq) ->
                       let uu____9492 =
                         let uu____9495 =
                           let uu____9496 =
                             let uu____9509 =
                               FStar_Syntax_Subst.close rec_bindings1 body1
                                in
                             ((is_rec, lbs1), uu____9509)  in
                           FStar_Syntax_Syntax.Tm_let uu____9496  in
                         FStar_All.pipe_left mk1 uu____9495  in
                       (uu____9492, aq))
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
              let uu____9569 =
                desugar_binding_pat_maybe_top top_level env pat is_mutable
                 in
              match uu____9569 with
              | (env1,binder,pat1) ->
                  let uu____9591 =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let uu____9617 = desugar_term_aq env1 t2  in
                        (match uu____9617 with
                         | (body1,aq) ->
                             let fv =
                               let uu____9631 =
                                 FStar_Syntax_Util.incr_delta_qualifier t12
                                  in
                               FStar_Syntax_Syntax.lid_as_fv l uu____9631
                                 FStar_Pervasives_Native.None
                                in
                             let uu____9632 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t12,
                                            (t12.FStar_Syntax_Syntax.pos))]),
                                      body1))
                                in
                             (uu____9632, aq))
                    | LocalBinder (x,uu____9656) ->
                        let uu____9657 = desugar_term_aq env1 t2  in
                        (match uu____9657 with
                         | (body1,aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | {
                                   FStar_Syntax_Syntax.v =
                                     FStar_Syntax_Syntax.Pat_wild uu____9671;
                                   FStar_Syntax_Syntax.p = uu____9672;_}::[]
                                   -> body1
                               | uu____9677 ->
                                   let uu____9680 =
                                     let uu____9683 =
                                       let uu____9684 =
                                         let uu____9707 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         let uu____9708 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1
                                            in
                                         (uu____9707, uu____9708)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____9684
                                        in
                                     FStar_Syntax_Syntax.mk uu____9683  in
                                   uu____9680 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range
                                in
                             let uu____9718 =
                               let uu____9721 =
                                 let uu____9722 =
                                   let uu____9735 =
                                     let uu____9736 =
                                       let uu____9737 =
                                         FStar_Syntax_Syntax.mk_binder x  in
                                       [uu____9737]  in
                                     FStar_Syntax_Subst.close uu____9736
                                       body2
                                      in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t12,
                                           (t12.FStar_Syntax_Syntax.pos))]),
                                     uu____9735)
                                    in
                                 FStar_Syntax_Syntax.Tm_let uu____9722  in
                               FStar_All.pipe_left mk1 uu____9721  in
                             (uu____9718, aq))
                     in
                  (match uu____9591 with
                   | (tm,aq) ->
                       if is_mutable
                       then
                         let uu____9778 =
                           FStar_All.pipe_left mk1
                             (FStar_Syntax_Syntax.Tm_meta
                                (tm,
                                  (FStar_Syntax_Syntax.Meta_desugared
                                     FStar_Syntax_Syntax.Mutable_alloc)))
                            in
                         (uu____9778, aq)
                       else (tm, aq))
               in
            let uu____9790 = FStar_List.hd lbs  in
            (match uu____9790 with
             | (attrs,(head_pat,defn)) ->
                 let uu____9834 = is_rec || (is_app_pattern head_pat)  in
                 if uu____9834
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____9847 =
                let uu____9848 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.Delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____9848  in
              mk1 uu____9847  in
            let uu____9849 = desugar_term_aq env t1  in
            (match uu____9849 with
             | (t1',aq1) ->
                 let uu____9860 = desugar_term_aq env t2  in
                 (match uu____9860 with
                  | (t2',aq2) ->
                      let uu____9871 = desugar_term_aq env t3  in
                      (match uu____9871 with
                       | (t3',aq3) ->
                           let uu____9882 =
                             let uu____9885 =
                               let uu____9886 =
                                 let uu____9909 =
                                   FStar_Syntax_Util.ascribe t1'
                                     ((FStar_Util.Inl t_bool1),
                                       FStar_Pervasives_Native.None)
                                    in
                                 let uu____9930 =
                                   let uu____9945 =
                                     let uu____9958 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t2.FStar_Parser_AST.range
                                        in
                                     (uu____9958,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____9969 =
                                     let uu____9984 =
                                       let uu____9997 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t3.FStar_Parser_AST.range
                                          in
                                       (uu____9997,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____9984]  in
                                   uu____9945 :: uu____9969  in
                                 (uu____9909, uu____9930)  in
                               FStar_Syntax_Syntax.Tm_match uu____9886  in
                             mk1 uu____9885  in
                           (uu____9882, (join_aqs [aq1; aq2; aq3])))))
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
            desugar_term_aq env a2
        | FStar_Parser_AST.Match (e,branches) ->
            let desugar_branch uu____10156 =
              match uu____10156 with
              | (pat,wopt,b) ->
                  let uu____10178 = desugar_match_pat env pat  in
                  (match uu____10178 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____10203 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____10203
                          in
                       let uu____10204 = desugar_term_aq env1 b  in
                       (match uu____10204 with
                        | (b1,aq) ->
                            let uu____10217 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____10217, aq)))
               in
            let uu____10222 = desugar_term_aq env e  in
            (match uu____10222 with
             | (e1,aq) ->
                 let uu____10233 =
                   let uu____10242 =
                     let uu____10253 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____10253 FStar_List.unzip  in
                   FStar_All.pipe_right uu____10242
                     (fun uu____10317  ->
                        match uu____10317 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____10233 with
                  | (brs,aqs) ->
                      let uu____10368 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____10368, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____10401 = is_comp_type env t  in
              if uu____10401
              then
                let uu____10408 = desugar_comp t.FStar_Parser_AST.range env t
                   in
                FStar_Util.Inr uu____10408
              else
                (let uu____10414 = desugar_term env t  in
                 FStar_Util.Inl uu____10414)
               in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)  in
            let uu____10420 = desugar_term_aq env e  in
            (match uu____10420 with
             | (e1,aq) ->
                 let uu____10431 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_ascribed
                        (e1, (annot, tac_opt1), FStar_Pervasives_Native.None))
                    in
                 (uu____10431, aq))
        | FStar_Parser_AST.Record (uu____10460,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____10501 = FStar_List.hd fields  in
              match uu____10501 with | (f,uu____10513) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____10555  ->
                        match uu____10555 with
                        | (g,uu____10561) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____10567,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____10581 =
                         let uu____10586 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____10586)
                          in
                       FStar_Errors.raise_error uu____10581
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
                  let uu____10594 =
                    let uu____10605 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____10636  ->
                              match uu____10636 with
                              | (f,uu____10646) ->
                                  let uu____10647 =
                                    let uu____10648 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____10648
                                     in
                                  (uu____10647, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____10605)  in
                  FStar_Parser_AST.Construct uu____10594
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____10666 =
                      let uu____10667 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____10667  in
                    FStar_Parser_AST.mk_term uu____10666
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____10669 =
                      let uu____10682 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____10712  ->
                                match uu____10712 with
                                | (f,uu____10722) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____10682)  in
                    FStar_Parser_AST.Record uu____10669  in
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
            let uu____10782 = desugar_term_aq env recterm1  in
            (match uu____10782 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____10798;
                         FStar_Syntax_Syntax.vars = uu____10799;_},args)
                      ->
                      let uu____10821 =
                        let uu____10824 =
                          let uu____10825 =
                            let uu____10840 =
                              let uu____10841 =
                                let uu____10844 =
                                  let uu____10845 =
                                    let uu____10852 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____10852)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____10845
                                   in
                                FStar_Pervasives_Native.Some uu____10844  in
                              FStar_Syntax_Syntax.fvar
                                (FStar_Ident.set_lid_range
                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                   e.FStar_Syntax_Syntax.pos)
                                FStar_Syntax_Syntax.Delta_constant
                                uu____10841
                               in
                            (uu____10840, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____10825  in
                        FStar_All.pipe_left mk1 uu____10824  in
                      (uu____10821, s)
                  | uu____10881 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____10885 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____10885 with
              | (constrname,is_rec) ->
                  let uu____10900 = desugar_term_aq env e  in
                  (match uu____10900 with
                   | (e1,s) ->
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
                       let uu____10918 =
                         let uu____10921 =
                           let uu____10922 =
                             let uu____10937 =
                               FStar_Syntax_Syntax.fvar
                                 (FStar_Ident.set_lid_range projname
                                    (FStar_Ident.range_of_lid f))
                                 FStar_Syntax_Syntax.Delta_equational qual
                                in
                             let uu____10938 =
                               let uu____10941 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____10941]  in
                             (uu____10937, uu____10938)  in
                           FStar_Syntax_Syntax.Tm_app uu____10922  in
                         FStar_All.pipe_left mk1 uu____10921  in
                       (uu____10918, s))))
        | FStar_Parser_AST.NamedTyp (uu____10948,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____10957 =
              let uu____10958 = FStar_Syntax_Subst.compress tm  in
              uu____10958.FStar_Syntax_Syntax.n  in
            (match uu____10957 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____10966 =
                   let uu___127_10969 =
                     let uu____10970 =
                       let uu____10971 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____10971  in
                     FStar_Syntax_Util.exp_string uu____10970  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___127_10969.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___127_10969.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____10966, noaqs)
             | uu____10984 ->
                 let uu____10985 =
                   let uu____10990 =
                     let uu____10991 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.strcat "VQuote, expected an fvar, got: "
                       uu____10991
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____10990)  in
                 FStar_Errors.raise_error uu____10985
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____10997 = desugar_term_aq env e  in
            (match uu____10997 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____11009 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____11009, noaqs))
        | FStar_Parser_AST.Antiquote (b,e) ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____11029 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____11030 =
              let uu____11039 =
                let uu____11046 = desugar_term env e  in (bv, b, uu____11046)
                 in
              [uu____11039]  in
            (uu____11029, uu____11030)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____11077 =
              let uu____11080 =
                let uu____11081 =
                  let uu____11088 = desugar_term env e  in (uu____11088, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____11081  in
              FStar_All.pipe_left mk1 uu____11080  in
            (uu____11077, noaqs)
        | uu____11103 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____11104 = desugar_formula env top  in
            (uu____11104, noaqs)
        | uu____11115 ->
            let uu____11116 =
              let uu____11121 =
                let uu____11122 = FStar_Parser_AST.term_to_string top  in
                Prims.strcat "Unexpected term: " uu____11122  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____11121)  in
            FStar_Errors.raise_error uu____11116 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____11128 -> false
    | uu____11137 -> true

and (is_synth_by_tactic :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (l,r,FStar_Parser_AST.Hash ) ->
          is_synth_by_tactic e l
      | FStar_Parser_AST.Var lid ->
          let uu____11143 =
            FStar_Syntax_DsEnv.resolve_to_fully_qualified_name e lid  in
          (match uu____11143 with
           | FStar_Pervasives_Native.Some lid1 ->
               FStar_Ident.lid_equals lid1 FStar_Parser_Const.synth_lid
           | FStar_Pervasives_Native.None  -> false)
      | uu____11147 -> false

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
           (fun uu____11184  ->
              match uu____11184 with
              | (a,imp) ->
                  let uu____11197 = desugar_term env a  in
                  arg_withimp_e imp uu____11197))

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
        let is_requires uu____11223 =
          match uu____11223 with
          | (t1,uu____11229) ->
              let uu____11230 =
                let uu____11231 = unparen t1  in
                uu____11231.FStar_Parser_AST.tm  in
              (match uu____11230 with
               | FStar_Parser_AST.Requires uu____11232 -> true
               | uu____11239 -> false)
           in
        let is_ensures uu____11247 =
          match uu____11247 with
          | (t1,uu____11253) ->
              let uu____11254 =
                let uu____11255 = unparen t1  in
                uu____11255.FStar_Parser_AST.tm  in
              (match uu____11254 with
               | FStar_Parser_AST.Ensures uu____11256 -> true
               | uu____11263 -> false)
           in
        let is_app head1 uu____11274 =
          match uu____11274 with
          | (t1,uu____11280) ->
              let uu____11281 =
                let uu____11282 = unparen t1  in
                uu____11282.FStar_Parser_AST.tm  in
              (match uu____11281 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____11284;
                      FStar_Parser_AST.level = uu____11285;_},uu____11286,uu____11287)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____11288 -> false)
           in
        let is_smt_pat uu____11296 =
          match uu____11296 with
          | (t1,uu____11302) ->
              let uu____11303 =
                let uu____11304 = unparen t1  in
                uu____11304.FStar_Parser_AST.tm  in
              (match uu____11303 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____11307);
                             FStar_Parser_AST.range = uu____11308;
                             FStar_Parser_AST.level = uu____11309;_},uu____11310)::uu____11311::[])
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
                             FStar_Parser_AST.range = uu____11350;
                             FStar_Parser_AST.level = uu____11351;_},uu____11352)::uu____11353::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
               | uu____11378 -> false)
           in
        let is_decreases = is_app "decreases"  in
        let pre_process_comp_typ t1 =
          let uu____11406 = head_and_args t1  in
          match uu____11406 with
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
                   let thunk_ens uu____11500 =
                     match uu____11500 with
                     | (e,i) ->
                         let uu____11511 = thunk_ens_ e  in (uu____11511, i)
                      in
                   let fail_lemma uu____11521 =
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
                         let uu____11601 =
                           let uu____11608 =
                             let uu____11615 = thunk_ens ens  in
                             [uu____11615; nil_pat]  in
                           req_true :: uu____11608  in
                         unit_tm :: uu____11601
                     | req::ens::[] when
                         (is_requires req) && (is_ensures ens) ->
                         let uu____11662 =
                           let uu____11669 =
                             let uu____11676 = thunk_ens ens  in
                             [uu____11676; nil_pat]  in
                           req :: uu____11669  in
                         unit_tm :: uu____11662
                     | ens::smtpat::[] when
                         (((let uu____11725 = is_requires ens  in
                            Prims.op_Negation uu____11725) &&
                             (let uu____11727 = is_smt_pat ens  in
                              Prims.op_Negation uu____11727))
                            &&
                            (let uu____11729 = is_decreases ens  in
                             Prims.op_Negation uu____11729))
                           && (is_smt_pat smtpat)
                         ->
                         let uu____11730 =
                           let uu____11737 =
                             let uu____11744 = thunk_ens ens  in
                             [uu____11744; smtpat]  in
                           req_true :: uu____11737  in
                         unit_tm :: uu____11730
                     | ens::dec::[] when
                         (is_ensures ens) && (is_decreases dec) ->
                         let uu____11791 =
                           let uu____11798 =
                             let uu____11805 = thunk_ens ens  in
                             [uu____11805; nil_pat; dec]  in
                           req_true :: uu____11798  in
                         unit_tm :: uu____11791
                     | ens::dec::smtpat::[] when
                         ((is_ensures ens) && (is_decreases dec)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____11865 =
                           let uu____11872 =
                             let uu____11879 = thunk_ens ens  in
                             [uu____11879; smtpat; dec]  in
                           req_true :: uu____11872  in
                         unit_tm :: uu____11865
                     | req::ens::dec::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_decreases dec)
                         ->
                         let uu____11939 =
                           let uu____11946 =
                             let uu____11953 = thunk_ens ens  in
                             [uu____11953; nil_pat; dec]  in
                           req :: uu____11946  in
                         unit_tm :: uu____11939
                     | req::ens::smtpat::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____12013 =
                           let uu____12020 =
                             let uu____12027 = thunk_ens ens  in
                             [uu____12027; smtpat]  in
                           req :: uu____12020  in
                         unit_tm :: uu____12013
                     | req::ens::dec::smtpat::[] when
                         (((is_requires req) && (is_ensures ens)) &&
                            (is_smt_pat smtpat))
                           && (is_decreases dec)
                         ->
                         let uu____12092 =
                           let uu____12099 =
                             let uu____12106 = thunk_ens ens  in
                             [uu____12106; dec; smtpat]  in
                           req :: uu____12099  in
                         unit_tm :: uu____12092
                     | _other -> fail_lemma ()  in
                   let head_and_attributes =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) lemma
                      in
                   (head_and_attributes, args1)
               | FStar_Parser_AST.Name l when
                   FStar_Syntax_DsEnv.is_effect_name env l ->
                   let uu____12168 =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) l
                      in
                   (uu____12168, args)
               | FStar_Parser_AST.Name l when
                   (let uu____12196 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____12196
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   (((FStar_Ident.set_lid_range
                        FStar_Parser_Const.effect_Tot_lid
                        head1.FStar_Parser_AST.range), []), args)
               | FStar_Parser_AST.Name l when
                   (let uu____12214 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____12214
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
               | uu____12252 ->
                   let default_effect =
                     let uu____12254 = FStar_Options.ml_ish ()  in
                     if uu____12254
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____12257 =
                           FStar_Options.warn_default_effects ()  in
                         if uu____12257
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
        let uu____12281 = pre_process_comp_typ t  in
        match uu____12281 with
        | ((eff,cattributes),args) ->
            (Obj.magic
               (if (FStar_List.length args) = (Prims.parse_int "0")
                then
                  Obj.repr
                    (let uu____12330 =
                       let uu____12335 =
                         let uu____12336 =
                           FStar_Syntax_Print.lid_to_string eff  in
                         FStar_Util.format1 "Not enough args to effect %s"
                           uu____12336
                          in
                       (FStar_Errors.Fatal_NotEnoughArgsToEffect,
                         uu____12335)
                        in
                     fail1 () uu____12330)
                else Obj.repr ());
             (let is_universe uu____12345 =
                match uu____12345 with
                | (uu____12350,imp) -> imp = FStar_Parser_AST.UnivApp  in
              let uu____12352 = FStar_Util.take is_universe args  in
              match uu____12352 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____12411  ->
                         match uu____12411 with
                         | (u,imp) -> desugar_universe u) universes
                     in
                  let uu____12418 =
                    let uu____12433 = FStar_List.hd args1  in
                    let uu____12442 = FStar_List.tl args1  in
                    (uu____12433, uu____12442)  in
                  (match uu____12418 with
                   | (result_arg,rest) ->
                       let result_typ =
                         desugar_typ env
                           (FStar_Pervasives_Native.fst result_arg)
                          in
                       let rest1 = desugar_args env rest  in
                       let uu____12497 =
                         let is_decrease uu____12533 =
                           match uu____12533 with
                           | (t1,uu____12543) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.pos = uu____12553;
                                       FStar_Syntax_Syntax.vars = uu____12554;_},uu____12555::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.decreases_lid
                                | uu____12586 -> false)
                            in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease)
                          in
                       (match uu____12497 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____12700  ->
                                      match uu____12700 with
                                      | (t1,uu____12710) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____12719,(arg,uu____12721)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____12750 -> failwith "impos")))
                               in
                            let no_additional_args =
                              let is_empty a l =
                                match l with
                                | [] -> true
                                | uu____12763 -> false  in
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
                                           | uu____12903 -> pat  in
                                         let uu____12904 =
                                           let uu____12915 =
                                             let uu____12926 =
                                               let uu____12935 =
                                                 FStar_Syntax_Syntax.mk
                                                   (FStar_Syntax_Syntax.Tm_meta
                                                      (pat1,
                                                        (FStar_Syntax_Syntax.Meta_desugared
                                                           FStar_Syntax_Syntax.Meta_smt_pat)))
                                                   FStar_Pervasives_Native.None
                                                   pat1.FStar_Syntax_Syntax.pos
                                                  in
                                               (uu____12935, aq)  in
                                             [uu____12926]  in
                                           ens :: uu____12915  in
                                         req :: uu____12904
                                     | uu____12976 -> rest2
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
        | uu____12998 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___128_13015 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___128_13015.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___128_13015.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___129_13049 = b  in
             {
               FStar_Parser_AST.b = (uu___129_13049.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___129_13049.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___129_13049.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____13108 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____13108)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____13121 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____13121 with
             | (env1,a1) ->
                 let a2 =
                   let uu___130_13131 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___130_13131.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___130_13131.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____13153 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____13167 =
                     let uu____13170 =
                       let uu____13171 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____13171]  in
                     no_annot_abs uu____13170 body2  in
                   FStar_All.pipe_left setpos uu____13167  in
                 let uu____13176 =
                   let uu____13177 =
                     let uu____13192 =
                       FStar_Syntax_Syntax.fvar
                         (FStar_Ident.set_lid_range q
                            b.FStar_Parser_AST.brange)
                         (FStar_Syntax_Syntax.Delta_defined_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____13193 =
                       let uu____13196 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____13196]  in
                     (uu____13192, uu____13193)  in
                   FStar_Syntax_Syntax.Tm_app uu____13177  in
                 FStar_All.pipe_left mk1 uu____13176)
        | uu____13201 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____13273 = q (rest, pats, body)  in
              let uu____13280 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____13273 uu____13280
                FStar_Parser_AST.Formula
               in
            let uu____13281 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____13281 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____13290 -> failwith "impossible"  in
      let uu____13293 =
        let uu____13294 = unparen f  in uu____13294.FStar_Parser_AST.tm  in
      match uu____13293 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____13301,uu____13302) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____13313,uu____13314) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____13345 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____13345
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____13381 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____13381
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____13424 -> desugar_term env f

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
      let uu____13429 =
        FStar_List.fold_left
          (fun uu____13465  ->
             fun b  ->
               match uu____13465 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___131_13517 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___131_13517.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___131_13517.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___131_13517.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____13534 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____13534 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___132_13554 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___132_13554.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___132_13554.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____13571 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____13429 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

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
          let uu____13658 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____13658)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____13663 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____13663)
      | FStar_Parser_AST.TVariable x ->
          let uu____13667 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____13667)
      | FStar_Parser_AST.NoName t ->
          let uu____13675 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____13675)
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
               (fun uu___94_13708  ->
                  match uu___94_13708 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____13709 -> false))
           in
        let quals2 q =
          let uu____13720 =
            (let uu____13723 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____13723) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____13720
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____13736 =
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
                  FStar_Syntax_Syntax.sigquals = uu____13736;
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
            let uu____13767 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____13797  ->
                        match uu____13797 with
                        | (x,uu____13805) ->
                            let uu____13806 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____13806 with
                             | (field_name,uu____13814) ->
                                 let only_decl =
                                   ((let uu____13818 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____13818)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____13820 =
                                        let uu____13821 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____13821.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____13820)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____13835 =
                                       FStar_List.filter
                                         (fun uu___95_13839  ->
                                            match uu___95_13839 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____13840 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____13835
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___96_13853  ->
                                             match uu___96_13853 with
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____13854 -> false))
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
                                      let uu____13862 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____13862
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          FStar_Syntax_Syntax.Delta_equational
                                      else
                                        FStar_Syntax_Syntax.Delta_equational
                                       in
                                    let lb =
                                      let uu____13867 =
                                        let uu____13872 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____13872  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____13867;
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
                                      let uu____13876 =
                                        let uu____13877 =
                                          let uu____13884 =
                                            let uu____13887 =
                                              let uu____13888 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____13888
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____13887]  in
                                          ((false, [lb]), uu____13884)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____13877
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____13876;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____13767 FStar_List.flatten
  
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
            (lid,uu____13932,t,uu____13934,n1,uu____13936) when
            Prims.op_Negation
              (FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid)
            ->
            let uu____13941 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____13941 with
             | (formals,uu____13957) ->
                 (match formals with
                  | [] -> []
                  | uu____13980 ->
                      let filter_records uu___97_13992 =
                        match uu___97_13992 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____13995,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____14007 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____14009 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____14009 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Syntax_Syntax.Data_ctor
                        | FStar_Pervasives_Native.Some q -> q  in
                      let iquals1 =
                        if
                          FStar_List.contains FStar_Syntax_Syntax.Abstract
                            iquals
                        then FStar_Syntax_Syntax.Private :: iquals
                        else iquals  in
                      let uu____14019 = FStar_Util.first_N n1 formals  in
                      (match uu____14019 with
                       | (uu____14042,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____14068 -> []
  
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
                    let uu____14118 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____14118
                    then
                      let uu____14121 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____14121
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____14124 =
                      let uu____14129 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____14129  in
                    let uu____14130 =
                      let uu____14133 = FStar_Syntax_Syntax.mk_Total k  in
                      FStar_Syntax_Util.arrow typars uu____14133  in
                    let uu____14136 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____14124;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____14130;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____14136;
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
          let tycon_id uu___98_14183 =
            match uu___98_14183 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____14185,uu____14186) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____14196,uu____14197,uu____14198) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____14208,uu____14209,uu____14210) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____14240,uu____14241,uu____14242) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____14284) ->
                let uu____14285 =
                  let uu____14286 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____14286  in
                FStar_Parser_AST.mk_term uu____14285 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____14288 =
                  let uu____14289 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____14289  in
                FStar_Parser_AST.mk_term uu____14288 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____14291) ->
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
              | uu____14314 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____14320 =
                     let uu____14321 =
                       let uu____14328 = binder_to_term b  in
                       (out, uu____14328, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____14321  in
                   FStar_Parser_AST.mk_term uu____14320
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___99_14338 =
            match uu___99_14338 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____14393  ->
                       match uu____14393 with
                       | (x,t,uu____14404) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated
                                ((FStar_Syntax_Util.mangle_field_name x), t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____14410 =
                    let uu____14411 =
                      let uu____14412 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____14412  in
                    FStar_Parser_AST.mk_term uu____14411
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____14410 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let uu____14416 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____14443  ->
                          match uu____14443 with
                          | (x,uu____14453,uu____14454) ->
                              FStar_Syntax_Util.unmangle_field_name x))
                   in
                ((FStar_Parser_AST.TyconVariant
                    (id1, parms, kopt,
                      [(constrName, (FStar_Pervasives_Native.Some constrTyp),
                         FStar_Pervasives_Native.None, false)])),
                  uu____14416)
            | uu____14507 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___100_14538 =
            match uu___100_14538 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____14562 = typars_of_binders _env binders  in
                (match uu____14562 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____14608 =
                         let uu____14609 =
                           let uu____14610 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____14610  in
                         FStar_Parser_AST.mk_term uu____14609
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____14608 binders  in
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
            | uu____14623 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____14667 =
              FStar_List.fold_left
                (fun uu____14707  ->
                   fun uu____14708  ->
                     match (uu____14707, uu____14708) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____14799 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____14799 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____14667 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____14912 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____14912
                | uu____14913 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____14921 = desugar_abstract_tc quals env [] tc  in
              (match uu____14921 with
               | (uu____14934,uu____14935,se,uu____14937) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____14940,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____14957 =
                                 let uu____14958 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____14958  in
                               if uu____14957
                               then
                                 let uu____14959 =
                                   let uu____14964 =
                                     let uu____14965 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____14965
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____14964)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____14959
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
                           | uu____14972 ->
                               let uu____14973 =
                                 let uu____14976 =
                                   let uu____14977 =
                                     let uu____14990 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____14990)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____14977
                                    in
                                 FStar_Syntax_Syntax.mk uu____14976  in
                               uu____14973 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___133_14994 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___133_14994.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___133_14994.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___133_14994.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____14997 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____15000 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____15000
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____15015 = typars_of_binders env binders  in
              (match uu____15015 with
               | (env',typars) ->
                   let k =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____15051 =
                           FStar_Util.for_some
                             (fun uu___101_15053  ->
                                match uu___101_15053 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____15054 -> false) quals
                            in
                         if uu____15051
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Util.ktype
                     | FStar_Pervasives_Native.Some k -> desugar_term env' k
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____15061 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___102_15065  ->
                               match uu___102_15065 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____15066 -> false))
                        in
                     if uu____15061
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____15075 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____15075
                     then
                       let uu____15078 =
                         let uu____15085 =
                           let uu____15086 = unparen t  in
                           uu____15086.FStar_Parser_AST.tm  in
                         match uu____15085 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____15107 =
                               match FStar_List.rev args with
                               | (last_arg,uu____15137)::args_rev ->
                                   let uu____15149 =
                                     let uu____15150 = unparen last_arg  in
                                     uu____15150.FStar_Parser_AST.tm  in
                                   (match uu____15149 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____15178 -> ([], args))
                               | uu____15187 -> ([], args)  in
                             (match uu____15107 with
                              | (cattributes,args1) ->
                                  let uu____15226 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____15226))
                         | uu____15237 -> (t, [])  in
                       match uu____15078 with
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
                                  (fun uu___103_15259  ->
                                     match uu___103_15259 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____15260 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____15271)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____15295 = tycon_record_as_variant trec  in
              (match uu____15295 with
               | (t,fs) ->
                   let uu____15312 =
                     let uu____15315 =
                       let uu____15316 =
                         let uu____15325 =
                           let uu____15328 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____15328  in
                         (uu____15325, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____15316  in
                     uu____15315 :: quals  in
                   desugar_tycon env d uu____15312 [t])
          | uu____15333::uu____15334 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____15495 = et  in
                match uu____15495 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____15720 ->
                         let trec = tc  in
                         let uu____15744 = tycon_record_as_variant trec  in
                         (match uu____15744 with
                          | (t,fs) ->
                              let uu____15803 =
                                let uu____15806 =
                                  let uu____15807 =
                                    let uu____15816 =
                                      let uu____15819 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____15819  in
                                    (uu____15816, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____15807
                                   in
                                uu____15806 :: quals1  in
                              collect_tcs uu____15803 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____15906 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____15906 with
                          | (env2,uu____15966,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____16115 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____16115 with
                          | (env2,uu____16175,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____16300 ->
                         failwith "Unrecognized mutual type definition")
                 in
              let uu____16347 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____16347 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___105_16858  ->
                             match uu___105_16858 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____16925,uu____16926);
                                    FStar_Syntax_Syntax.sigrng = uu____16927;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____16928;
                                    FStar_Syntax_Syntax.sigmeta = uu____16929;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____16930;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____16991 =
                                     typars_of_binders env1 binders  in
                                   match uu____16991 with
                                   | (env2,tpars1) ->
                                       let uu____17022 =
                                         push_tparams env2 tpars1  in
                                       (match uu____17022 with
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
                                 let uu____17055 =
                                   let uu____17076 =
                                     mk_typ_abbrev id1 uvs tpars k t1 
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____17076)
                                    in
                                 [uu____17055]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____17144);
                                    FStar_Syntax_Syntax.sigrng = uu____17145;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____17147;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____17148;_},constrs,tconstr,quals1)
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
                                 let uu____17244 = push_tparams env1 tpars
                                    in
                                 (match uu____17244 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____17321  ->
                                             match uu____17321 with
                                             | (x,uu____17335) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____17343 =
                                        let uu____17372 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____17486  ->
                                                  match uu____17486 with
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
                                                        let uu____17542 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____17542
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
                                                                uu___104_17553
                                                                 ->
                                                                match uu___104_17553
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____17565
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____17573 =
                                                        let uu____17594 =
                                                          let uu____17595 =
                                                            let uu____17596 =
                                                              let uu____17611
                                                                =
                                                                let uu____17614
                                                                  =
                                                                  let uu____17617
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____17617
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____17614
                                                                 in
                                                              (name, univs1,
                                                                uu____17611,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____17596
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____17595;
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
                                                          uu____17594)
                                                         in
                                                      (name, uu____17573)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____17372
                                         in
                                      (match uu____17343 with
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
                             | uu____17856 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____17988  ->
                             match uu____17988 with
                             | (name_doc,uu____18016,uu____18017) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____18097  ->
                             match uu____18097 with
                             | (uu____18118,uu____18119,se) -> se))
                      in
                   let uu____18149 =
                     let uu____18156 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____18156 rng
                      in
                   (match uu____18149 with
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
                               (fun uu____18222  ->
                                  match uu____18222 with
                                  | (uu____18245,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____18296,tps,k,uu____18299,constrs)
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
                                  | uu____18318 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____18335  ->
                                 match uu____18335 with
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
      let uu____18370 =
        FStar_List.fold_left
          (fun uu____18393  ->
             fun b  ->
               match uu____18393 with
               | (env1,binders1) ->
                   let uu____18413 = desugar_binder env1 b  in
                   (match uu____18413 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____18430 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____18430 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____18447 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____18370 with
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
          let uu____18492 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___106_18497  ->
                    match uu___106_18497 with
                    | FStar_Syntax_Syntax.Reflectable uu____18498 -> true
                    | uu____18499 -> false))
             in
          if uu____18492
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
                  let uu____18605 = desugar_binders monad_env eff_binders  in
                  match uu____18605 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let for_free =
                        let uu____18626 =
                          let uu____18627 =
                            let uu____18634 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____18634  in
                          FStar_List.length uu____18627  in
                        uu____18626 = (Prims.parse_int "1")  in
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
                            (uu____18676,(FStar_Parser_AST.TyconAbbrev
                                          (name,uu____18678,uu____18679,uu____18680),uu____18681)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____18714 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____18715 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____18727 = name_of_eff_decl decl  in
                             FStar_List.mem uu____18727 mandatory_members)
                          eff_decls
                         in
                      (match uu____18715 with
                       | (mandatory_members_decls,actions) ->
                           let uu____18744 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____18773  ->
                                     fun decl  ->
                                       match uu____18773 with
                                       | (env2,out) ->
                                           let uu____18793 =
                                             desugar_decl env2 decl  in
                                           (match uu____18793 with
                                            | (env3,ses) ->
                                                let uu____18806 =
                                                  let uu____18809 =
                                                    FStar_List.hd ses  in
                                                  uu____18809 :: out  in
                                                (env3, uu____18806)))
                                  (env1, []))
                              in
                           (match uu____18744 with
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
                                              (uu____18877,(FStar_Parser_AST.TyconAbbrev
                                                            (name,action_params,uu____18880,
                                                             {
                                                               FStar_Parser_AST.tm
                                                                 =
                                                                 FStar_Parser_AST.Construct
                                                                 (uu____18881,
                                                                  (def,uu____18883)::
                                                                  (cps_type,uu____18885)::[]);
                                                               FStar_Parser_AST.range
                                                                 =
                                                                 uu____18886;
                                                               FStar_Parser_AST.level
                                                                 =
                                                                 uu____18887;_}),doc1)::[])
                                              when Prims.op_Negation for_free
                                              ->
                                              let uu____18939 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____18939 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____18959 =
                                                     let uu____18960 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____18961 =
                                                       let uu____18962 =
                                                         desugar_term env3
                                                           def
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____18962
                                                        in
                                                     let uu____18967 =
                                                       let uu____18968 =
                                                         desugar_typ env3
                                                           cps_type
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____18968
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____18960;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____18961;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____18967
                                                     }  in
                                                   (uu____18959, doc1))
                                          | FStar_Parser_AST.Tycon
                                              (uu____18975,(FStar_Parser_AST.TyconAbbrev
                                                            (name,action_params,uu____18978,defn),doc1)::[])
                                              when for_free ->
                                              let uu____19013 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____19013 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____19033 =
                                                     let uu____19034 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____19035 =
                                                       let uu____19036 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____19036
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____19034;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____19035;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____19033, doc1))
                                          | uu____19043 ->
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
                                  let uu____19073 =
                                    let uu____19074 =
                                      FStar_Syntax_DsEnv.fail_or env2
                                        (FStar_Syntax_DsEnv.try_lookup_definition
                                           env2) l
                                       in
                                    FStar_All.pipe_left
                                      (FStar_Syntax_Subst.close binders1)
                                      uu____19074
                                     in
                                  ([], uu____19073)  in
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
                                      let uu____19091 =
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      ([], uu____19091)  in
                                    let uu____19098 =
                                      let uu____19099 =
                                        let uu____19100 =
                                          let uu____19101 = lookup1 "repr"
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____19101
                                           in
                                        let uu____19110 = lookup1 "return"
                                           in
                                        let uu____19111 = lookup1 "bind"  in
                                        let uu____19112 =
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
                                            uu____19100;
                                          FStar_Syntax_Syntax.return_repr =
                                            uu____19110;
                                          FStar_Syntax_Syntax.bind_repr =
                                            uu____19111;
                                          FStar_Syntax_Syntax.actions =
                                            actions1;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            uu____19112
                                        }  in
                                      FStar_Syntax_Syntax.Sig_new_effect_for_free
                                        uu____19099
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____19098;
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
                                         (fun uu___107_19118  ->
                                            match uu___107_19118 with
                                            | FStar_Syntax_Syntax.Reifiable 
                                                -> true
                                            | FStar_Syntax_Syntax.Reflectable
                                                uu____19119 -> true
                                            | uu____19120 -> false)
                                         qualifiers
                                        in
                                     let un_ts =
                                       ([], FStar_Syntax_Syntax.tun)  in
                                     let uu____19130 =
                                       let uu____19131 =
                                         let uu____19132 =
                                           lookup1 "return_wp"  in
                                         let uu____19133 = lookup1 "bind_wp"
                                            in
                                         let uu____19134 =
                                           lookup1 "if_then_else"  in
                                         let uu____19135 = lookup1 "ite_wp"
                                            in
                                         let uu____19136 = lookup1 "stronger"
                                            in
                                         let uu____19137 = lookup1 "close_wp"
                                            in
                                         let uu____19138 = lookup1 "assert_p"
                                            in
                                         let uu____19139 = lookup1 "assume_p"
                                            in
                                         let uu____19140 = lookup1 "null_wp"
                                            in
                                         let uu____19141 = lookup1 "trivial"
                                            in
                                         let uu____19142 =
                                           if rr
                                           then
                                             let uu____19143 = lookup1 "repr"
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.snd
                                               uu____19143
                                           else FStar_Syntax_Syntax.tun  in
                                         let uu____19159 =
                                           if rr
                                           then lookup1 "return"
                                           else un_ts  in
                                         let uu____19161 =
                                           if rr
                                           then lookup1 "bind"
                                           else un_ts  in
                                         let uu____19163 =
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
                                             uu____19132;
                                           FStar_Syntax_Syntax.bind_wp =
                                             uu____19133;
                                           FStar_Syntax_Syntax.if_then_else =
                                             uu____19134;
                                           FStar_Syntax_Syntax.ite_wp =
                                             uu____19135;
                                           FStar_Syntax_Syntax.stronger =
                                             uu____19136;
                                           FStar_Syntax_Syntax.close_wp =
                                             uu____19137;
                                           FStar_Syntax_Syntax.assert_p =
                                             uu____19138;
                                           FStar_Syntax_Syntax.assume_p =
                                             uu____19139;
                                           FStar_Syntax_Syntax.null_wp =
                                             uu____19140;
                                           FStar_Syntax_Syntax.trivial =
                                             uu____19141;
                                           FStar_Syntax_Syntax.repr =
                                             uu____19142;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____19159;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____19161;
                                           FStar_Syntax_Syntax.actions =
                                             actions1;
                                           FStar_Syntax_Syntax.eff_attrs =
                                             uu____19163
                                         }  in
                                       FStar_Syntax_Syntax.Sig_new_effect
                                         uu____19131
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         uu____19130;
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
                                          fun uu____19189  ->
                                            match uu____19189 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____19203 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____19203
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
                let uu____19227 = desugar_binders env1 eff_binders  in
                match uu____19227 with
                | (env2,binders) ->
                    let uu____19246 =
                      let uu____19265 = head_and_args defn  in
                      match uu____19265 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____19310 ->
                                let uu____19311 =
                                  let uu____19316 =
                                    let uu____19317 =
                                      let uu____19318 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.strcat uu____19318 " not found"
                                       in
                                    Prims.strcat "Effect " uu____19317  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____19316)
                                   in
                                FStar_Errors.raise_error uu____19311
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____19320 =
                            match FStar_List.rev args with
                            | (last_arg,uu____19350)::args_rev ->
                                let uu____19362 =
                                  let uu____19363 = unparen last_arg  in
                                  uu____19363.FStar_Parser_AST.tm  in
                                (match uu____19362 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____19391 -> ([], args))
                            | uu____19400 -> ([], args)  in
                          (match uu____19320 with
                           | (cattributes,args1) ->
                               let uu____19451 = desugar_args env2 args1  in
                               let uu____19460 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____19451, uu____19460))
                       in
                    (match uu____19246 with
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
                          (let uu____19516 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____19516 with
                           | (ed_binders,uu____19530,ed_binders_opening) ->
                               let sub1 uu____19541 =
                                 match uu____19541 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____19555 =
                                         FStar_Syntax_Subst.shift_subst
                                           (FStar_List.length us)
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____19555 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____19559 =
                                       let uu____19560 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____19560)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____19559
                                  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____19565 =
                                   let uu____19566 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____19566
                                    in
                                 let uu____19577 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____19578 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____19579 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____19580 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____19581 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____19582 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____19583 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____19584 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____19585 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____19586 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____19587 =
                                   let uu____19588 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____19588
                                    in
                                 let uu____19599 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____19600 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____19601 =
                                   FStar_List.map
                                     (fun action  ->
                                        let uu____19609 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____19610 =
                                          let uu____19611 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____19611
                                           in
                                        let uu____19622 =
                                          let uu____19623 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____19623
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____19609;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____19610;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____19622
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
                                     uu____19565;
                                   FStar_Syntax_Syntax.ret_wp = uu____19577;
                                   FStar_Syntax_Syntax.bind_wp = uu____19578;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____19579;
                                   FStar_Syntax_Syntax.ite_wp = uu____19580;
                                   FStar_Syntax_Syntax.stronger = uu____19581;
                                   FStar_Syntax_Syntax.close_wp = uu____19582;
                                   FStar_Syntax_Syntax.assert_p = uu____19583;
                                   FStar_Syntax_Syntax.assume_p = uu____19584;
                                   FStar_Syntax_Syntax.null_wp = uu____19585;
                                   FStar_Syntax_Syntax.trivial = uu____19586;
                                   FStar_Syntax_Syntax.repr = uu____19587;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____19599;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____19600;
                                   FStar_Syntax_Syntax.actions = uu____19601;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____19636 =
                                     let uu____19637 =
                                       let uu____19644 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____19644
                                        in
                                     FStar_List.length uu____19637  in
                                   uu____19636 = (Prims.parse_int "1")  in
                                 let uu____19673 =
                                   let uu____19676 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____19676 quals  in
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
                                   FStar_Syntax_Syntax.sigquals = uu____19673;
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
                                             let uu____19696 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____19696
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____19698 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____19698
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
    let uu____19713 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____19713 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.strcat "  " (Prims.strcat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____19764 ->
              let uu____19765 =
                let uu____19766 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____19766
                 in
              Prims.strcat "\n  " uu____19765
          | uu____19767 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____19780  ->
               match uu____19780 with
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
          let uu____19798 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____19798
            FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____19800 =
          let uu____19809 = FStar_Syntax_Syntax.as_arg arg  in [uu____19809]
           in
        FStar_Syntax_Util.mk_app fv uu____19800

and (desugar_decl :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      let uu____19816 = desugar_decl_noattrs env d  in
      match uu____19816 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____19836 = mk_comment_attr d  in uu____19836 :: attrs1  in
          let s =
            FStar_List.fold_left
              (fun s  ->
                 fun a  ->
                   let uu____19847 =
                     let uu____19848 = FStar_Syntax_Print.term_to_string a
                        in
                     Prims.strcat "; " uu____19848  in
                   Prims.strcat s uu____19847) "" attrs2
             in
          let uu____19849 =
            FStar_List.map
              (fun sigelt  ->
                 let uu___134_19855 = sigelt  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___134_19855.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___134_19855.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___134_19855.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___134_19855.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs = attrs2
                 }) sigelts
             in
          (env1, uu____19849)

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
      | FStar_Parser_AST.Fsdoc uu____19881 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____19897 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____19897, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals  in
          let tcs1 =
            FStar_List.map
              (fun uu____19936  ->
                 match uu____19936 with | (x,uu____19944) -> x) tcs
             in
          let uu____19949 =
            FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals
             in
          desugar_tycon env d uu____19949 tcs1
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals  in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____19971;
                    FStar_Parser_AST.prange = uu____19972;_},uu____19973)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____19982;
                    FStar_Parser_AST.prange = uu____19983;_},uu____19984)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____19999;
                         FStar_Parser_AST.prange = uu____20000;_},uu____20001);
                    FStar_Parser_AST.prange = uu____20002;_},uu____20003)::[]
                   -> false
               | (p,uu____20031)::[] ->
                   let uu____20040 = is_app_pattern p  in
                   Prims.op_Negation uu____20040
               | uu____20041 -> false)
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
            let uu____20114 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____20114 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____20126 =
                     let uu____20127 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____20127.FStar_Syntax_Syntax.n  in
                   match uu____20126 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____20135) ->
                       let fvs =
                         FStar_All.pipe_right
                           (FStar_Pervasives_Native.snd lbs)
                           (FStar_List.map
                              (fun lb  ->
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname))
                          in
                       let quals1 =
                         match quals with
                         | uu____20168::uu____20169 ->
                             FStar_List.map
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____20172 ->
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.collect
                                  (fun uu___108_20187  ->
                                     match uu___108_20187 with
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inl uu____20190;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____20191;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____20192;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____20193;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____20194;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____20195;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____20196;_}
                                         -> []
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____20208;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____20209;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____20210;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____20211;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____20212;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____20213;_}
                                         ->
                                         FStar_Syntax_DsEnv.lookup_letbinding_quals
                                           env
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                          in
                       let quals2 =
                         let uu____20227 =
                           FStar_All.pipe_right lets1
                             (FStar_Util.for_some
                                (fun uu____20258  ->
                                   match uu____20258 with
                                   | (uu____20271,(uu____20272,t)) ->
                                       t.FStar_Parser_AST.level =
                                         FStar_Parser_AST.Formula))
                            in
                         if uu____20227
                         then FStar_Syntax_Syntax.Logic :: quals1
                         else quals1  in
                       let lbs1 =
                         let uu____20296 =
                           FStar_All.pipe_right quals2
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract)
                            in
                         if uu____20296
                         then
                           let uu____20305 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu___135_20319 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___136_20321 = fv  in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___136_20321.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___136_20321.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___135_20319.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___135_20319.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___135_20319.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___135_20319.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___135_20319.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___135_20319.FStar_Syntax_Syntax.lbpos)
                                     }))
                              in
                           ((FStar_Pervasives_Native.fst lbs), uu____20305)
                         else lbs  in
                       let names1 =
                         FStar_All.pipe_right fvs
                           (FStar_List.map
                              (fun fv  ->
                                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                          in
                       let attrs =
                         FStar_List.map (desugar_term env)
                           d.FStar_Parser_AST.attrs
                          in
                       let s =
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_let (lbs1, names1));
                           FStar_Syntax_Syntax.sigrng =
                             (d.FStar_Parser_AST.drange);
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
                   | uu____20356 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____20362 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____20381 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____20362 with
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
                       let uu___137_20417 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___137_20417.FStar_Parser_AST.prange)
                       }
                   | uu____20424 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___138_20431 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___138_20431.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___138_20431.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___138_20431.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____20463 id1 =
                   match uu____20463 with
                   | (env1,ses) ->
                       let main =
                         let uu____20484 =
                           let uu____20485 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____20485  in
                         FStar_Parser_AST.mk_term uu____20484
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
                       let uu____20535 = desugar_decl env1 id_decl  in
                       (match uu____20535 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____20553 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____20553 FStar_Util.set_elements
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
            let uu____20584 = close_fun env t  in
            desugar_term env uu____20584  in
          let quals1 =
            let uu____20588 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____20588
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let se =
            let uu____20594 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____20594;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in
          let env2 =
            FStar_Syntax_DsEnv.push_doc env1 lid d.FStar_Parser_AST.doc  in
          (env2, [se])
      | FStar_Parser_AST.Exception (id1,FStar_Pervasives_Native.None ) ->
          let uu____20606 =
            FStar_Syntax_DsEnv.fail_or env
              (FStar_Syntax_DsEnv.try_lookup_lid env)
              FStar_Parser_Const.exn_lid
             in
          (match uu____20606 with
           | (t,uu____20620) ->
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
            let uu____20654 =
              let uu____20661 = FStar_Syntax_Syntax.null_binder t  in
              [uu____20661]  in
            let uu____20662 =
              let uu____20665 =
                let uu____20666 =
                  FStar_Syntax_DsEnv.fail_or env
                    (FStar_Syntax_DsEnv.try_lookup_lid env)
                    FStar_Parser_Const.exn_lid
                   in
                FStar_Pervasives_Native.fst uu____20666  in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____20665
               in
            FStar_Syntax_Util.arrow uu____20654 uu____20662  in
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
            let uu____20729 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____20729 with
            | FStar_Pervasives_Native.None  ->
                let uu____20732 =
                  let uu____20737 =
                    let uu____20738 =
                      let uu____20739 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.strcat uu____20739 " not found"  in
                    Prims.strcat "Effect name " uu____20738  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____20737)  in
                FStar_Errors.raise_error uu____20732
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____20743 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____20785 =
                  let uu____20794 =
                    let uu____20801 = desugar_term env t  in
                    ([], uu____20801)  in
                  FStar_Pervasives_Native.Some uu____20794  in
                (uu____20785, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____20834 =
                  let uu____20843 =
                    let uu____20850 = desugar_term env wp  in
                    ([], uu____20850)  in
                  FStar_Pervasives_Native.Some uu____20843  in
                let uu____20859 =
                  let uu____20868 =
                    let uu____20875 = desugar_term env t  in
                    ([], uu____20875)  in
                  FStar_Pervasives_Native.Some uu____20868  in
                (uu____20834, uu____20859)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____20901 =
                  let uu____20910 =
                    let uu____20917 = desugar_term env t  in
                    ([], uu____20917)  in
                  FStar_Pervasives_Native.Some uu____20910  in
                (FStar_Pervasives_Native.None, uu____20901)
             in
          (match uu____20743 with
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
      let uu____21010 =
        FStar_List.fold_left
          (fun uu____21030  ->
             fun d  ->
               match uu____21030 with
               | (env1,sigelts) ->
                   let uu____21050 = desugar_decl env1 d  in
                   (match uu____21050 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____21010 with
      | (env1,sigelts) ->
          let rec forward acc uu___110_21091 =
            match uu___110_21091 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____21105,FStar_Syntax_Syntax.Sig_let uu____21106) ->
                     let uu____21119 =
                       let uu____21122 =
                         let uu___139_21123 = se2  in
                         let uu____21124 =
                           let uu____21127 =
                             FStar_List.filter
                               (fun uu___109_21141  ->
                                  match uu___109_21141 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____21145;
                                           FStar_Syntax_Syntax.vars =
                                             uu____21146;_},uu____21147);
                                      FStar_Syntax_Syntax.pos = uu____21148;
                                      FStar_Syntax_Syntax.vars = uu____21149;_}
                                      when
                                      let uu____21172 =
                                        let uu____21173 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____21173
                                         in
                                      uu____21172 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____21174 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____21127
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___139_21123.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___139_21123.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___139_21123.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___139_21123.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____21124
                         }  in
                       uu____21122 :: se1 :: acc  in
                     forward uu____21119 sigelts1
                 | uu____21179 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____21187 = forward [] sigelts  in (env1, uu____21187)
  
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
          | (FStar_Pervasives_Native.None ,uu____21238) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____21242;
               FStar_Syntax_Syntax.exports = uu____21243;
               FStar_Syntax_Syntax.is_interface = uu____21244;_},FStar_Parser_AST.Module
             (current_lid,uu____21246)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____21254) ->
              let uu____21257 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____21257
           in
        let uu____21262 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____21298 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____21298, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____21315 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____21315, mname, decls, false)
           in
        match uu____21262 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____21345 = desugar_decls env2 decls  in
            (match uu____21345 with
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
          let uu____21399 =
            (FStar_Options.interactive ()) &&
              (let uu____21401 =
                 let uu____21402 =
                   let uu____21403 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____21403  in
                 FStar_Util.get_file_extension uu____21402  in
               FStar_List.mem uu____21401 ["fsti"; "fsi"])
             in
          if uu____21399 then as_interface m else m  in
        let uu____21407 = desugar_modul_common curmod env m1  in
        match uu____21407 with
        | (x,y,pop_when_done) ->
            (if pop_when_done
             then (let uu____21422 = FStar_Syntax_DsEnv.pop ()  in ())
             else ();
             (x, y))
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul ->
      (env_t,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun m  ->
      let uu____21438 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____21438 with
      | (env1,modul,pop_when_done) ->
          let uu____21452 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____21452 with
           | (env2,modul1) ->
               ((let uu____21464 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____21464
                 then
                   let uu____21465 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____21465
                 else ());
                (let uu____21467 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____21467, modul1))))
  
let (ast_modul_to_modul :
  FStar_Parser_AST.modul ->
    FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun env  ->
      let uu____21481 = desugar_modul env modul  in
      match uu____21481 with | (env1,modul1) -> (modul1, env1)
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      let uu____21508 = desugar_decls env decls  in
      match uu____21508 with | (env1,sigelts) -> (sigelts, env1)
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        let uu____21546 = desugar_partial_modul modul env a_modul  in
        match uu____21546 with | (env1,modul1) -> (modul1, env1)
  
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
              | uu____21620 ->
                  let t =
                    let uu____21628 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____21628  in
                  let uu____21637 =
                    let uu____21638 = FStar_Syntax_Subst.compress t  in
                    uu____21638.FStar_Syntax_Syntax.n  in
                  (match uu____21637 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____21648,uu____21649)
                       -> bs1
                   | uu____21670 -> failwith "Impossible")
               in
            let uu____21677 =
              let uu____21684 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____21684
                FStar_Syntax_Syntax.t_unit
               in
            match uu____21677 with
            | (binders,uu____21686,binders_opening) ->
                let erase_term t =
                  let uu____21692 =
                    let uu____21693 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____21693  in
                  FStar_Syntax_Subst.close binders uu____21692  in
                let erase_tscheme uu____21709 =
                  match uu____21709 with
                  | (us,t) ->
                      let t1 =
                        let uu____21729 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____21729 t  in
                      let uu____21732 =
                        let uu____21733 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____21733  in
                      ([], uu____21732)
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
                    | uu____21762 ->
                        let bs =
                          let uu____21770 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____21770  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____21800 =
                          let uu____21801 =
                            let uu____21804 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____21804  in
                          uu____21801.FStar_Syntax_Syntax.n  in
                        (match uu____21800 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____21812,uu____21813) -> bs1
                         | uu____21834 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____21845 =
                      let uu____21846 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____21846  in
                    FStar_Syntax_Subst.close binders uu____21845  in
                  let uu___140_21847 = action  in
                  let uu____21848 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____21849 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___140_21847.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___140_21847.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____21848;
                    FStar_Syntax_Syntax.action_typ = uu____21849
                  }  in
                let uu___141_21850 = ed  in
                let uu____21851 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____21852 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____21853 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____21854 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____21855 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____21856 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____21857 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____21858 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____21859 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____21860 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____21861 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____21862 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____21863 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____21864 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____21865 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____21866 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___141_21850.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___141_21850.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____21851;
                  FStar_Syntax_Syntax.signature = uu____21852;
                  FStar_Syntax_Syntax.ret_wp = uu____21853;
                  FStar_Syntax_Syntax.bind_wp = uu____21854;
                  FStar_Syntax_Syntax.if_then_else = uu____21855;
                  FStar_Syntax_Syntax.ite_wp = uu____21856;
                  FStar_Syntax_Syntax.stronger = uu____21857;
                  FStar_Syntax_Syntax.close_wp = uu____21858;
                  FStar_Syntax_Syntax.assert_p = uu____21859;
                  FStar_Syntax_Syntax.assume_p = uu____21860;
                  FStar_Syntax_Syntax.null_wp = uu____21861;
                  FStar_Syntax_Syntax.trivial = uu____21862;
                  FStar_Syntax_Syntax.repr = uu____21863;
                  FStar_Syntax_Syntax.return_repr = uu____21864;
                  FStar_Syntax_Syntax.bind_repr = uu____21865;
                  FStar_Syntax_Syntax.actions = uu____21866;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___141_21850.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___142_21878 = se  in
                  let uu____21879 =
                    let uu____21880 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____21880  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____21879;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___142_21878.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___142_21878.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___142_21878.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___142_21878.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___143_21884 = se  in
                  let uu____21885 =
                    let uu____21886 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____21886
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____21885;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___143_21884.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___143_21884.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___143_21884.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___143_21884.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____21888 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____21889 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____21889 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____21901 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____21901
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____21903 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____21903)
  