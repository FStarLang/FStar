open Prims
type annotated_pat =
  (FStar_Syntax_Syntax.pat,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.typ)
                             FStar_Pervasives_Native.tuple2 Prims.list)
    FStar_Pervasives_Native.tuple2
let (desugar_disjunctive_pattern :
  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t,(FStar_Syntax_Syntax.bv,
                                                             FStar_Syntax_Syntax.term'
                                                               FStar_Syntax_Syntax.syntax)
                                                             FStar_Pervasives_Native.tuple2
                                                             Prims.list)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.branch Prims.list)
  =
  fun annotated_pats  ->
    fun when_opt  ->
      fun branch1  ->
        FStar_All.pipe_right annotated_pats
          (FStar_List.map
             (fun uu____104  ->
                match uu____104 with
                | (pat,annots) ->
                    let branch2 =
                      FStar_List.fold_left
                        (fun br  ->
                           fun uu____159  ->
                             match uu____159 with
                             | (bv,ty) ->
                                 let lb =
                                   let uu____177 =
                                     FStar_Syntax_Syntax.bv_to_name bv  in
                                   FStar_Syntax_Util.mk_letbinding
                                     (FStar_Util.Inl bv) [] ty
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____177 [] br.FStar_Syntax_Syntax.pos
                                    in
                                 let branch2 =
                                   let uu____183 =
                                     let uu____184 =
                                       FStar_Syntax_Syntax.mk_binder bv  in
                                     [uu____184]  in
                                   FStar_Syntax_Subst.close uu____183 branch1
                                    in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((false, [lb]), branch2))
                                   FStar_Pervasives_Native.None
                                   br.FStar_Syntax_Syntax.pos) branch1 annots
                       in
                    FStar_Syntax_Util.branch (pat, when_opt, branch2)))
  
let (trans_qual :
  FStar_Range.range ->
    FStar_Ident.lident FStar_Pervasives_Native.option ->
      FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier)
  =
  fun r  ->
    fun maybe_effect_id  ->
      fun uu___248_237  ->
        match uu___248_237 with
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
  fun uu___249_246  ->
    match uu___249_246 with
    | FStar_Parser_AST.SetOptions s -> FStar_Syntax_Syntax.SetOptions s
    | FStar_Parser_AST.ResetOptions sopt ->
        FStar_Syntax_Syntax.ResetOptions sopt
    | FStar_Parser_AST.PushOptions sopt ->
        FStar_Syntax_Syntax.PushOptions sopt
    | FStar_Parser_AST.PopOptions  -> FStar_Syntax_Syntax.PopOptions
    | FStar_Parser_AST.LightOff  -> FStar_Syntax_Syntax.LightOff
  
let (as_imp :
  FStar_Parser_AST.imp ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
  =
  fun uu___250_260  ->
    match uu___250_260 with
    | FStar_Parser_AST.Hash  ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | uu____263 -> FStar_Pervasives_Native.None
  
let arg_withimp_e :
  'Auu____270 .
    FStar_Parser_AST.imp ->
      'Auu____270 ->
        ('Auu____270,FStar_Syntax_Syntax.arg_qualifier
                       FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2
  = fun imp  -> fun t  -> (t, (as_imp imp)) 
let arg_withimp_t :
  'Auu____295 .
    FStar_Parser_AST.imp ->
      'Auu____295 ->
        ('Auu____295,FStar_Syntax_Syntax.arg_qualifier
                       FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2
  =
  fun imp  ->
    fun t  ->
      match imp with
      | FStar_Parser_AST.Hash  ->
          (t, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag))
      | uu____314 -> (t, FStar_Pervasives_Native.None)
  
let (contains_binder : FStar_Parser_AST.binder Prims.list -> Prims.bool) =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b  ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____331 -> true
            | uu____336 -> false))
  
let rec (unparen : FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____343 -> t
  
let (tm_type_z : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____349 =
      let uu____350 = FStar_Ident.lid_of_path ["Type0"] r  in
      FStar_Parser_AST.Name uu____350  in
    FStar_Parser_AST.mk_term uu____349 r FStar_Parser_AST.Kind
  
let (tm_type : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____356 =
      let uu____357 = FStar_Ident.lid_of_path ["Type"] r  in
      FStar_Parser_AST.Name uu____357  in
    FStar_Parser_AST.mk_term uu____356 r FStar_Parser_AST.Kind
  
let rec (is_comp_type :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____368 =
        let uu____369 = unparen t  in uu____369.FStar_Parser_AST.tm  in
      match uu____368 with
      | FStar_Parser_AST.Name l ->
          let uu____371 = FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
          FStar_All.pipe_right uu____371 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l,uu____377) ->
          let uu____390 = FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
          FStar_All.pipe_right uu____390 FStar_Option.isSome
      | FStar_Parser_AST.App (head1,uu____396,uu____397) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,uu____400,uu____401) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____406,t1) -> is_comp_type env t1
      | uu____408 -> false
  
let (unit_ty : FStar_Parser_AST.term) =
  FStar_Parser_AST.mk_term
    (FStar_Parser_AST.Name FStar_Parser_Const.unit_lid)
    FStar_Range.dummyRange FStar_Parser_AST.Type_level
  
let (compile_op_lid :
  Prims.int -> Prims.string -> FStar_Range.range -> FStar_Ident.lident) =
  fun n1  ->
    fun s  ->
      fun r  ->
        let uu____424 =
          let uu____427 =
            let uu____428 =
              let uu____433 = FStar_Parser_AST.compile_op n1 s r  in
              (uu____433, r)  in
            FStar_Ident.mk_ident uu____428  in
          [uu____427]  in
        FStar_All.pipe_right uu____424 FStar_Ident.lid_of_ids
  
let op_as_term :
  'Auu____446 .
    FStar_Syntax_DsEnv.env ->
      Prims.int ->
        'Auu____446 ->
          FStar_Ident.ident ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun arity  ->
      fun rng  ->
        fun op  ->
          let r l dd =
            let uu____482 =
              let uu____483 =
                let uu____484 =
                  FStar_Ident.set_lid_range l op.FStar_Ident.idRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____484 dd
                  FStar_Pervasives_Native.None
                 in
              FStar_All.pipe_right uu____483 FStar_Syntax_Syntax.fv_to_tm  in
            FStar_Pervasives_Native.Some uu____482  in
          let fallback uu____492 =
            let uu____493 = FStar_Ident.text_of_id op  in
            match uu____493 with
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
            | "-" when arity = (Prims.parse_int "1") ->
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
                let uu____496 = FStar_Options.ml_ish ()  in
                if uu____496
                then
                  r FStar_Parser_Const.list_append_lid
                    (FStar_Syntax_Syntax.Delta_equational_at_level
                       (Prims.parse_int "2"))
                else
                  r FStar_Parser_Const.list_tot_append_lid
                    (FStar_Syntax_Syntax.Delta_equational_at_level
                       (Prims.parse_int "2"))
            | "^" ->
                r FStar_Parser_Const.strcat_lid
                  FStar_Syntax_Syntax.delta_equational
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
                     (Prims.parse_int "2"))
            | "==" ->
                r FStar_Parser_Const.eq2_lid
                  (FStar_Syntax_Syntax.Delta_constant_at_level
                     (Prims.parse_int "2"))
            | "<<" ->
                r FStar_Parser_Const.precedes_lid
                  FStar_Syntax_Syntax.delta_constant
            | "/\\" ->
                r FStar_Parser_Const.and_lid
                  (FStar_Syntax_Syntax.Delta_constant_at_level
                     (Prims.parse_int "1"))
            | "\\/" ->
                r FStar_Parser_Const.or_lid
                  (FStar_Syntax_Syntax.Delta_constant_at_level
                     (Prims.parse_int "1"))
            | "==>" ->
                r FStar_Parser_Const.imp_lid
                  (FStar_Syntax_Syntax.Delta_constant_at_level
                     (Prims.parse_int "1"))
            | "<==>" ->
                r FStar_Parser_Const.iff_lid
                  (FStar_Syntax_Syntax.Delta_constant_at_level
                     (Prims.parse_int "2"))
            | uu____500 -> FStar_Pervasives_Native.None  in
          let uu____501 =
            let uu____504 =
              compile_op_lid arity op.FStar_Ident.idText
                op.FStar_Ident.idRange
               in
            FStar_Syntax_DsEnv.try_lookup_lid env uu____504  in
          match uu____501 with
          | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
          | uu____508 -> fallback ()
  
let (sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list)
  =
  fun ftv  ->
    let uu____522 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv
       in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____522
  
let rec (free_type_vars_b :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Syntax_DsEnv.env,FStar_Ident.ident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____569 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____573 = FStar_Syntax_DsEnv.push_bv env x  in
          (match uu____573 with | (env1,uu____585) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____588,term) ->
          let uu____590 = free_type_vars env term  in (env, uu____590)
      | FStar_Parser_AST.TAnnotated (id1,uu____596) ->
          let uu____597 = FStar_Syntax_DsEnv.push_bv env id1  in
          (match uu____597 with | (env1,uu____609) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____613 = free_type_vars env t  in (env, uu____613)

and (free_type_vars :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun t  ->
      let uu____620 =
        let uu____621 = unparen t  in uu____621.FStar_Parser_AST.tm  in
      match uu____620 with
      | FStar_Parser_AST.Labeled uu____624 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____634 = FStar_Syntax_DsEnv.try_lookup_id env a  in
          (match uu____634 with
           | FStar_Pervasives_Native.None  -> [a]
           | uu____639 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____642 -> []
      | FStar_Parser_AST.Uvar uu____643 -> []
      | FStar_Parser_AST.Var uu____644 -> []
      | FStar_Parser_AST.Projector uu____645 -> []
      | FStar_Parser_AST.Discrim uu____650 -> []
      | FStar_Parser_AST.Name uu____651 -> []
      | FStar_Parser_AST.Requires (t1,uu____653) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____659) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____664,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None  -> []
             | FStar_Pervasives_Native.Some t2 -> [t2])
             in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____682,ts) ->
          FStar_List.collect
            (fun uu____703  ->
               match uu____703 with | (t1,uu____711) -> free_type_vars env t1)
            ts
      | FStar_Parser_AST.Op (uu____712,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____720) ->
          let uu____721 = free_type_vars env t1  in
          let uu____724 = free_type_vars env t2  in
          FStar_List.append uu____721 uu____724
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____729 = free_type_vars_b env b  in
          (match uu____729 with
           | (env1,f) ->
               let uu____744 = free_type_vars env1 t1  in
               FStar_List.append f uu____744)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____761 =
            FStar_List.fold_left
              (fun uu____785  ->
                 fun bt  ->
                   match uu____785 with
                   | (env1,free) ->
                       let uu____809 =
                         match bt with
                         | FStar_Util.Inl binder ->
                             free_type_vars_b env1 binder
                         | FStar_Util.Inr t1 ->
                             let uu____824 = free_type_vars env1 body  in
                             (env1, uu____824)
                          in
                       (match uu____809 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____761 with
           | (env1,free) ->
               let uu____853 = free_type_vars env1 body  in
               FStar_List.append free uu____853)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____862 =
            FStar_List.fold_left
              (fun uu____882  ->
                 fun binder  ->
                   match uu____882 with
                   | (env1,free) ->
                       let uu____902 = free_type_vars_b env1 binder  in
                       (match uu____902 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____862 with
           | (env1,free) ->
               let uu____933 = free_type_vars env1 body  in
               FStar_List.append free uu____933)
      | FStar_Parser_AST.Project (t1,uu____937) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.Abs uu____941 -> []
      | FStar_Parser_AST.Let uu____948 -> []
      | FStar_Parser_AST.LetOpen uu____969 -> []
      | FStar_Parser_AST.If uu____974 -> []
      | FStar_Parser_AST.QForall uu____981 -> []
      | FStar_Parser_AST.QExists uu____994 -> []
      | FStar_Parser_AST.Record uu____1007 -> []
      | FStar_Parser_AST.Match uu____1020 -> []
      | FStar_Parser_AST.TryWith uu____1035 -> []
      | FStar_Parser_AST.Bind uu____1050 -> []
      | FStar_Parser_AST.Quote uu____1057 -> []
      | FStar_Parser_AST.VQuote uu____1062 -> []
      | FStar_Parser_AST.Antiquote uu____1063 -> []
      | FStar_Parser_AST.Seq uu____1064 -> []

let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term,(FStar_Parser_AST.term,FStar_Parser_AST.imp)
                             FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let rec aux args t1 =
      let uu____1117 =
        let uu____1118 = unparen t1  in uu____1118.FStar_Parser_AST.tm  in
      match uu____1117 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____1160 -> (t1, args)  in
    aux [] t
  
let (close :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____1184 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1184  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1202 =
                     let uu____1203 =
                       let uu____1208 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____1208)  in
                     FStar_Parser_AST.TAnnotated uu____1203  in
                   FStar_Parser_AST.mk_binder uu____1202
                     x.FStar_Ident.idRange FStar_Parser_AST.Type_level
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
        let uu____1225 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1225  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1243 =
                     let uu____1244 =
                       let uu____1249 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____1249)  in
                     FStar_Parser_AST.TAnnotated uu____1244  in
                   FStar_Parser_AST.mk_binder uu____1243
                     x.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____1251 =
             let uu____1252 = unparen t  in uu____1252.FStar_Parser_AST.tm
              in
           match uu____1251 with
           | FStar_Parser_AST.Product uu____1253 -> t
           | uu____1260 ->
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
      | uu____1296 -> (bs, t)
  
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild uu____1304 -> true
    | FStar_Parser_AST.PatTvar (uu____1307,uu____1308) -> true
    | FStar_Parser_AST.PatVar (uu____1313,uu____1314) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____1320) -> is_var_pattern p1
    | uu____1333 -> false
  
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____1340) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____1353;
           FStar_Parser_AST.prange = uu____1354;_},uu____1355)
        -> true
    | uu____1366 -> false
  
let (replace_unit_pattern :
  FStar_Parser_AST.pattern -> FStar_Parser_AST.pattern) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatConst (FStar_Const.Const_unit ) ->
        FStar_Parser_AST.mk_pattern
          (FStar_Parser_AST.PatAscribed
             ((FStar_Parser_AST.mk_pattern
                 (FStar_Parser_AST.PatWild FStar_Pervasives_Native.None)
                 p.FStar_Parser_AST.prange),
               (unit_ty, FStar_Pervasives_Native.None)))
          p.FStar_Parser_AST.prange
    | uu____1380 -> p
  
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
            let uu____1450 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____1450 with
             | (name,args,uu____1493) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1543);
               FStar_Parser_AST.prange = uu____1544;_},args)
            when is_top_level1 ->
            let uu____1554 =
              let uu____1559 = FStar_Syntax_DsEnv.qualify env id1  in
              FStar_Util.Inr uu____1559  in
            (uu____1554, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1581);
               FStar_Parser_AST.prange = uu____1582;_},args)
            -> ((FStar_Util.Inl id1), args, FStar_Pervasives_Native.None)
        | uu____1612 -> failwith "Not an app pattern"
  
let rec (gather_pattern_bound_vars_maybe_top :
  Prims.bool ->
    FStar_Ident.ident FStar_Util.set ->
      FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set)
  =
  fun fail_on_patconst  ->
    fun acc  ->
      fun p  ->
        let gather_pattern_bound_vars_from_list =
          FStar_List.fold_left
            (gather_pattern_bound_vars_maybe_top fail_on_patconst) acc
           in
        match p.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatWild uu____1667 -> acc
        | FStar_Parser_AST.PatName uu____1670 -> acc
        | FStar_Parser_AST.PatOp uu____1671 -> acc
        | FStar_Parser_AST.PatConst uu____1672 ->
            if fail_on_patconst
            then
              FStar_Errors.raise_error
                (FStar_Errors.Error_CannotRedefineConst,
                  "Constants cannot be redefined") p.FStar_Parser_AST.prange
            else acc
        | FStar_Parser_AST.PatApp (phead,pats) ->
            gather_pattern_bound_vars_from_list (phead :: pats)
        | FStar_Parser_AST.PatTvar (x,uu____1685) -> FStar_Util.set_add x acc
        | FStar_Parser_AST.PatVar (x,uu____1691) -> FStar_Util.set_add x acc
        | FStar_Parser_AST.PatList pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatTuple (pats,uu____1700) ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatOr pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatRecord guarded_pats ->
            let uu____1715 =
              FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
            gather_pattern_bound_vars_from_list uu____1715
        | FStar_Parser_AST.PatAscribed (pat,uu____1723) ->
            gather_pattern_bound_vars_maybe_top fail_on_patconst acc pat
  
let (gather_pattern_bound_vars :
  Prims.bool -> FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set)
  =
  fun fail_on_patconst  ->
    fun p  ->
      let acc =
        FStar_Util.new_set
          (fun id1  ->
             fun id2  ->
               if id1.FStar_Ident.idText = id2.FStar_Ident.idText
               then (Prims.parse_int "0")
               else (Prims.parse_int "1"))
         in
      gather_pattern_bound_vars_maybe_top fail_on_patconst acc p
  
type bnd =
  | LocalBinder of (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
  FStar_Pervasives_Native.tuple2 
  | LetBinder of
  (FStar_Ident.lident,(FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term
                                                  FStar_Pervasives_Native.option)
                        FStar_Pervasives_Native.tuple2)
  FStar_Pervasives_Native.tuple2 
let (uu___is_LocalBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LocalBinder _0 -> true | uu____1792 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____1828 -> false
  
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
  fun uu___251_1874  ->
    match uu___251_1874 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____1881 -> failwith "Impossible"
  
type env_t = FStar_Syntax_DsEnv.env
type lenv_t = FStar_Syntax_Syntax.bv Prims.list
let (mk_lb :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list,(FStar_Syntax_Syntax.bv,
                                                                    FStar_Syntax_Syntax.fv)
                                                                    FStar_Util.either,
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.term'
                                                           FStar_Syntax_Syntax.syntax,
    FStar_Range.range) FStar_Pervasives_Native.tuple5 ->
    FStar_Syntax_Syntax.letbinding)
  =
  fun uu____1914  ->
    match uu____1914 with
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
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun t  -> FStar_Syntax_Util.abs bs t FStar_Pervasives_Native.None
  
let (mk_ref_read :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____1994 =
        let uu____2011 =
          let uu____2014 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____2014  in
        let uu____2015 =
          let uu____2026 =
            let uu____2035 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2035)  in
          [uu____2026]  in
        (uu____2011, uu____2015)  in
      FStar_Syntax_Syntax.Tm_app uu____1994  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____2082 =
        let uu____2099 =
          let uu____2102 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____2102  in
        let uu____2103 =
          let uu____2114 =
            let uu____2123 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2123)  in
          [uu____2114]  in
        (uu____2099, uu____2103)  in
      FStar_Syntax_Syntax.Tm_app uu____2082  in
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
          let uu____2184 =
            let uu____2201 =
              let uu____2204 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____2204  in
            let uu____2205 =
              let uu____2216 =
                let uu____2225 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____2225)  in
              let uu____2232 =
                let uu____2243 =
                  let uu____2252 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____2252)  in
                [uu____2243]  in
              uu____2216 :: uu____2232  in
            (uu____2201, uu____2205)  in
          FStar_Syntax_Syntax.Tm_app uu____2184  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let (generalize_annotated_univs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun s  ->
    let bs_univnames bs =
      let uu____2310 =
        let uu____2325 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____2344  ->
               match uu____2344 with
               | ({ FStar_Syntax_Syntax.ppname = uu____2355;
                    FStar_Syntax_Syntax.index = uu____2356;
                    FStar_Syntax_Syntax.sort = t;_},uu____2358)
                   ->
                   let uu____2365 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____2365) uu____2325
         in
      FStar_All.pipe_right bs uu____2310  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____2381 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____2398 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____2424 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____2445,uu____2446,bs,t,uu____2449,uu____2450)
                            ->
                            let uu____2459 = bs_univnames bs  in
                            let uu____2462 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____2459 uu____2462
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____2465,uu____2466,t,uu____2468,uu____2469,uu____2470)
                            -> FStar_Syntax_Free.univnames t
                        | uu____2475 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____2424 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___279_2483 = s  in
        let uu____2484 =
          let uu____2485 =
            let uu____2494 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____2512,bs,t,lids1,lids2) ->
                          let uu___280_2525 = se  in
                          let uu____2526 =
                            let uu____2527 =
                              let uu____2544 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____2545 =
                                let uu____2546 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____2546 t  in
                              (lid, uvs, uu____2544, uu____2545, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____2527
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____2526;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___280_2525.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___280_2525.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___280_2525.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___280_2525.FStar_Syntax_Syntax.sigattrs)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____2560,t,tlid,n1,lids1) ->
                          let uu___281_2569 = se  in
                          let uu____2570 =
                            let uu____2571 =
                              let uu____2586 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____2586, tlid, n1, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____2571  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____2570;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___281_2569.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___281_2569.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___281_2569.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___281_2569.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____2589 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____2494, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____2485  in
        {
          FStar_Syntax_Syntax.sigel = uu____2484;
          FStar_Syntax_Syntax.sigrng =
            (uu___279_2483.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___279_2483.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___279_2483.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___279_2483.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2595,t) ->
        let uvs =
          let uu____2598 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____2598 FStar_Util.set_elements  in
        let uu___282_2603 = s  in
        let uu____2604 =
          let uu____2605 =
            let uu____2612 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____2612)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____2605  in
        {
          FStar_Syntax_Syntax.sigel = uu____2604;
          FStar_Syntax_Syntax.sigrng =
            (uu___282_2603.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___282_2603.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___282_2603.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___282_2603.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____2634 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____2637 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____2644) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____2677,(FStar_Util.Inl t,uu____2679),uu____2680)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____2727,(FStar_Util.Inr c,uu____2729),uu____2730)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____2777 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____2778,(FStar_Util.Inl t,uu____2780),uu____2781) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____2828,(FStar_Util.Inr c,uu____2830),uu____2831) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____2878 -> empty_set  in
          FStar_Util.set_union uu____2634 uu____2637  in
        let all_lb_univs =
          let uu____2882 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____2898 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____2898) empty_set)
             in
          FStar_All.pipe_right uu____2882 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___283_2908 = s  in
        let uu____2909 =
          let uu____2910 =
            let uu____2917 =
              let uu____2918 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___284_2930 = lb  in
                        let uu____2931 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____2934 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___284_2930.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____2931;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___284_2930.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____2934;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___284_2930.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___284_2930.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____2918)  in
            (uu____2917, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____2910  in
        {
          FStar_Syntax_Syntax.sigel = uu____2909;
          FStar_Syntax_Syntax.sigrng =
            (uu___283_2908.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___283_2908.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___283_2908.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___283_2908.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____2942,fml) ->
        let uvs =
          let uu____2945 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____2945 FStar_Util.set_elements  in
        let uu___285_2950 = s  in
        let uu____2951 =
          let uu____2952 =
            let uu____2959 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____2959)  in
          FStar_Syntax_Syntax.Sig_assume uu____2952  in
        {
          FStar_Syntax_Syntax.sigel = uu____2951;
          FStar_Syntax_Syntax.sigrng =
            (uu___285_2950.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___285_2950.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___285_2950.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___285_2950.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____2961,bs,c,flags1) ->
        let uvs =
          let uu____2970 =
            let uu____2973 = bs_univnames bs  in
            let uu____2976 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____2973 uu____2976  in
          FStar_All.pipe_right uu____2970 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___286_2984 = s  in
        let uu____2985 =
          let uu____2986 =
            let uu____2999 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____3000 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____2999, uu____3000, flags1)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____2986  in
        {
          FStar_Syntax_Syntax.sigel = uu____2985;
          FStar_Syntax_Syntax.sigrng =
            (uu___286_2984.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___286_2984.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___286_2984.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___286_2984.FStar_Syntax_Syntax.sigattrs)
        }
    | uu____3003 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___252_3008  ->
    match uu___252_3008 with
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
    | "null_wp" -> true
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
    | uu____3009 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____3021 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____3021)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____3040 =
      let uu____3041 = unparen t  in uu____3041.FStar_Parser_AST.tm  in
    match uu____3040 with
    | FStar_Parser_AST.Wild  ->
        let uu____3046 =
          let uu____3047 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____3047  in
        FStar_Util.Inr uu____3046
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____3058)) ->
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
             let uu____3123 = sum_to_universe u n1  in
             FStar_Util.Inr uu____3123
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____3134 = sum_to_universe u n1  in
             FStar_Util.Inr uu____3134
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____3145 =
               let uu____3150 =
                 let uu____3151 = FStar_Parser_AST.term_to_string t  in
                 Prims.strcat
                   "This universe might contain a sum of two universe variables "
                   uu____3151
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____3150)
                in
             FStar_Errors.raise_error uu____3145 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____3156 ->
        let rec aux t1 univargs =
          let uu____3190 =
            let uu____3191 = unparen t1  in uu____3191.FStar_Parser_AST.tm
             in
          match uu____3190 with
          | FStar_Parser_AST.App (t2,targ,uu____3198) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___253_3221  ->
                     match uu___253_3221 with
                     | FStar_Util.Inr uu____3226 -> true
                     | uu____3227 -> false) univargs
              then
                let uu____3232 =
                  let uu____3233 =
                    FStar_List.map
                      (fun uu___254_3242  ->
                         match uu___254_3242 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____3233  in
                FStar_Util.Inr uu____3232
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___255_3259  ->
                        match uu___255_3259 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____3265 -> failwith "impossible")
                     univargs
                    in
                 let uu____3266 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____3266)
          | uu____3272 ->
              let uu____3273 =
                let uu____3278 =
                  let uu____3279 =
                    let uu____3280 = FStar_Parser_AST.term_to_string t1  in
                    Prims.strcat uu____3280 " in universe context"  in
                  Prims.strcat "Unexpected term " uu____3279  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3278)  in
              FStar_Errors.raise_error uu____3273 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____3289 ->
        let uu____3290 =
          let uu____3295 =
            let uu____3296 =
              let uu____3297 = FStar_Parser_AST.term_to_string t  in
              Prims.strcat uu____3297 " in universe context"  in
            Prims.strcat "Unexpected term " uu____3296  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3295)  in
        FStar_Errors.raise_error uu____3290 t.FStar_Parser_AST.range
  
let rec (desugar_universe :
  FStar_Parser_AST.term -> FStar_Syntax_Syntax.universe) =
  fun t  ->
    let u = desugar_maybe_non_constant_universe t  in
    match u with
    | FStar_Util.Inl n1 -> int_to_universe n1
    | FStar_Util.Inr u1 -> u1
  
let (check_no_aq : FStar_Syntax_Syntax.antiquotations -> unit) =
  fun aq  ->
    match aq with
    | [] -> ()
    | (bv,{
            FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_quoted
              (e,{
                   FStar_Syntax_Syntax.qkind =
                     FStar_Syntax_Syntax.Quote_dynamic ;
                   FStar_Syntax_Syntax.antiquotes = uu____3327;_});
            FStar_Syntax_Syntax.pos = uu____3328;
            FStar_Syntax_Syntax.vars = uu____3329;_})::uu____3330
        ->
        let uu____3361 =
          let uu____3366 =
            let uu____3367 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____3367
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____3366)  in
        FStar_Errors.raise_error uu____3361 e.FStar_Syntax_Syntax.pos
    | (bv,e)::uu____3370 ->
        let uu____3389 =
          let uu____3394 =
            let uu____3395 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____3395
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____3394)  in
        FStar_Errors.raise_error uu____3389 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'Auu____3404 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident,'Auu____3404) FStar_Pervasives_Native.tuple2
        Prims.list -> FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____3432 = FStar_List.hd fields  in
        match uu____3432 with
        | (f,uu____3442) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____3454 =
                match uu____3454 with
                | (f',uu____3460) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____3462 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____3462
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
              (let uu____3466 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____3466);
              (match () with | () -> record)))
  
let rec (desugar_data_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern ->
      (env_t,bnd,annotated_pat Prims.list) FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun p  ->
      let check_linear_pattern_variables pats r =
        let rec pat_vars p1 =
          match p1.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_dot_term uu____3846 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_wild uu____3853 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_constant uu____3854 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_var x ->
              FStar_Util.set_add x FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_cons (uu____3856,pats1) ->
              let aux out uu____3894 =
                match uu____3894 with
                | (p2,uu____3906) ->
                    let intersection =
                      let uu____3914 = pat_vars p2  in
                      FStar_Util.set_intersect uu____3914 out  in
                    let uu____3917 = FStar_Util.set_is_empty intersection  in
                    if uu____3917
                    then
                      let uu____3920 = pat_vars p2  in
                      FStar_Util.set_union out uu____3920
                    else
                      (let duplicate_bv =
                         let uu____3925 =
                           FStar_Util.set_elements intersection  in
                         FStar_List.hd uu____3925  in
                       let uu____3928 =
                         let uu____3933 =
                           FStar_Util.format1
                             "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                             (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                            in
                         (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                           uu____3933)
                          in
                       FStar_Errors.raise_error uu____3928 r)
                 in
              FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
           in
        match pats with
        | [] -> ()
        | p1::[] ->
            let uu____3953 = pat_vars p1  in
            FStar_All.pipe_right uu____3953 (fun a1  -> ())
        | p1::ps ->
            let pvars = pat_vars p1  in
            let aux p2 =
              let uu____3981 =
                let uu____3982 = pat_vars p2  in
                FStar_Util.set_eq pvars uu____3982  in
              if uu____3981
              then ()
              else
                (let nonlinear_vars =
                   let uu____3989 = pat_vars p2  in
                   FStar_Util.set_symmetric_difference pvars uu____3989  in
                 let first_nonlinear_var =
                   let uu____3993 = FStar_Util.set_elements nonlinear_vars
                      in
                   FStar_List.hd uu____3993  in
                 let uu____3996 =
                   let uu____4001 =
                     FStar_Util.format1
                       "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                       (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                      in
                   (FStar_Errors.Fatal_IncoherentPatterns, uu____4001)  in
                 FStar_Errors.raise_error uu____3996 r)
               in
            FStar_List.iter aux ps
         in
      let resolvex l e x =
        let uu____4026 =
          FStar_All.pipe_right l
            (FStar_Util.find_opt
               (fun y  ->
                  (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                    x.FStar_Ident.idText))
           in
        match uu____4026 with
        | FStar_Pervasives_Native.Some y -> (l, e, y)
        | uu____4042 ->
            let uu____4045 = FStar_Syntax_DsEnv.push_bv e x  in
            (match uu____4045 with | (e1,x1) -> ((x1 :: l), e1, x1))
         in
      let rec aux' top loc env1 p1 =
        let pos q = FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange
           in
        let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
        let orig = p1  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr uu____4190 -> failwith "impossible"
        | FStar_Parser_AST.PatOp op ->
            let uu____4212 =
              let uu____4213 =
                let uu____4214 =
                  let uu____4221 =
                    let uu____4222 =
                      let uu____4227 =
                        FStar_Parser_AST.compile_op (Prims.parse_int "0")
                          op.FStar_Ident.idText op.FStar_Ident.idRange
                         in
                      (uu____4227, (op.FStar_Ident.idRange))  in
                    FStar_Ident.mk_ident uu____4222  in
                  (uu____4221, FStar_Pervasives_Native.None)  in
                FStar_Parser_AST.PatVar uu____4214  in
              {
                FStar_Parser_AST.pat = uu____4213;
                FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
              }  in
            aux loc env1 uu____4212
        | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
            ((match tacopt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some uu____4244 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                      "Type ascriptions within patterns cannot be associated with a tactic")
                    orig.FStar_Parser_AST.prange);
             (let uu____4245 = aux loc env1 p2  in
              match uu____4245 with
              | (loc1,env',binder,p3,annots,imp) ->
                  let annot_pat_var p4 t1 =
                    match p4.FStar_Syntax_Syntax.v with
                    | FStar_Syntax_Syntax.Pat_var x ->
                        let uu___287_4330 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_var
                               (let uu___288_4335 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___288_4335.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___288_4335.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___287_4330.FStar_Syntax_Syntax.p)
                        }
                    | FStar_Syntax_Syntax.Pat_wild x ->
                        let uu___289_4337 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_wild
                               (let uu___290_4342 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___290_4342.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___290_4342.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___289_4337.FStar_Syntax_Syntax.p)
                        }
                    | uu____4343 when top -> p4
                    | uu____4344 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                            "Type ascriptions within patterns are only allowed on variables")
                          orig.FStar_Parser_AST.prange
                     in
                  let uu____4347 =
                    match binder with
                    | LetBinder uu____4368 -> failwith "impossible"
                    | LocalBinder (x,aq) ->
                        let t1 =
                          let uu____4392 = close_fun env1 t  in
                          desugar_term env1 uu____4392  in
                        let x1 =
                          let uu___291_4394 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___291_4394.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___291_4394.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t1
                          }  in
                        ([(x1, t1)], (LocalBinder (x1, aq)))
                     in
                  (match uu____4347 with
                   | (annots',binder1) ->
                       (loc1, env', binder1, p3,
                         (FStar_List.append annots' annots), imp))))
        | FStar_Parser_AST.PatWild aq ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                FStar_Syntax_Syntax.tun
               in
            let uu____4459 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
            (loc, env1, (LocalBinder (x, aq1)), uu____4459, [], imp)
        | FStar_Parser_AST.PatConst c ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                FStar_Syntax_Syntax.tun
               in
            let uu____4472 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____4472, [], false)
        | FStar_Parser_AST.PatTvar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____4493 = resolvex loc env1 x  in
            (match uu____4493 with
             | (loc1,env2,xbv) ->
                 let uu____4521 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____4521, [], imp))
        | FStar_Parser_AST.PatVar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____4542 = resolvex loc env1 x  in
            (match uu____4542 with
             | (loc1,env2,xbv) ->
                 let uu____4570 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____4570, [], imp))
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
            let uu____4584 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (l1, []))
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____4584, [], false)
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
               FStar_Parser_AST.prange = uu____4610;_},args)
            ->
            let uu____4616 =
              FStar_List.fold_right
                (fun arg  ->
                   fun uu____4675  ->
                     match uu____4675 with
                     | (loc1,env2,annots,args1) ->
                         let uu____4752 = aux loc1 env2 arg  in
                         (match uu____4752 with
                          | (loc2,env3,uu____4797,arg1,ans,imp) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((arg1, imp) :: args1)))) args
                (loc, env1, [], [])
               in
            (match uu____4616 with
             | (loc1,env2,annots,args1) ->
                 let l1 =
                   FStar_Syntax_DsEnv.fail_or env2
                     (FStar_Syntax_DsEnv.try_lookup_datacon env2) l
                    in
                 let x =
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some
                        (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun
                    in
                 let uu____4919 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____4919, annots, false))
        | FStar_Parser_AST.PatApp uu____4934 ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
              p1.FStar_Parser_AST.prange
        | FStar_Parser_AST.PatList pats ->
            let uu____4962 =
              FStar_List.fold_right
                (fun pat  ->
                   fun uu____5013  ->
                     match uu____5013 with
                     | (loc1,env2,annots,pats1) ->
                         let uu____5074 = aux loc1 env2 pat  in
                         (match uu____5074 with
                          | (loc2,env3,uu____5115,pat1,ans,uu____5118) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                (pat1 :: pats1)))) pats (loc, env1, [], [])
               in
            (match uu____4962 with
             | (loc1,env2,annots,pats1) ->
                 let pat =
                   let uu____5212 =
                     let uu____5215 =
                       let uu____5222 =
                         FStar_Range.end_range p1.FStar_Parser_AST.prange  in
                       pos_r uu____5222  in
                     let uu____5223 =
                       let uu____5224 =
                         let uu____5237 =
                           FStar_Syntax_Syntax.lid_as_fv
                             FStar_Parser_Const.nil_lid
                             FStar_Syntax_Syntax.delta_constant
                             (FStar_Pervasives_Native.Some
                                FStar_Syntax_Syntax.Data_ctor)
                            in
                         (uu____5237, [])  in
                       FStar_Syntax_Syntax.Pat_cons uu____5224  in
                     FStar_All.pipe_left uu____5215 uu____5223  in
                   FStar_List.fold_right
                     (fun hd1  ->
                        fun tl1  ->
                          let r =
                            FStar_Range.union_ranges
                              hd1.FStar_Syntax_Syntax.p
                              tl1.FStar_Syntax_Syntax.p
                             in
                          let uu____5269 =
                            let uu____5270 =
                              let uu____5283 =
                                FStar_Syntax_Syntax.lid_as_fv
                                  FStar_Parser_Const.cons_lid
                                  FStar_Syntax_Syntax.delta_constant
                                  (FStar_Pervasives_Native.Some
                                     FStar_Syntax_Syntax.Data_ctor)
                                 in
                              (uu____5283, [(hd1, false); (tl1, false)])  in
                            FStar_Syntax_Syntax.Pat_cons uu____5270  in
                          FStar_All.pipe_left (pos_r r) uu____5269) pats1
                     uu____5212
                    in
                 let x =
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some
                        (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)), pat,
                   annots, false))
        | FStar_Parser_AST.PatTuple (args,dep1) ->
            let uu____5329 =
              FStar_List.fold_left
                (fun uu____5387  ->
                   fun p2  ->
                     match uu____5387 with
                     | (loc1,env2,annots,pats) ->
                         let uu____5465 = aux loc1 env2 p2  in
                         (match uu____5465 with
                          | (loc2,env3,uu____5510,pat,ans,uu____5513) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((pat, false) :: pats)))) (loc, env1, [], [])
                args
               in
            (match uu____5329 with
             | (loc1,env2,annots,args1) ->
                 let args2 = FStar_List.rev args1  in
                 let l =
                   if dep1
                   then
                     FStar_Parser_Const.mk_dtuple_data_lid
                       (FStar_List.length args2) p1.FStar_Parser_AST.prange
                   else
                     FStar_Parser_Const.mk_tuple_data_lid
                       (FStar_List.length args2) p1.FStar_Parser_AST.prange
                    in
                 let constr =
                   FStar_Syntax_DsEnv.fail_or env2
                     (FStar_Syntax_DsEnv.try_lookup_lid env2) l
                    in
                 let l1 =
                   match constr.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                   | uu____5662 -> failwith "impossible"  in
                 let x =
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some
                        (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun
                    in
                 let uu____5664 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____5664, annots, false))
        | FStar_Parser_AST.PatRecord [] ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
              p1.FStar_Parser_AST.prange
        | FStar_Parser_AST.PatRecord fields ->
            let record = check_fields env1 fields p1.FStar_Parser_AST.prange
               in
            let fields1 =
              FStar_All.pipe_right fields
                (FStar_List.map
                   (fun uu____5739  ->
                      match uu____5739 with
                      | (f,p2) -> ((f.FStar_Ident.ident), p2)))
               in
            let args =
              FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                (FStar_List.map
                   (fun uu____5769  ->
                      match uu____5769 with
                      | (f,uu____5775) ->
                          let uu____5776 =
                            FStar_All.pipe_right fields1
                              (FStar_List.tryFind
                                 (fun uu____5802  ->
                                    match uu____5802 with
                                    | (g,uu____5808) ->
                                        f.FStar_Ident.idText =
                                          g.FStar_Ident.idText))
                             in
                          (match uu____5776 with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatWild
                                    FStar_Pervasives_Native.None)
                                 p1.FStar_Parser_AST.prange
                           | FStar_Pervasives_Native.Some (uu____5813,p2) ->
                               p2)))
               in
            let app =
              let uu____5820 =
                let uu____5821 =
                  let uu____5828 =
                    let uu____5829 =
                      let uu____5830 =
                        FStar_Ident.lid_of_ids
                          (FStar_List.append
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                             [record.FStar_Syntax_DsEnv.constrname])
                         in
                      FStar_Parser_AST.PatName uu____5830  in
                    FStar_Parser_AST.mk_pattern uu____5829
                      p1.FStar_Parser_AST.prange
                     in
                  (uu____5828, args)  in
                FStar_Parser_AST.PatApp uu____5821  in
              FStar_Parser_AST.mk_pattern uu____5820
                p1.FStar_Parser_AST.prange
               in
            let uu____5833 = aux loc env1 app  in
            (match uu____5833 with
             | (env2,e,b,p2,annots,uu____5877) ->
                 let p3 =
                   match p2.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                       let uu____5913 =
                         let uu____5914 =
                           let uu____5927 =
                             let uu___292_5928 = fv  in
                             let uu____5929 =
                               let uu____5932 =
                                 let uu____5933 =
                                   let uu____5940 =
                                     FStar_All.pipe_right
                                       record.FStar_Syntax_DsEnv.fields
                                       (FStar_List.map
                                          FStar_Pervasives_Native.fst)
                                      in
                                   ((record.FStar_Syntax_DsEnv.typename),
                                     uu____5940)
                                    in
                                 FStar_Syntax_Syntax.Record_ctor uu____5933
                                  in
                               FStar_Pervasives_Native.Some uu____5932  in
                             {
                               FStar_Syntax_Syntax.fv_name =
                                 (uu___292_5928.FStar_Syntax_Syntax.fv_name);
                               FStar_Syntax_Syntax.fv_delta =
                                 (uu___292_5928.FStar_Syntax_Syntax.fv_delta);
                               FStar_Syntax_Syntax.fv_qual = uu____5929
                             }  in
                           (uu____5927, args1)  in
                         FStar_Syntax_Syntax.Pat_cons uu____5914  in
                       FStar_All.pipe_left pos uu____5913
                   | uu____5965 -> p2  in
                 (env2, e, b, p3, annots, false))
      
      and aux loc env1 p1 = aux' false loc env1 p1
       in
      let aux_maybe_or env1 p1 =
        let loc = []  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr [] -> failwith "impossible"
        | FStar_Parser_AST.PatOr (p2::ps) ->
            let uu____6047 = aux' true loc env1 p2  in
            (match uu____6047 with
             | (loc1,env2,var,p3,ans,uu____6089) ->
                 let uu____6102 =
                   FStar_List.fold_left
                     (fun uu____6151  ->
                        fun p4  ->
                          match uu____6151 with
                          | (loc2,env3,ps1) ->
                              let uu____6216 = aux' true loc2 env3 p4  in
                              (match uu____6216 with
                               | (loc3,env4,uu____6255,p5,ans1,uu____6258) ->
                                   (loc3, env4, ((p5, ans1) :: ps1))))
                     (loc1, env2, []) ps
                    in
                 (match uu____6102 with
                  | (loc2,env3,ps1) ->
                      let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                      (env3, var, pats)))
        | uu____6417 ->
            let uu____6418 = aux' true loc env1 p1  in
            (match uu____6418 with
             | (loc1,env2,vars,pat,ans,b) -> (env2, vars, [(pat, ans)]))
         in
      let uu____6511 = aux_maybe_or env p  in
      match uu____6511 with
      | (env1,b,pats) ->
          ((let uu____6566 = FStar_List.map FStar_Pervasives_Native.fst pats
               in
            check_linear_pattern_variables uu____6566
              p.FStar_Parser_AST.prange);
           (env1, b, pats))

and (desugar_binding_pat_maybe_top :
  Prims.bool ->
    FStar_Syntax_DsEnv.env ->
      FStar_Parser_AST.pattern ->
        (env_t,bnd,annotated_pat Prims.list) FStar_Pervasives_Native.tuple3)
  =
  fun top  ->
    fun env  ->
      fun p  ->
        let mklet x ty tacopt =
          let uu____6638 =
            let uu____6639 =
              let uu____6650 = FStar_Syntax_DsEnv.qualify env x  in
              (uu____6650, (ty, tacopt))  in
            LetBinder uu____6639  in
          (env, uu____6638, [])  in
        let op_to_ident x =
          let uu____6667 =
            let uu____6672 =
              FStar_Parser_AST.compile_op (Prims.parse_int "0")
                x.FStar_Ident.idText x.FStar_Ident.idRange
               in
            (uu____6672, (x.FStar_Ident.idRange))  in
          FStar_Ident.mk_ident uu____6667  in
        if top
        then
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu____6690 = op_to_ident x  in
              mklet uu____6690 FStar_Syntax_Syntax.tun
                FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x,uu____6692) ->
              mklet x FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu____6698;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____6714 = op_to_ident x  in
              let uu____6715 = desugar_term env t  in
              mklet uu____6714 uu____6715 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____6717);
                 FStar_Parser_AST.prange = uu____6718;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____6738 = desugar_term env t  in
              mklet x uu____6738 tacopt1
          | uu____6739 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu____6749 = desugar_data_pat env p  in
           match uu____6749 with
           | (env1,binder,p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu____6778;
                      FStar_Syntax_Syntax.p = uu____6779;_},uu____6780)::[]
                     -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu____6793;
                      FStar_Syntax_Syntax.p = uu____6794;_},uu____6795)::[]
                     -> []
                 | uu____6808 -> p1  in
               (env1, binder, p2))

and (desugar_binding_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern ->
      (env_t,bnd,annotated_pat Prims.list) FStar_Pervasives_Native.tuple3)
  = fun env  -> fun p  -> desugar_binding_pat_maybe_top false env p

and (desugar_match_pat_maybe_top :
  Prims.bool ->
    FStar_Syntax_DsEnv.env ->
      FStar_Parser_AST.pattern ->
        (env_t,annotated_pat Prims.list) FStar_Pervasives_Native.tuple2)
  =
  fun uu____6815  ->
    fun env  ->
      fun pat  ->
        let uu____6818 = desugar_data_pat env pat  in
        match uu____6818 with | (env1,uu____6834,pat1) -> (env1, pat1)

and (desugar_match_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern ->
      (env_t,annotated_pat Prims.list) FStar_Pervasives_Native.tuple2)
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
      let uu____6853 = desugar_term_aq env e  in
      match uu____6853 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____6870 = desugar_typ_aq env e  in
      match uu____6870 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness,FStar_Const.width)
        FStar_Pervasives_Native.tuple2 ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____6880  ->
        fun range  ->
          match uu____6880 with
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
              ((let uu____6890 =
                  let uu____6891 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____6891  in
                if uu____6890
                then
                  let uu____6892 =
                    let uu____6897 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____6897)  in
                  FStar_Errors.log_issue range uu____6892
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
                  let uu____6902 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____6902 range  in
                let lid1 =
                  let uu____6906 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____6906 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____6916 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____6916 range  in
                           let private_fv =
                             let uu____6918 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____6918 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___293_6919 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___293_6919.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___293_6919.FStar_Syntax_Syntax.vars)
                           }
                       | uu____6920 ->
                           failwith
                             (Prims.strcat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____6923 =
                        let uu____6928 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____6928)
                         in
                      FStar_Errors.raise_error uu____6923 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____6944 =
                  let uu____6951 =
                    let uu____6952 =
                      let uu____6969 =
                        let uu____6980 =
                          let uu____6989 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____6989)  in
                        [uu____6980]  in
                      (lid1, uu____6969)  in
                    FStar_Syntax_Syntax.Tm_app uu____6952  in
                  FStar_Syntax_Syntax.mk uu____6951  in
                uu____6944 FStar_Pervasives_Native.None range))

and (desugar_name :
  (FStar_Syntax_Syntax.term' ->
     FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
    ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      env_t -> Prims.bool -> FStar_Ident.lid -> FStar_Syntax_Syntax.term)
  =
  fun mk1  ->
    fun setpos  ->
      fun env  ->
        fun resolve  ->
          fun l  ->
            let uu____7038 =
              let uu____7045 =
                (if resolve
                 then FStar_Syntax_DsEnv.try_lookup_lid_with_attributes
                 else
                   FStar_Syntax_DsEnv.try_lookup_lid_with_attributes_no_resolve)
                  env
                 in
              FStar_Syntax_DsEnv.fail_or env uu____7045 l  in
            match uu____7038 with
            | (tm,attrs) ->
                let warn_if_deprecated attrs1 =
                  FStar_List.iter
                    (fun a  ->
                       match a.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_app
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____7095;
                              FStar_Syntax_Syntax.vars = uu____7096;_},args)
                           when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____7123 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____7123 " is deprecated"  in
                           let msg1 =
                             if
                               (FStar_List.length args) >
                                 (Prims.parse_int "0")
                             then
                               let uu____7133 =
                                 let uu____7134 =
                                   let uu____7137 = FStar_List.hd args  in
                                   FStar_Pervasives_Native.fst uu____7137  in
                                 uu____7134.FStar_Syntax_Syntax.n  in
                               match uu____7133 with
                               | FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_string (s,uu____7159))
                                   when
                                   Prims.op_Negation
                                     ((FStar_Util.trim_string s) = "")
                                   ->
                                   Prims.strcat msg
                                     (Prims.strcat ", use "
                                        (Prims.strcat s " instead"))
                               | uu____7160 -> msg
                             else msg  in
                           let uu____7162 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____7162
                             (FStar_Errors.Warning_DeprecatedDefinition,
                               msg1)
                       | FStar_Syntax_Syntax.Tm_fvar fv when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____7165 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____7165 " is deprecated"  in
                           let uu____7166 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____7166
                             (FStar_Errors.Warning_DeprecatedDefinition, msg)
                       | uu____7167 -> ()) attrs1
                   in
                (warn_if_deprecated attrs; (let tm1 = setpos tm  in tm1))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____7182 =
          let uu____7183 = unparen t  in uu____7183.FStar_Parser_AST.tm  in
        match uu____7182 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____7184; FStar_Ident.ident = uu____7185;
              FStar_Ident.nsstr = uu____7186; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____7189 ->
            let uu____7190 =
              let uu____7195 =
                let uu____7196 = FStar_Parser_AST.term_to_string t  in
                Prims.strcat "Unknown attribute " uu____7196  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____7195)  in
            FStar_Errors.raise_error uu____7190 t.FStar_Parser_AST.range
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
          let uu___294_7279 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___294_7279.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___294_7279.FStar_Syntax_Syntax.vars)
          }  in
        let uu____7282 =
          let uu____7283 = unparen top  in uu____7283.FStar_Parser_AST.tm  in
        match uu____7282 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____7288 ->
            let uu____7295 = desugar_formula env top  in (uu____7295, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____7302 = desugar_formula env t  in (uu____7302, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____7309 = desugar_formula env t  in (uu____7309, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____7333 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____7333, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____7335 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____7335, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____7343 =
                let uu____7344 =
                  let uu____7351 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____7351, args)  in
                FStar_Parser_AST.Op uu____7344  in
              FStar_Parser_AST.mk_term uu____7343 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____7354 =
              let uu____7355 =
                let uu____7356 =
                  let uu____7363 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____7363, [e])  in
                FStar_Parser_AST.Op uu____7356  in
              FStar_Parser_AST.mk_term uu____7355 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____7354
        | FStar_Parser_AST.Op (op_star,lhs::rhs::[]) when
            (let uu____7373 = FStar_Ident.text_of_id op_star  in
             uu____7373 = "*") &&
              (let uu____7375 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____7375 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____7390;_},t1::t2::[])
                  when
                  let uu____7395 =
                    op_as_term env (Prims.parse_int "2")
                      top.FStar_Parser_AST.range op_star
                     in
                  FStar_All.pipe_right uu____7395 FStar_Option.isNone ->
                  let uu____7400 = flatten1 t1  in
                  FStar_List.append uu____7400 [t2]
              | uu____7403 -> [t]  in
            let terms = flatten1 lhs  in
            let t =
              let uu___295_7408 = top  in
              let uu____7409 =
                let uu____7410 =
                  let uu____7421 =
                    FStar_List.map (fun _0_1  -> FStar_Util.Inr _0_1) terms
                     in
                  (uu____7421, rhs)  in
                FStar_Parser_AST.Sum uu____7410  in
              {
                FStar_Parser_AST.tm = uu____7409;
                FStar_Parser_AST.range =
                  (uu___295_7408.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___295_7408.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env t
        | FStar_Parser_AST.Tvar a ->
            let uu____7439 =
              let uu____7440 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_All.pipe_left setpos uu____7440  in
            (uu____7439, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____7446 =
              let uu____7451 =
                let uu____7452 =
                  let uu____7453 = FStar_Ident.text_of_id u  in
                  Prims.strcat uu____7453 " in non-universe context"  in
                Prims.strcat "Unexpected universe variable " uu____7452  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____7451)  in
            FStar_Errors.raise_error uu____7446 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____7464 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____7464 with
             | FStar_Pervasives_Native.None  ->
                 let uu____7471 =
                   let uu____7476 =
                     let uu____7477 = FStar_Ident.text_of_id s  in
                     Prims.strcat "Unexpected or unbound operator: "
                       uu____7477
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____7476)
                    in
                 FStar_Errors.raise_error uu____7471
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let uu____7487 =
                     let uu____7512 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____7574 = desugar_term_aq env t  in
                               match uu____7574 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____7512 FStar_List.unzip  in
                   (match uu____7487 with
                    | (args1,aqs) ->
                        let uu____7707 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____7707, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____7723)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____7738 =
              let uu___296_7739 = top  in
              let uu____7740 =
                let uu____7741 =
                  let uu____7748 =
                    let uu___297_7749 = top  in
                    let uu____7750 =
                      let uu____7751 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____7751  in
                    {
                      FStar_Parser_AST.tm = uu____7750;
                      FStar_Parser_AST.range =
                        (uu___297_7749.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___297_7749.FStar_Parser_AST.level)
                    }  in
                  (uu____7748, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____7741  in
              {
                FStar_Parser_AST.tm = uu____7740;
                FStar_Parser_AST.range =
                  (uu___296_7739.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___296_7739.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____7738
        | FStar_Parser_AST.Construct (n1,(a,uu____7754)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____7770 =
                let uu___298_7771 = top  in
                let uu____7772 =
                  let uu____7773 =
                    let uu____7780 =
                      let uu___299_7781 = top  in
                      let uu____7782 =
                        let uu____7783 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____7783  in
                      {
                        FStar_Parser_AST.tm = uu____7782;
                        FStar_Parser_AST.range =
                          (uu___299_7781.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___299_7781.FStar_Parser_AST.level)
                      }  in
                    (uu____7780, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____7773  in
                {
                  FStar_Parser_AST.tm = uu____7772;
                  FStar_Parser_AST.range =
                    (uu___298_7771.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___298_7771.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____7770))
        | FStar_Parser_AST.Construct (n1,(a,uu____7786)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____7801 =
              let uu___300_7802 = top  in
              let uu____7803 =
                let uu____7804 =
                  let uu____7811 =
                    let uu___301_7812 = top  in
                    let uu____7813 =
                      let uu____7814 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____7814  in
                    {
                      FStar_Parser_AST.tm = uu____7813;
                      FStar_Parser_AST.range =
                        (uu___301_7812.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___301_7812.FStar_Parser_AST.level)
                    }  in
                  (uu____7811, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____7804  in
              {
                FStar_Parser_AST.tm = uu____7803;
                FStar_Parser_AST.range =
                  (uu___300_7802.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___300_7802.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____7801
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____7815; FStar_Ident.ident = uu____7816;
              FStar_Ident.nsstr = uu____7817; FStar_Ident.str = "Type0";_}
            ->
            let uu____7820 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____7820, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____7821; FStar_Ident.ident = uu____7822;
              FStar_Ident.nsstr = uu____7823; FStar_Ident.str = "Type";_}
            ->
            let uu____7826 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____7826, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____7827; FStar_Ident.ident = uu____7828;
               FStar_Ident.nsstr = uu____7829; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____7847 =
              let uu____7848 =
                let uu____7849 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____7849  in
              mk1 uu____7848  in
            (uu____7847, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____7850; FStar_Ident.ident = uu____7851;
              FStar_Ident.nsstr = uu____7852; FStar_Ident.str = "Effect";_}
            ->
            let uu____7855 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____7855, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____7856; FStar_Ident.ident = uu____7857;
              FStar_Ident.nsstr = uu____7858; FStar_Ident.str = "True";_}
            ->
            let uu____7861 =
              let uu____7862 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____7862
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____7861, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____7863; FStar_Ident.ident = uu____7864;
              FStar_Ident.nsstr = uu____7865; FStar_Ident.str = "False";_}
            ->
            let uu____7868 =
              let uu____7869 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____7869
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____7868, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____7872;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____7874 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____7874 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____7883 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_constant_at_level
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None
                     in
                  (uu____7883, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____7884 =
                    let uu____7885 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____7885 txt
                     in
                  failwith uu____7884))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____7892 = desugar_name mk1 setpos env true l  in
              (uu____7892, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____7895 = desugar_name mk1 setpos env true l  in
              (uu____7895, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____7906 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____7906 with
                | FStar_Pervasives_Native.Some uu____7915 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____7920 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____7920 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____7934 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____7951 =
                    let uu____7952 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____7952  in
                  (uu____7951, noaqs)
              | uu____7953 ->
                  let uu____7960 =
                    let uu____7965 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____7965)  in
                  FStar_Errors.raise_error uu____7960
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____7972 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____7972 with
              | FStar_Pervasives_Native.None  ->
                  let uu____7979 =
                    let uu____7984 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____7984)
                     in
                  FStar_Errors.raise_error uu____7979
                    top.FStar_Parser_AST.range
              | uu____7989 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____7993 = desugar_name mk1 setpos env true lid'  in
                  (uu____7993, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8009 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____8009 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____8028 ->
                       let uu____8035 =
                         FStar_Util.take
                           (fun uu____8059  ->
                              match uu____8059 with
                              | (uu____8064,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____8035 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____8109 =
                              let uu____8134 =
                                FStar_List.map
                                  (fun uu____8177  ->
                                     match uu____8177 with
                                     | (t,imp) ->
                                         let uu____8194 =
                                           desugar_term_aq env t  in
                                         (match uu____8194 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____8134
                                FStar_List.unzip
                               in
                            (match uu____8109 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____8335 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____8335, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____8353 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____8353 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.strcat "Constructor "
                             (Prims.strcat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____8360 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.strcat "Effect "
                             (Prims.strcat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) when
            FStar_Util.for_all
              (fun uu___256_8385  ->
                 match uu___256_8385 with
                 | FStar_Util.Inr uu____8390 -> true
                 | uu____8391 -> false) binders
            ->
            let terms =
              let uu____8399 =
                FStar_All.pipe_right binders
                  (FStar_List.map
                     (fun uu___257_8416  ->
                        match uu___257_8416 with
                        | FStar_Util.Inr x -> x
                        | FStar_Util.Inl uu____8422 -> failwith "Impossible"))
                 in
              FStar_List.append uu____8399 [t]  in
            let uu____8423 =
              let uu____8448 =
                FStar_All.pipe_right terms
                  (FStar_List.map
                     (fun t1  ->
                        let uu____8505 = desugar_typ_aq env t1  in
                        match uu____8505 with
                        | (t',aq) ->
                            let uu____8516 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____8516, aq)))
                 in
              FStar_All.pipe_right uu____8448 FStar_List.unzip  in
            (match uu____8423 with
             | (targs,aqs) ->
                 let tup =
                   let uu____8626 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____8626
                    in
                 let uu____8635 =
                   mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                 (uu____8635, (join_aqs aqs)))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____8662 =
              let uu____8679 =
                let uu____8686 =
                  let uu____8693 =
                    FStar_All.pipe_left (fun _0_2  -> FStar_Util.Inl _0_2)
                      (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                         FStar_Pervasives_Native.None)
                     in
                  [uu____8693]  in
                FStar_List.append binders uu____8686  in
              FStar_List.fold_left
                (fun uu____8746  ->
                   fun b  ->
                     match uu____8746 with
                     | (env1,tparams,typs) ->
                         let uu____8807 =
                           match b with
                           | FStar_Util.Inl b1 -> desugar_binder env1 b1
                           | FStar_Util.Inr t1 ->
                               let uu____8822 = desugar_typ env1 t1  in
                               (FStar_Pervasives_Native.None, uu____8822)
                            in
                         (match uu____8807 with
                          | (xopt,t1) ->
                              let uu____8847 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____8856 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____8856)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____8847 with
                               | (env2,x) ->
                                   let uu____8876 =
                                     let uu____8879 =
                                       let uu____8882 =
                                         let uu____8883 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____8883
                                          in
                                       [uu____8882]  in
                                     FStar_List.append typs uu____8879  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___302_8909 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___302_8909.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___302_8909.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____8876)))) (env, [], []) uu____8679
               in
            (match uu____8662 with
             | (env1,uu____8937,targs) ->
                 let tup =
                   let uu____8960 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____8960
                    in
                 let uu____8961 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_app (tup, targs))
                    in
                 (uu____8961, noaqs))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____8980 = uncurry binders t  in
            (match uu____8980 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___258_9024 =
                   match uu___258_9024 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1  in
                       let uu____9040 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____9040
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____9064 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____9064 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____9097 = aux env [] bs  in (uu____9097, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____9106 = desugar_binder env b  in
            (match uu____9106 with
             | (FStar_Pervasives_Native.None ,uu____9117) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____9131 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____9131 with
                  | ((x,uu____9147),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____9160 =
                        let uu____9161 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____9161  in
                      (uu____9160, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let bvss =
              FStar_List.map (gather_pattern_bound_vars false) binders  in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set1::sets2 ->
                    let i = FStar_Util.set_intersect acc set1  in
                    let uu____9239 = FStar_Util.set_is_empty i  in
                    if uu____9239
                    then
                      let uu____9242 = FStar_Util.set_union acc set1  in
                      aux uu____9242 sets2
                    else
                      (let uu____9246 =
                         let uu____9247 = FStar_Util.set_elements i  in
                         FStar_List.hd uu____9247  in
                       FStar_Pervasives_Native.Some uu____9246)
                 in
              let uu____9250 = FStar_Syntax_Syntax.new_id_set ()  in
              aux uu____9250 sets  in
            ((let uu____9254 = check_disjoint bvss  in
              match uu____9254 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some id1 ->
                  let uu____9258 =
                    let uu____9263 =
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        id1.FStar_Ident.idText
                       in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____9263)
                     in
                  let uu____9264 = FStar_Ident.range_of_id id1  in
                  FStar_Errors.raise_error uu____9258 uu____9264);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern)
                 in
              let uu____9272 =
                FStar_List.fold_left
                  (fun uu____9292  ->
                     fun pat  ->
                       match uu____9292 with
                       | (env1,ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____9318,(t,FStar_Pervasives_Native.None ))
                                ->
                                let uu____9328 =
                                  let uu____9331 = free_type_vars env1 t  in
                                  FStar_List.append uu____9331 ftvs  in
                                (env1, uu____9328)
                            | FStar_Parser_AST.PatAscribed
                                (uu____9336,(t,FStar_Pervasives_Native.Some
                                             tac))
                                ->
                                let uu____9347 =
                                  let uu____9350 = free_type_vars env1 t  in
                                  let uu____9353 =
                                    let uu____9356 = free_type_vars env1 tac
                                       in
                                    FStar_List.append uu____9356 ftvs  in
                                  FStar_List.append uu____9350 uu____9353  in
                                (env1, uu____9347)
                            | uu____9361 -> (env1, ftvs))) (env, []) binders1
                 in
              match uu____9272 with
              | (uu____9370,ftv) ->
                  let ftv1 = sort_ftv ftv  in
                  let binders2 =
                    let uu____9382 =
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
                    FStar_List.append uu____9382 binders1  in
                  let rec aux env1 bs sc_pat_opt uu___259_9439 =
                    match uu___259_9439 with
                    | [] ->
                        let uu____9466 = desugar_term_aq env1 body  in
                        (match uu____9466 with
                         | (body1,aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc,pat) ->
                                   let body2 =
                                     let uu____9503 =
                                       let uu____9504 =
                                         FStar_Syntax_Syntax.pat_bvs pat  in
                                       FStar_All.pipe_right uu____9504
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder)
                                        in
                                     FStar_Syntax_Subst.close uu____9503
                                       body1
                                      in
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_match
                                        (sc,
                                          [(pat,
                                             FStar_Pervasives_Native.None,
                                             body2)]))
                                     FStar_Pervasives_Native.None
                                     body2.FStar_Syntax_Syntax.pos
                               | FStar_Pervasives_Native.None  -> body1  in
                             let uu____9573 =
                               let uu____9576 =
                                 no_annot_abs (FStar_List.rev bs) body2  in
                               setpos uu____9576  in
                             (uu____9573, aq))
                    | p::rest ->
                        let uu____9591 = desugar_binding_pat env1 p  in
                        (match uu____9591 with
                         | (env2,b,pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1,uu____9625)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____9640 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange
                                in
                             let uu____9647 =
                               match b with
                               | LetBinder uu____9688 ->
                                   failwith "Impossible"
                               | LocalBinder (x,aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None
                                        ,uu____9756) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.None ) ->
                                         let uu____9810 =
                                           let uu____9819 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____9819, p1)  in
                                         FStar_Pervasives_Native.Some
                                           uu____9810
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.Some
                                        (sc,p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____9881,uu____9882) ->
                                              let tup2 =
                                                let uu____9884 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.parse_int "2")
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____9884
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____9888 =
                                                  let uu____9895 =
                                                    let uu____9896 =
                                                      let uu____9913 =
                                                        mk1
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let uu____9916 =
                                                        let uu____9927 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let uu____9936 =
                                                          let uu____9947 =
                                                            let uu____9956 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____9956
                                                             in
                                                          [uu____9947]  in
                                                        uu____9927 ::
                                                          uu____9936
                                                         in
                                                      (uu____9913,
                                                        uu____9916)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____9896
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____9895
                                                   in
                                                uu____9888
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range
                                                 in
                                              let p2 =
                                                let uu____10007 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____10007
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____10050,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____10052,pats)) ->
                                              let tupn =
                                                let uu____10095 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    ((Prims.parse_int "1") +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10095
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10107 =
                                                  let uu____10108 =
                                                    let uu____10125 =
                                                      mk1
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____10128 =
                                                      let uu____10139 =
                                                        let uu____10150 =
                                                          let uu____10159 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____10159
                                                           in
                                                        [uu____10150]  in
                                                      FStar_List.append args
                                                        uu____10139
                                                       in
                                                    (uu____10125,
                                                      uu____10128)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____10108
                                                   in
                                                mk1 uu____10107  in
                                              let p2 =
                                                let uu____10207 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats [(p1, false)])))
                                                  uu____10207
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____10248 ->
                                              failwith "Impossible")
                                      in
                                   ((x, aq), sc_pat_opt1)
                                in
                             (match uu____9647 with
                              | (b1,sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest))
                     in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____10341,uu____10342,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____10364 =
                let uu____10365 = unparen e  in
                uu____10365.FStar_Parser_AST.tm  in
              match uu____10364 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____10375 ->
                  let uu____10376 = desugar_term_aq env e  in
                  (match uu____10376 with
                   | (head1,aq) ->
                       let uu____10389 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____10389, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____10396 ->
            let rec aux args aqs e =
              let uu____10473 =
                let uu____10474 = unparen e  in
                uu____10474.FStar_Parser_AST.tm  in
              match uu____10473 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____10492 = desugar_term_aq env t  in
                  (match uu____10492 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____10540 ->
                  let uu____10541 = desugar_term_aq env e  in
                  (match uu____10541 with
                   | (head1,aq) ->
                       let uu____10562 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____10562, (join_aqs (aq :: aqs))))
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
            let uu____10622 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____10622
        | FStar_Parser_AST.Seq (t1,t2) ->
            let t =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Let
                   (FStar_Parser_AST.NoLetQualifier,
                     [(FStar_Pervasives_Native.None,
                        ((FStar_Parser_AST.mk_pattern
                            (FStar_Parser_AST.PatWild
                               FStar_Pervasives_Native.None)
                            t1.FStar_Parser_AST.range), t1))], t2))
                top.FStar_Parser_AST.range FStar_Parser_AST.Expr
               in
            let uu____10674 = desugar_term_aq env t  in
            (match uu____10674 with
             | (tm,s) ->
                 let uu____10685 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____10685, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____10691 =
              let uu____10704 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____10704 then desugar_typ_aq else desugar_term_aq  in
            uu____10691 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____10759 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____10902  ->
                        match uu____10902 with
                        | (attr_opt,(p,def)) ->
                            let uu____10960 = is_app_pattern p  in
                            if uu____10960
                            then
                              let uu____10991 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____10991, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____11073 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____11073, def1)
                               | uu____11118 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____11156);
                                           FStar_Parser_AST.prange =
                                             uu____11157;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____11205 =
                                            let uu____11226 =
                                              let uu____11231 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____11231  in
                                            (uu____11226, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____11205, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____11322) ->
                                        if top_level
                                        then
                                          let uu____11357 =
                                            let uu____11378 =
                                              let uu____11383 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____11383  in
                                            (uu____11378, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____11357, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____11473 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____11504 =
                FStar_List.fold_left
                  (fun uu____11577  ->
                     fun uu____11578  ->
                       match (uu____11577, uu____11578) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____11686,uu____11687),uu____11688))
                           ->
                           let uu____11805 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____11831 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____11831 with
                                  | (env2,xx) ->
                                      let uu____11850 =
                                        let uu____11853 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____11853 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____11850))
                             | FStar_Util.Inr l ->
                                 let uu____11861 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (uu____11861, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____11805 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____11504 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____12009 =
                    match uu____12009 with
                    | (attrs_opt,(uu____12045,args,result_t),def) ->
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
                                let uu____12133 = is_comp_type env1 t  in
                                if uu____12133
                                then
                                  ((let uu____12135 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____12145 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____12145))
                                       in
                                    match uu____12135 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____12148 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____12150 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____12150))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____12148
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t)
                                 in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed (def, t1, tacopt))
                                def.FStar_Parser_AST.range
                                FStar_Parser_AST.Expr
                           in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____12157 ->
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
                              let uu____12172 =
                                let uu____12173 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____12173
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____12172
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
                  let uu____12250 = desugar_term_aq env' body  in
                  (match uu____12250 with
                   | (body1,aq) ->
                       let uu____12263 =
                         let uu____12266 =
                           let uu____12267 =
                             let uu____12280 =
                               FStar_Syntax_Subst.close rec_bindings1 body1
                                in
                             ((is_rec, lbs1), uu____12280)  in
                           FStar_Syntax_Syntax.Tm_let uu____12267  in
                         FStar_All.pipe_left mk1 uu____12266  in
                       (uu____12263, aq))
               in
            let ds_non_rec attrs_opt pat t1 t2 =
              let attrs =
                match attrs_opt with
                | FStar_Pervasives_Native.None  -> []
                | FStar_Pervasives_Native.Some l ->
                    FStar_List.map (desugar_term env) l
                 in
              let t11 = desugar_term env t1  in
              let uu____12353 =
                desugar_binding_pat_maybe_top top_level env pat  in
              match uu____12353 with
              | (env1,binder,pat1) ->
                  let uu____12375 =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let uu____12401 = desugar_term_aq env1 t2  in
                        (match uu____12401 with
                         | (body1,aq) ->
                             let fv =
                               let uu____12415 =
                                 FStar_Syntax_Util.incr_delta_qualifier t11
                                  in
                               FStar_Syntax_Syntax.lid_as_fv l uu____12415
                                 FStar_Pervasives_Native.None
                                in
                             let uu____12416 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t11,
                                            (t11.FStar_Syntax_Syntax.pos))]),
                                      body1))
                                in
                             (uu____12416, aq))
                    | LocalBinder (x,uu____12446) ->
                        let uu____12447 = desugar_term_aq env1 t2  in
                        (match uu____12447 with
                         | (body1,aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | ({
                                    FStar_Syntax_Syntax.v =
                                      FStar_Syntax_Syntax.Pat_wild
                                      uu____12461;
                                    FStar_Syntax_Syntax.p = uu____12462;_},uu____12463)::[]
                                   -> body1
                               | uu____12476 ->
                                   let uu____12479 =
                                     let uu____12486 =
                                       let uu____12487 =
                                         let uu____12510 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         let uu____12513 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1
                                            in
                                         (uu____12510, uu____12513)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____12487
                                        in
                                     FStar_Syntax_Syntax.mk uu____12486  in
                                   uu____12479 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range
                                in
                             let uu____12553 =
                               let uu____12556 =
                                 let uu____12557 =
                                   let uu____12570 =
                                     let uu____12573 =
                                       let uu____12574 =
                                         FStar_Syntax_Syntax.mk_binder x  in
                                       [uu____12574]  in
                                     FStar_Syntax_Subst.close uu____12573
                                       body2
                                      in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t11,
                                           (t11.FStar_Syntax_Syntax.pos))]),
                                     uu____12570)
                                    in
                                 FStar_Syntax_Syntax.Tm_let uu____12557  in
                               FStar_All.pipe_left mk1 uu____12556  in
                             (uu____12553, aq))
                     in
                  (match uu____12375 with | (tm,aq) -> (tm, aq))
               in
            let uu____12633 = FStar_List.hd lbs  in
            (match uu____12633 with
             | (attrs,(head_pat,defn)) ->
                 let uu____12677 = is_rec || (is_app_pattern head_pat)  in
                 if uu____12677
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____12690 =
                let uu____12691 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____12691  in
              mk1 uu____12690  in
            let uu____12692 = desugar_term_aq env t1  in
            (match uu____12692 with
             | (t1',aq1) ->
                 let uu____12703 = desugar_term_aq env t2  in
                 (match uu____12703 with
                  | (t2',aq2) ->
                      let uu____12714 = desugar_term_aq env t3  in
                      (match uu____12714 with
                       | (t3',aq3) ->
                           let uu____12725 =
                             let uu____12726 =
                               let uu____12727 =
                                 let uu____12750 =
                                   let uu____12767 =
                                     let uu____12782 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t2.FStar_Parser_AST.range
                                        in
                                     (uu____12782,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____12795 =
                                     let uu____12812 =
                                       let uu____12827 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t3.FStar_Parser_AST.range
                                          in
                                       (uu____12827,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____12812]  in
                                   uu____12767 :: uu____12795  in
                                 (t1', uu____12750)  in
                               FStar_Syntax_Syntax.Tm_match uu____12727  in
                             mk1 uu____12726  in
                           (uu____12725, (join_aqs [aq1; aq2; aq3])))))
        | FStar_Parser_AST.TryWith (e,branches) ->
            let r = top.FStar_Parser_AST.range  in
            let handler = FStar_Parser_AST.mk_function branches r r  in
            let body =
              FStar_Parser_AST.mk_function
                [((FStar_Parser_AST.mk_pattern
                     (FStar_Parser_AST.PatConst FStar_Const.Const_unit) r),
                   FStar_Pervasives_Native.None, e)] r r
               in
            let try_with_lid1 = FStar_Ident.lid_of_path ["try_with"] r  in
            let try_with1 =
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Var try_with_lid1) r
                FStar_Parser_AST.Expr
               in
            let a1 =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   (try_with1, body, FStar_Parser_AST.Nothing)) r
                top.FStar_Parser_AST.level
               in
            let a2 =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App (a1, handler, FStar_Parser_AST.Nothing))
                r top.FStar_Parser_AST.level
               in
            desugar_term_aq env a2
        | FStar_Parser_AST.Match (e,branches) ->
            let desugar_branch uu____13020 =
              match uu____13020 with
              | (pat,wopt,b) ->
                  let uu____13042 = desugar_match_pat env pat  in
                  (match uu____13042 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____13073 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____13073
                          in
                       let uu____13078 = desugar_term_aq env1 b  in
                       (match uu____13078 with
                        | (b1,aq) ->
                            let uu____13091 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____13091, aq)))
               in
            let uu____13096 = desugar_term_aq env e  in
            (match uu____13096 with
             | (e1,aq) ->
                 let uu____13107 =
                   let uu____13138 =
                     let uu____13171 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____13171 FStar_List.unzip  in
                   FStar_All.pipe_right uu____13138
                     (fun uu____13301  ->
                        match uu____13301 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____13107 with
                  | (brs,aqs) ->
                      let uu____13520 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____13520, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____13554 =
              let uu____13575 = is_comp_type env t  in
              if uu____13575
              then
                let comp = desugar_comp t.FStar_Parser_AST.range env t  in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____13626 = desugar_term_aq env t  in
                 match uu____13626 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____13554 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____13718 = desugar_term_aq env e  in
                 (match uu____13718 with
                  | (e1,aq) ->
                      let uu____13729 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____13729, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____13768,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____13809 = FStar_List.hd fields  in
              match uu____13809 with | (f,uu____13821) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____13867  ->
                        match uu____13867 with
                        | (g,uu____13873) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____13879,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____13893 =
                         let uu____13898 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____13898)
                          in
                       FStar_Errors.raise_error uu____13893
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
                  let uu____13906 =
                    let uu____13917 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____13948  ->
                              match uu____13948 with
                              | (f,uu____13958) ->
                                  let uu____13959 =
                                    let uu____13960 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____13960
                                     in
                                  (uu____13959, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____13917)  in
                  FStar_Parser_AST.Construct uu____13906
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____13978 =
                      let uu____13979 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____13979  in
                    FStar_Parser_AST.mk_term uu____13978
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____13981 =
                      let uu____13994 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____14024  ->
                                match uu____14024 with
                                | (f,uu____14034) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____13994)  in
                    FStar_Parser_AST.Record uu____13981  in
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
            let uu____14094 = desugar_term_aq env recterm1  in
            (match uu____14094 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____14110;
                         FStar_Syntax_Syntax.vars = uu____14111;_},args)
                      ->
                      let uu____14137 =
                        let uu____14138 =
                          let uu____14139 =
                            let uu____14156 =
                              let uu____14159 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____14160 =
                                let uu____14163 =
                                  let uu____14164 =
                                    let uu____14171 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____14171)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____14164
                                   in
                                FStar_Pervasives_Native.Some uu____14163  in
                              FStar_Syntax_Syntax.fvar uu____14159
                                FStar_Syntax_Syntax.delta_constant
                                uu____14160
                               in
                            (uu____14156, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____14139  in
                        FStar_All.pipe_left mk1 uu____14138  in
                      (uu____14137, s)
                  | uu____14200 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____14204 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____14204 with
              | (constrname,is_rec) ->
                  let uu____14219 = desugar_term_aq env e  in
                  (match uu____14219 with
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
                       let uu____14237 =
                         let uu____14238 =
                           let uu____14239 =
                             let uu____14256 =
                               let uu____14259 =
                                 let uu____14260 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____14260
                                  in
                               FStar_Syntax_Syntax.fvar uu____14259
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1")) qual
                                in
                             let uu____14261 =
                               let uu____14272 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____14272]  in
                             (uu____14256, uu____14261)  in
                           FStar_Syntax_Syntax.Tm_app uu____14239  in
                         FStar_All.pipe_left mk1 uu____14238  in
                       (uu____14237, s))))
        | FStar_Parser_AST.NamedTyp (uu____14309,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____14318 =
              let uu____14319 = FStar_Syntax_Subst.compress tm  in
              uu____14319.FStar_Syntax_Syntax.n  in
            (match uu____14318 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____14327 =
                   let uu___303_14328 =
                     let uu____14329 =
                       let uu____14330 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____14330  in
                     FStar_Syntax_Util.exp_string uu____14329  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___303_14328.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___303_14328.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____14327, noaqs)
             | uu____14331 ->
                 let uu____14332 =
                   let uu____14337 =
                     let uu____14338 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.strcat "VQuote, expected an fvar, got: "
                       uu____14338
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____14337)  in
                 FStar_Errors.raise_error uu____14332
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____14344 = desugar_term_aq env e  in
            (match uu____14344 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____14356 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____14356, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____14361 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____14362 =
              let uu____14363 =
                let uu____14370 = desugar_term env e  in (bv, uu____14370)
                 in
              [uu____14363]  in
            (uu____14361, uu____14362)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____14395 =
              let uu____14396 =
                let uu____14397 =
                  let uu____14404 = desugar_term env e  in (uu____14404, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____14397  in
              FStar_All.pipe_left mk1 uu____14396  in
            (uu____14395, noaqs)
        | uu____14409 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____14410 = desugar_formula env top  in
            (uu____14410, noaqs)
        | uu____14411 ->
            let uu____14412 =
              let uu____14417 =
                let uu____14418 = FStar_Parser_AST.term_to_string top  in
                Prims.strcat "Unexpected term: " uu____14418  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____14417)  in
            FStar_Errors.raise_error uu____14412 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____14424 -> false
    | uu____14433 -> true

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
           (fun uu____14470  ->
              match uu____14470 with
              | (a,imp) ->
                  let uu____14483 = desugar_term env a  in
                  arg_withimp_e imp uu____14483))

and (desugar_comp :
  FStar_Range.range ->
    FStar_Syntax_DsEnv.env ->
      FStar_Parser_AST.term ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun r  ->
    fun env  ->
      fun t  ->
        let fail1 err = FStar_Errors.raise_error err r  in
        let is_requires uu____14515 =
          match uu____14515 with
          | (t1,uu____14521) ->
              let uu____14522 =
                let uu____14523 = unparen t1  in
                uu____14523.FStar_Parser_AST.tm  in
              (match uu____14522 with
               | FStar_Parser_AST.Requires uu____14524 -> true
               | uu____14531 -> false)
           in
        let is_ensures uu____14541 =
          match uu____14541 with
          | (t1,uu____14547) ->
              let uu____14548 =
                let uu____14549 = unparen t1  in
                uu____14549.FStar_Parser_AST.tm  in
              (match uu____14548 with
               | FStar_Parser_AST.Ensures uu____14550 -> true
               | uu____14557 -> false)
           in
        let is_app head1 uu____14572 =
          match uu____14572 with
          | (t1,uu____14578) ->
              let uu____14579 =
                let uu____14580 = unparen t1  in
                uu____14580.FStar_Parser_AST.tm  in
              (match uu____14579 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____14582;
                      FStar_Parser_AST.level = uu____14583;_},uu____14584,uu____14585)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____14586 -> false)
           in
        let is_smt_pat uu____14596 =
          match uu____14596 with
          | (t1,uu____14602) ->
              let uu____14603 =
                let uu____14604 = unparen t1  in
                uu____14604.FStar_Parser_AST.tm  in
              (match uu____14603 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____14607);
                             FStar_Parser_AST.range = uu____14608;
                             FStar_Parser_AST.level = uu____14609;_},uu____14610)::uu____14611::[])
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
                             FStar_Parser_AST.range = uu____14650;
                             FStar_Parser_AST.level = uu____14651;_},uu____14652)::uu____14653::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
               | uu____14678 -> false)
           in
        let is_decreases = is_app "decreases"  in
        let pre_process_comp_typ t1 =
          let uu____14710 = head_and_args t1  in
          match uu____14710 with
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
                       FStar_Parser_AST.mk_pattern
                         (FStar_Parser_AST.PatWild
                            FStar_Pervasives_Native.None)
                         ens.FStar_Parser_AST.range
                        in
                     FStar_Parser_AST.mk_term
                       (FStar_Parser_AST.Abs ([wildpat], ens))
                       ens.FStar_Parser_AST.range FStar_Parser_AST.Expr
                      in
                   let thunk_ens uu____14808 =
                     match uu____14808 with
                     | (e,i) ->
                         let uu____14819 = thunk_ens_ e  in (uu____14819, i)
                      in
                   let fail_lemma uu____14831 =
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
                         let uu____14911 =
                           let uu____14918 =
                             let uu____14925 = thunk_ens ens  in
                             [uu____14925; nil_pat]  in
                           req_true :: uu____14918  in
                         unit_tm :: uu____14911
                     | req::ens::[] when
                         (is_requires req) && (is_ensures ens) ->
                         let uu____14972 =
                           let uu____14979 =
                             let uu____14986 = thunk_ens ens  in
                             [uu____14986; nil_pat]  in
                           req :: uu____14979  in
                         unit_tm :: uu____14972
                     | ens::smtpat::[] when
                         (((let uu____15035 = is_requires ens  in
                            Prims.op_Negation uu____15035) &&
                             (let uu____15037 = is_smt_pat ens  in
                              Prims.op_Negation uu____15037))
                            &&
                            (let uu____15039 = is_decreases ens  in
                             Prims.op_Negation uu____15039))
                           && (is_smt_pat smtpat)
                         ->
                         let uu____15040 =
                           let uu____15047 =
                             let uu____15054 = thunk_ens ens  in
                             [uu____15054; smtpat]  in
                           req_true :: uu____15047  in
                         unit_tm :: uu____15040
                     | ens::dec::[] when
                         (is_ensures ens) && (is_decreases dec) ->
                         let uu____15101 =
                           let uu____15108 =
                             let uu____15115 = thunk_ens ens  in
                             [uu____15115; nil_pat; dec]  in
                           req_true :: uu____15108  in
                         unit_tm :: uu____15101
                     | ens::dec::smtpat::[] when
                         ((is_ensures ens) && (is_decreases dec)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____15175 =
                           let uu____15182 =
                             let uu____15189 = thunk_ens ens  in
                             [uu____15189; smtpat; dec]  in
                           req_true :: uu____15182  in
                         unit_tm :: uu____15175
                     | req::ens::dec::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_decreases dec)
                         ->
                         let uu____15249 =
                           let uu____15256 =
                             let uu____15263 = thunk_ens ens  in
                             [uu____15263; nil_pat; dec]  in
                           req :: uu____15256  in
                         unit_tm :: uu____15249
                     | req::ens::smtpat::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____15323 =
                           let uu____15330 =
                             let uu____15337 = thunk_ens ens  in
                             [uu____15337; smtpat]  in
                           req :: uu____15330  in
                         unit_tm :: uu____15323
                     | req::ens::dec::smtpat::[] when
                         (((is_requires req) && (is_ensures ens)) &&
                            (is_smt_pat smtpat))
                           && (is_decreases dec)
                         ->
                         let uu____15402 =
                           let uu____15409 =
                             let uu____15416 = thunk_ens ens  in
                             [uu____15416; dec; smtpat]  in
                           req :: uu____15409  in
                         unit_tm :: uu____15402
                     | _other -> fail_lemma ()  in
                   let head_and_attributes =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) lemma
                      in
                   (head_and_attributes, args1)
               | FStar_Parser_AST.Name l when
                   FStar_Syntax_DsEnv.is_effect_name env l ->
                   let uu____15478 =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) l
                      in
                   (uu____15478, args)
               | FStar_Parser_AST.Name l when
                   (let uu____15506 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____15506
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   let uu____15507 =
                     let uu____15514 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_Tot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____15514, [])  in
                   (uu____15507, args)
               | FStar_Parser_AST.Name l when
                   (let uu____15532 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____15532
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                   ->
                   let uu____15533 =
                     let uu____15540 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_GTot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____15540, [])  in
                   (uu____15533, args)
               | FStar_Parser_AST.Name l when
                   (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                      ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                     || ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                   ->
                   let uu____15556 =
                     let uu____15563 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_Tot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____15563, [])  in
                   (uu____15556, [(t1, FStar_Parser_AST.Nothing)])
               | uu____15586 ->
                   let default_effect =
                     let uu____15588 = FStar_Options.ml_ish ()  in
                     if uu____15588
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____15591 =
                           FStar_Options.warn_default_effects ()  in
                         if uu____15591
                         then
                           FStar_Errors.log_issue
                             head1.FStar_Parser_AST.range
                             (FStar_Errors.Warning_UseDefaultEffect,
                               "Using default effect Tot")
                         else ());
                        FStar_Parser_Const.effect_Tot_lid)
                      in
                   let uu____15593 =
                     let uu____15600 =
                       FStar_Ident.set_lid_range default_effect
                         head1.FStar_Parser_AST.range
                        in
                     (uu____15600, [])  in
                   (uu____15593, [(t1, FStar_Parser_AST.Nothing)]))
           in
        let uu____15623 = pre_process_comp_typ t  in
        match uu____15623 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____15672 =
                  let uu____15677 =
                    let uu____15678 = FStar_Syntax_Print.lid_to_string eff
                       in
                    FStar_Util.format1 "Not enough args to effect %s"
                      uu____15678
                     in
                  (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____15677)  in
                fail1 uu____15672)
             else ();
             (let is_universe uu____15689 =
                match uu____15689 with
                | (uu____15694,imp) -> imp = FStar_Parser_AST.UnivApp  in
              let uu____15696 = FStar_Util.take is_universe args  in
              match uu____15696 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____15755  ->
                         match uu____15755 with
                         | (u,imp) -> desugar_universe u) universes
                     in
                  let uu____15762 =
                    let uu____15777 = FStar_List.hd args1  in
                    let uu____15786 = FStar_List.tl args1  in
                    (uu____15777, uu____15786)  in
                  (match uu____15762 with
                   | (result_arg,rest) ->
                       let result_typ =
                         desugar_typ env
                           (FStar_Pervasives_Native.fst result_arg)
                          in
                       let rest1 = desugar_args env rest  in
                       let uu____15841 =
                         let is_decrease uu____15879 =
                           match uu____15879 with
                           | (t1,uu____15889) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.pos = uu____15899;
                                       FStar_Syntax_Syntax.vars = uu____15900;_},uu____15901::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.decreases_lid
                                | uu____15940 -> false)
                            in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease)
                          in
                       (match uu____15841 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____16056  ->
                                      match uu____16056 with
                                      | (t1,uu____16066) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____16075,(arg,uu____16077)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____16116 -> failwith "impos")))
                               in
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
                                | uu____16133 -> false  in
                              (((is_empty decreases_clause) &&
                                  (is_empty rest2))
                                 && (is_empty cattributes))
                                && (is_empty universes1)
                               in
                            let uu____16144 =
                              no_additional_args &&
                                (FStar_Ident.lid_equals eff
                                   FStar_Parser_Const.effect_Tot_lid)
                               in
                            if uu____16144
                            then FStar_Syntax_Syntax.mk_Total result_typ
                            else
                              (let uu____16148 =
                                 no_additional_args &&
                                   (FStar_Ident.lid_equals eff
                                      FStar_Parser_Const.effect_GTot_lid)
                                  in
                               if uu____16148
                               then FStar_Syntax_Syntax.mk_GTotal result_typ
                               else
                                 (let flags1 =
                                    let uu____16155 =
                                      FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_Lemma_lid
                                       in
                                    if uu____16155
                                    then [FStar_Syntax_Syntax.LEMMA]
                                    else
                                      (let uu____16159 =
                                         FStar_Ident.lid_equals eff
                                           FStar_Parser_Const.effect_Tot_lid
                                          in
                                       if uu____16159
                                       then [FStar_Syntax_Syntax.TOTAL]
                                       else
                                         (let uu____16163 =
                                            FStar_Ident.lid_equals eff
                                              FStar_Parser_Const.effect_ML_lid
                                             in
                                          if uu____16163
                                          then [FStar_Syntax_Syntax.MLEFFECT]
                                          else
                                            (let uu____16167 =
                                               FStar_Ident.lid_equals eff
                                                 FStar_Parser_Const.effect_GTot_lid
                                                in
                                             if uu____16167
                                             then
                                               [FStar_Syntax_Syntax.SOMETRIVIAL]
                                             else [])))
                                     in
                                  let flags2 =
                                    FStar_List.append flags1 cattributes  in
                                  let rest3 =
                                    let uu____16185 =
                                      FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_Lemma_lid
                                       in
                                    if uu____16185
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
                                                  let uu____16274 =
                                                    FStar_Ident.set_lid_range
                                                      FStar_Parser_Const.pattern_lid
                                                      pat.FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_Syntax.fvar
                                                    uu____16274
                                                    FStar_Syntax_Syntax.delta_constant
                                                    FStar_Pervasives_Native.None
                                                   in
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  nil
                                                  [(pattern,
                                                     (FStar_Pervasives_Native.Some
                                                        FStar_Syntax_Syntax.imp_tag))]
                                                  FStar_Pervasives_Native.None
                                                  pat.FStar_Syntax_Syntax.pos
                                            | uu____16295 -> pat  in
                                          let uu____16296 =
                                            let uu____16307 =
                                              let uu____16318 =
                                                let uu____16327 =
                                                  FStar_Syntax_Syntax.mk
                                                    (FStar_Syntax_Syntax.Tm_meta
                                                       (pat1,
                                                         (FStar_Syntax_Syntax.Meta_desugared
                                                            FStar_Syntax_Syntax.Meta_smt_pat)))
                                                    FStar_Pervasives_Native.None
                                                    pat1.FStar_Syntax_Syntax.pos
                                                   in
                                                (uu____16327, aq)  in
                                              [uu____16318]  in
                                            ens :: uu____16307  in
                                          req :: uu____16296
                                      | uu____16368 -> rest2
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
                                    }))))))

and (desugar_formula :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun f  ->
      let connective s =
        match s with
        | "/\\" -> FStar_Pervasives_Native.Some FStar_Parser_Const.and_lid
        | "\\/" -> FStar_Pervasives_Native.Some FStar_Parser_Const.or_lid
        | "==>" -> FStar_Pervasives_Native.Some FStar_Parser_Const.imp_lid
        | "<==>" -> FStar_Pervasives_Native.Some FStar_Parser_Const.iff_lid
        | "~" -> FStar_Pervasives_Native.Some FStar_Parser_Const.not_lid
        | uu____16392 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___304_16413 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___304_16413.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___304_16413.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___305_16455 = b  in
             {
               FStar_Parser_AST.b = (uu___305_16455.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___305_16455.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___305_16455.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____16518 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____16518)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____16531 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____16531 with
             | (env1,a1) ->
                 let a2 =
                   let uu___306_16541 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___306_16541.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___306_16541.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____16567 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____16581 =
                     let uu____16584 =
                       let uu____16585 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____16585]  in
                     no_annot_abs uu____16584 body2  in
                   FStar_All.pipe_left setpos uu____16581  in
                 let uu____16606 =
                   let uu____16607 =
                     let uu____16624 =
                       let uu____16627 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____16627
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____16628 =
                       let uu____16639 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____16639]  in
                     (uu____16624, uu____16628)  in
                   FStar_Syntax_Syntax.Tm_app uu____16607  in
                 FStar_All.pipe_left mk1 uu____16606)
        | uu____16678 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____16758 = q (rest, pats, body)  in
              let uu____16765 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____16758 uu____16765
                FStar_Parser_AST.Formula
               in
            let uu____16766 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____16766 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____16775 -> failwith "impossible"  in
      let uu____16778 =
        let uu____16779 = unparen f  in uu____16779.FStar_Parser_AST.tm  in
      match uu____16778 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____16786,uu____16787) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____16798,uu____16799) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____16830 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____16830
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____16866 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____16866
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____16909 -> desugar_term env f

and (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                FStar_Pervasives_Native.tuple2 Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bs  ->
      let uu____16914 =
        FStar_List.fold_left
          (fun uu____16947  ->
             fun b  ->
               match uu____16947 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___307_16991 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___307_16991.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___307_16991.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___307_16991.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____17006 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____17006 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___308_17024 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___308_17024.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___308_17024.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____17025 =
                               let uu____17032 =
                                 let uu____17037 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____17037)  in
                               uu____17032 :: out  in
                             (env2, uu____17025))
                    | uu____17048 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____16914 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

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
          let uu____17119 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____17119)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____17124 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____17124)
      | FStar_Parser_AST.TVariable x ->
          let uu____17128 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____17128)
      | FStar_Parser_AST.NoName t ->
          let uu____17132 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____17132)
      | FStar_Parser_AST.Variable x ->
          ((FStar_Pervasives_Native.Some x), FStar_Syntax_Syntax.tun)

and (as_binder :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      (FStar_Ident.ident FStar_Pervasives_Native.option,FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.tuple2 ->
        ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                                   FStar_Pervasives_Native.option)
           FStar_Pervasives_Native.tuple2,FStar_Syntax_DsEnv.env)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun imp  ->
      fun uu___260_17140  ->
        match uu___260_17140 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____17162 = FStar_Syntax_Syntax.null_binder k  in
            (uu____17162, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____17179 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____17179 with
             | (env1,a1) ->
                 let uu____17196 =
                   let uu____17203 = trans_aqual env1 imp  in
                   ((let uu___309_17209 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___309_17209.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___309_17209.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____17203)
                    in
                 (uu____17196, env1))

and (trans_aqual :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___261_17217  ->
      match uu___261_17217 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____17221 =
            let uu____17222 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____17222  in
          FStar_Pervasives_Native.Some uu____17221
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None

let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b  ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x,uu____17237) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x,uu____17239) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu____17242 -> FStar_Pervasives_Native.None
  
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs  ->
    FStar_List.collect
      (fun b  ->
         let uu____17259 = binder_ident b  in
         FStar_Common.list_of_option uu____17259) bs
  
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
               (fun uu___262_17295  ->
                  match uu___262_17295 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____17296 -> false))
           in
        let quals2 q =
          let uu____17309 =
            (let uu____17312 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____17312) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____17309
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____17326 = FStar_Ident.range_of_lid disc_name  in
                let uu____17327 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____17326;
                  FStar_Syntax_Syntax.sigquals = uu____17327;
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
  fun iquals  ->
    fun fvq  ->
      fun env  ->
        fun lid  ->
          fun fields  ->
            let p = FStar_Ident.range_of_lid lid  in
            let uu____17366 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____17404  ->
                        match uu____17404 with
                        | (x,uu____17414) ->
                            let uu____17419 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____17419 with
                             | (field_name,uu____17427) ->
                                 let only_decl =
                                   ((let uu____17431 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____17431)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____17433 =
                                        let uu____17434 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____17434.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____17433)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____17450 =
                                       FStar_List.filter
                                         (fun uu___263_17454  ->
                                            match uu___263_17454 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____17455 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____17450
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___264_17468  ->
                                             match uu___264_17468 with
                                             | FStar_Syntax_Syntax.NoExtract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____17469 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____17471 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____17471;
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____17476 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____17476
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          (FStar_Syntax_Syntax.Delta_equational_at_level
                                             (Prims.parse_int "1"))
                                      else
                                        FStar_Syntax_Syntax.Delta_equational_at_level
                                          (Prims.parse_int "1")
                                       in
                                    let lb =
                                      let uu____17481 =
                                        let uu____17486 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____17486  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____17481;
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
                                      let uu____17490 =
                                        let uu____17491 =
                                          let uu____17498 =
                                            let uu____17501 =
                                              let uu____17502 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____17502
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____17501]  in
                                          ((false, [lb]), uu____17498)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____17491
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____17490;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____17366 FStar_List.flatten
  
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
            (lid,uu____17546,t,uu____17548,n1,uu____17550) when
            let uu____17555 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____17555 ->
            let uu____17556 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____17556 with
             | (formals,uu____17574) ->
                 (match formals with
                  | [] -> []
                  | uu____17603 ->
                      let filter_records uu___265_17619 =
                        match uu___265_17619 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____17622,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____17634 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____17636 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____17636 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Syntax_Syntax.Data_ctor
                        | FStar_Pervasives_Native.Some q -> q  in
                      let iquals1 =
                        if
                          (FStar_List.contains FStar_Syntax_Syntax.Abstract
                             iquals)
                            &&
                            (Prims.op_Negation
                               (FStar_List.contains
                                  FStar_Syntax_Syntax.Private iquals))
                        then FStar_Syntax_Syntax.Private :: iquals
                        else iquals  in
                      let uu____17646 = FStar_Util.first_N n1 formals  in
                      (match uu____17646 with
                       | (uu____17675,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____17709 -> []
  
let (mk_typ_abbrev :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                                FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Ident.lident Prims.list ->
              FStar_Syntax_Syntax.qualifier Prims.list ->
                FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun lid  ->
    fun uvs  ->
      fun typars  ->
        fun kopt  ->
          fun t  ->
            fun lids  ->
              fun quals  ->
                fun rng  ->
                  let dd =
                    let uu____17787 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____17787
                    then
                      let uu____17790 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____17790
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____17793 =
                      let uu____17798 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____17798  in
                    let uu____17799 =
                      if FStar_Util.is_some kopt
                      then
                        let uu____17804 =
                          let uu____17807 =
                            FStar_All.pipe_right kopt FStar_Util.must  in
                          FStar_Syntax_Syntax.mk_Total uu____17807  in
                        FStar_Syntax_Util.arrow typars uu____17804
                      else FStar_Syntax_Syntax.tun  in
                    let uu____17811 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____17793;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____17799;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____17811;
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
          let tycon_id uu___266_17862 =
            match uu___266_17862 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____17864,uu____17865) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____17875,uu____17876,uu____17877) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____17887,uu____17888,uu____17889) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____17919,uu____17920,uu____17921) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____17965) ->
                let uu____17966 =
                  let uu____17967 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____17967  in
                FStar_Parser_AST.mk_term uu____17966 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____17969 =
                  let uu____17970 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____17970  in
                FStar_Parser_AST.mk_term uu____17969 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____17972) ->
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
              | uu____18003 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____18011 =
                     let uu____18012 =
                       let uu____18019 = binder_to_term b  in
                       (out, uu____18019, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____18012  in
                   FStar_Parser_AST.mk_term uu____18011
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___267_18031 =
            match uu___267_18031 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____18086  ->
                       match uu____18086 with
                       | (x,t,uu____18097) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated (x, t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____18103 =
                    let uu____18104 =
                      let uu____18105 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____18105  in
                    FStar_Parser_AST.mk_term uu____18104
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____18103 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let names1 =
                  let uu____18112 = binder_idents parms  in id1 ::
                    uu____18112
                   in
                (FStar_List.iter
                   (fun uu____18130  ->
                      match uu____18130 with
                      | (f,uu____18140,uu____18141) ->
                          let uu____18146 =
                            FStar_Util.for_some
                              (fun i  -> FStar_Ident.ident_equals f i) names1
                             in
                          if uu____18146
                          then
                            let uu____18149 =
                              let uu____18154 =
                                let uu____18155 =
                                  FStar_Ident.string_of_ident f  in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu____18155
                                 in
                              (FStar_Errors.Error_FieldShadow, uu____18154)
                               in
                            FStar_Errors.raise_error uu____18149
                              f.FStar_Ident.idRange
                          else ()) fields;
                 (let uu____18157 =
                    FStar_All.pipe_right fields
                      (FStar_List.map
                         (fun uu____18184  ->
                            match uu____18184 with
                            | (x,uu____18194,uu____18195) -> x))
                     in
                  ((FStar_Parser_AST.TyconVariant
                      (id1, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp),
                           FStar_Pervasives_Native.None, false)])),
                    uu____18157)))
            | uu____18248 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___268_18287 =
            match uu___268_18287 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____18311 = typars_of_binders _env binders  in
                (match uu____18311 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____18347 =
                         let uu____18348 =
                           let uu____18349 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____18349  in
                         FStar_Parser_AST.mk_term uu____18348
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____18347 binders  in
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
                         FStar_Syntax_Syntax.delta_constant
                        in
                     let _env2 =
                       FStar_Syntax_DsEnv.push_top_level_rec_binding _env'
                         id1 FStar_Syntax_Syntax.delta_constant
                        in
                     (_env1, _env2, se, tconstr))
            | uu____18360 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____18402 =
              FStar_List.fold_left
                (fun uu____18436  ->
                   fun uu____18437  ->
                     match (uu____18436, uu____18437) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____18506 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____18506 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____18402 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____18597 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____18597
                | uu____18598 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____18606 = desugar_abstract_tc quals env [] tc  in
              (match uu____18606 with
               | (uu____18619,uu____18620,se,uu____18622) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____18625,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____18642 =
                                 let uu____18643 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____18643  in
                               if uu____18642
                               then
                                 let uu____18644 =
                                   let uu____18649 =
                                     let uu____18650 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____18650
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____18649)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____18644
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
                           | uu____18659 ->
                               let uu____18660 =
                                 let uu____18667 =
                                   let uu____18668 =
                                     let uu____18683 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____18683)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____18668
                                    in
                                 FStar_Syntax_Syntax.mk uu____18667  in
                               uu____18660 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___310_18699 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___310_18699.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___310_18699.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___310_18699.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____18700 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____18703 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____18703
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____18716 = typars_of_binders env binders  in
              (match uu____18716 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____18750 =
                           FStar_Util.for_some
                             (fun uu___269_18752  ->
                                match uu___269_18752 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____18753 -> false) quals
                            in
                         if uu____18750
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____18758 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____18758
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____18763 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___270_18767  ->
                               match uu___270_18767 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____18768 -> false))
                        in
                     if uu____18763
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____18777 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____18777
                     then
                       let uu____18780 =
                         let uu____18787 =
                           let uu____18788 = unparen t  in
                           uu____18788.FStar_Parser_AST.tm  in
                         match uu____18787 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____18809 =
                               match FStar_List.rev args with
                               | (last_arg,uu____18839)::args_rev ->
                                   let uu____18851 =
                                     let uu____18852 = unparen last_arg  in
                                     uu____18852.FStar_Parser_AST.tm  in
                                   (match uu____18851 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____18880 -> ([], args))
                               | uu____18889 -> ([], args)  in
                             (match uu____18809 with
                              | (cattributes,args1) ->
                                  let uu____18928 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____18928))
                         | uu____18939 -> (t, [])  in
                       match uu____18780 with
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
                                  (fun uu___271_18961  ->
                                     match uu___271_18961 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____18962 -> true))
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
                        mk_typ_abbrev qlid [] typars kopt1 t1 [qlid] quals1
                          rng)
                      in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in
                   let env2 =
                     FStar_Syntax_DsEnv.push_doc env1 qlid
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se]))
          | (FStar_Parser_AST.TyconRecord uu____18969)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____18993 = tycon_record_as_variant trec  in
              (match uu____18993 with
               | (t,fs) ->
                   let uu____19010 =
                     let uu____19013 =
                       let uu____19014 =
                         let uu____19023 =
                           let uu____19026 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____19026  in
                         (uu____19023, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____19014  in
                     uu____19013 :: quals  in
                   desugar_tycon env d uu____19010 [t])
          | uu____19031::uu____19032 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____19199 = et  in
                match uu____19199 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____19424 ->
                         let trec = tc  in
                         let uu____19448 = tycon_record_as_variant trec  in
                         (match uu____19448 with
                          | (t,fs) ->
                              let uu____19507 =
                                let uu____19510 =
                                  let uu____19511 =
                                    let uu____19520 =
                                      let uu____19523 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____19523  in
                                    (uu____19520, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____19511
                                   in
                                uu____19510 :: quals1  in
                              collect_tcs uu____19507 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____19610 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____19610 with
                          | (env2,uu____19670,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____19819 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____19819 with
                          | (env2,uu____19879,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____20004 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____20051 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____20051 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___273_20556  ->
                             match uu___273_20556 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____20621,uu____20622);
                                    FStar_Syntax_Syntax.sigrng = uu____20623;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____20624;
                                    FStar_Syntax_Syntax.sigmeta = uu____20625;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____20626;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____20689 =
                                     typars_of_binders env1 binders  in
                                   match uu____20689 with
                                   | (env2,tpars1) ->
                                       let uu____20716 =
                                         push_tparams env2 tpars1  in
                                       (match uu____20716 with
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
                                 let uu____20745 =
                                   let uu____20764 =
                                     mk_typ_abbrev id1 uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____20764)
                                    in
                                 [uu____20745]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____20824);
                                    FStar_Syntax_Syntax.sigrng = uu____20825;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____20827;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____20828;_},constrs,tconstr,quals1)
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
                                 let uu____20926 = push_tparams env1 tpars
                                    in
                                 (match uu____20926 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____20993  ->
                                             match uu____20993 with
                                             | (x,uu____21005) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____21009 =
                                        let uu____21036 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____21144  ->
                                                  match uu____21144 with
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
                                                        let uu____21198 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____21198
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
                                                                uu___272_21209
                                                                 ->
                                                                match uu___272_21209
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____21221
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____21229 =
                                                        let uu____21248 =
                                                          let uu____21249 =
                                                            let uu____21250 =
                                                              let uu____21265
                                                                =
                                                                let uu____21266
                                                                  =
                                                                  let uu____21269
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____21269
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____21266
                                                                 in
                                                              (name, univs1,
                                                                uu____21265,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____21250
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____21249;
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
                                                          uu____21248)
                                                         in
                                                      (name, uu____21229)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____21036
                                         in
                                      (match uu____21009 with
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
                             | uu____21484 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____21610  ->
                             match uu____21610 with
                             | (name_doc,uu____21636,uu____21637) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____21709  ->
                             match uu____21709 with
                             | (uu____21728,uu____21729,se) -> se))
                      in
                   let uu____21755 =
                     let uu____21762 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____21762 rng
                      in
                   (match uu____21755 with
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
                               (fun uu____21824  ->
                                  match uu____21824 with
                                  | (uu____21845,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____21892,tps,k,uu____21895,constrs)
                                      when
                                      (FStar_List.length constrs) >
                                        (Prims.parse_int "1")
                                      ->
                                      let quals1 =
                                        se.FStar_Syntax_Syntax.sigquals  in
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
                                        else quals1  in
                                      mk_data_discriminators quals2 env3
                                        constrs
                                  | uu____21914 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____21931  ->
                                 match uu____21931 with
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
      (FStar_Syntax_DsEnv.env,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                                                        FStar_Pervasives_Native.option)
                                FStar_Pervasives_Native.tuple2 Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun binders  ->
      let uu____21974 =
        FStar_List.fold_left
          (fun uu____22009  ->
             fun b  ->
               match uu____22009 with
               | (env1,binders1) ->
                   let uu____22053 = desugar_binder env1 b  in
                   (match uu____22053 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____22076 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____22076 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____22129 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____21974 with
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
          let uu____22230 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___274_22235  ->
                    match uu___274_22235 with
                    | FStar_Syntax_Syntax.Reflectable uu____22236 -> true
                    | uu____22237 -> false))
             in
          if uu____22230
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____22240 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____22240
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
  
let (get_fail_attr :
  Prims.bool ->
    FStar_Syntax_Syntax.term ->
      (Prims.int Prims.list,Prims.bool) FStar_Pervasives_Native.tuple2
        FStar_Pervasives_Native.option)
  =
  fun warn  ->
    fun at1  ->
      let uu____22272 = FStar_Syntax_Util.head_and_args at1  in
      match uu____22272 with
      | (hd1,args) ->
          let uu____22323 =
            let uu____22338 =
              let uu____22339 = FStar_Syntax_Subst.compress hd1  in
              uu____22339.FStar_Syntax_Syntax.n  in
            (uu____22338, args)  in
          (match uu____22323 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(a1,uu____22362)::[]) when
               (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr)
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.fail_lax_attr)
               ->
               let uu____22397 =
                 let uu____22402 =
                   let uu____22411 =
                     FStar_Syntax_Embeddings.e_list
                       FStar_Syntax_Embeddings.e_int
                      in
                   FStar_Syntax_Embeddings.unembed uu____22411 a1  in
                 uu____22402 true FStar_Syntax_Embeddings.id_norm_cb  in
               (match uu____22397 with
                | FStar_Pervasives_Native.Some es when
                    (FStar_List.length es) > (Prims.parse_int "0") ->
                    let b =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.fail_lax_attr
                       in
                    let uu____22436 =
                      let uu____22443 =
                        FStar_List.map FStar_BigInt.to_int_fs es  in
                      (uu____22443, b)  in
                    FStar_Pervasives_Native.Some uu____22436
                | uu____22454 ->
                    (if warn
                     then
                       FStar_Errors.log_issue at1.FStar_Syntax_Syntax.pos
                         (FStar_Errors.Warning_UnappliedFail,
                           "Found ill-applied 'expect_failure', argument should be a non-empty list of integer literals")
                     else ();
                     FStar_Pervasives_Native.None))
           | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
               (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr)
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.fail_lax_attr)
               ->
               let b =
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.fail_lax_attr
                  in
               FStar_Pervasives_Native.Some ([], b)
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____22496) when
               (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr)
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.fail_lax_attr)
               ->
               (if warn
                then
                  FStar_Errors.log_issue at1.FStar_Syntax_Syntax.pos
                    (FStar_Errors.Warning_UnappliedFail,
                      "Found ill-applied 'expect_failure', argument should be a non-empty list of integer literals")
                else ();
                FStar_Pervasives_Native.None)
           | uu____22525 -> FStar_Pervasives_Native.None)
  
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
                  let uu____22694 = desugar_binders monad_env eff_binders  in
                  match uu____22694 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let for_free =
                        let uu____22733 =
                          let uu____22734 =
                            let uu____22743 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____22743  in
                          FStar_List.length uu____22734  in
                        uu____22733 = (Prims.parse_int "1")  in
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
                            (uu____22789,uu____22790,(FStar_Parser_AST.TyconAbbrev
                                                      (name,uu____22792,uu____22793,uu____22794),uu____22795)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____22828 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____22829 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____22841 = name_of_eff_decl decl  in
                             FStar_List.mem uu____22841 mandatory_members)
                          eff_decls
                         in
                      (match uu____22829 with
                       | (mandatory_members_decls,actions) ->
                           let uu____22858 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____22887  ->
                                     fun decl  ->
                                       match uu____22887 with
                                       | (env2,out) ->
                                           let uu____22907 =
                                             desugar_decl env2 decl  in
                                           (match uu____22907 with
                                            | (env3,ses) ->
                                                let uu____22920 =
                                                  let uu____22923 =
                                                    FStar_List.hd ses  in
                                                  uu____22923 :: out  in
                                                (env3, uu____22920)))
                                  (env1, []))
                              in
                           (match uu____22858 with
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
                                              (uu____22992,uu____22993,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____22996,
                                                 {
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.Construct
                                                     (uu____22997,(def,uu____22999)::
                                                      (cps_type,uu____23001)::[]);
                                                   FStar_Parser_AST.range =
                                                     uu____23002;
                                                   FStar_Parser_AST.level =
                                                     uu____23003;_}),doc1)::[])
                                              when Prims.op_Negation for_free
                                              ->
                                              let uu____23055 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____23055 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____23093 =
                                                     let uu____23094 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____23095 =
                                                       let uu____23096 =
                                                         desugar_term env3
                                                           def
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____23096
                                                        in
                                                     let uu____23103 =
                                                       let uu____23104 =
                                                         desugar_typ env3
                                                           cps_type
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____23104
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____23094;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____23095;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____23103
                                                     }  in
                                                   (uu____23093, doc1))
                                          | FStar_Parser_AST.Tycon
                                              (uu____23113,uu____23114,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____23117,defn),doc1)::[])
                                              when for_free ->
                                              let uu____23152 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____23152 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____23190 =
                                                     let uu____23191 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____23192 =
                                                       let uu____23193 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____23193
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____23191;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____23192;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____23190, doc1))
                                          | uu____23202 ->
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
                                    let uu____23234 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____23234
                                     in
                                  let uu____23235 =
                                    let uu____23236 =
                                      FStar_Syntax_DsEnv.fail_or env2
                                        (FStar_Syntax_DsEnv.try_lookup_definition
                                           env2) l
                                       in
                                    FStar_All.pipe_left
                                      (FStar_Syntax_Subst.close binders1)
                                      uu____23236
                                     in
                                  ([], uu____23235)  in
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
                                      let uu____23253 =
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      ([], uu____23253)  in
                                    let uu____23260 =
                                      let uu____23261 =
                                        let uu____23262 =
                                          let uu____23263 = lookup1 "repr"
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____23263
                                           in
                                        let uu____23272 = lookup1 "return"
                                           in
                                        let uu____23273 = lookup1 "bind"  in
                                        let uu____23274 =
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
                                            uu____23262;
                                          FStar_Syntax_Syntax.return_repr =
                                            uu____23272;
                                          FStar_Syntax_Syntax.bind_repr =
                                            uu____23273;
                                          FStar_Syntax_Syntax.actions =
                                            actions1;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            uu____23274
                                        }  in
                                      FStar_Syntax_Syntax.Sig_new_effect_for_free
                                        uu____23261
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____23260;
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
                                         (fun uu___275_23280  ->
                                            match uu___275_23280 with
                                            | FStar_Syntax_Syntax.Reifiable 
                                                -> true
                                            | FStar_Syntax_Syntax.Reflectable
                                                uu____23281 -> true
                                            | uu____23282 -> false)
                                         qualifiers
                                        in
                                     let un_ts =
                                       ([], FStar_Syntax_Syntax.tun)  in
                                     let uu____23296 =
                                       let uu____23297 =
                                         let uu____23298 =
                                           lookup1 "return_wp"  in
                                         let uu____23299 = lookup1 "bind_wp"
                                            in
                                         let uu____23300 =
                                           lookup1 "if_then_else"  in
                                         let uu____23301 = lookup1 "ite_wp"
                                            in
                                         let uu____23302 = lookup1 "stronger"
                                            in
                                         let uu____23303 = lookup1 "close_wp"
                                            in
                                         let uu____23304 = lookup1 "assert_p"
                                            in
                                         let uu____23305 = lookup1 "assume_p"
                                            in
                                         let uu____23306 = lookup1 "null_wp"
                                            in
                                         let uu____23307 = lookup1 "trivial"
                                            in
                                         let uu____23308 =
                                           if rr
                                           then
                                             let uu____23309 = lookup1 "repr"
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.snd
                                               uu____23309
                                           else FStar_Syntax_Syntax.tun  in
                                         let uu____23325 =
                                           if rr
                                           then lookup1 "return"
                                           else un_ts  in
                                         let uu____23327 =
                                           if rr
                                           then lookup1 "bind"
                                           else un_ts  in
                                         let uu____23329 =
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
                                             uu____23298;
                                           FStar_Syntax_Syntax.bind_wp =
                                             uu____23299;
                                           FStar_Syntax_Syntax.if_then_else =
                                             uu____23300;
                                           FStar_Syntax_Syntax.ite_wp =
                                             uu____23301;
                                           FStar_Syntax_Syntax.stronger =
                                             uu____23302;
                                           FStar_Syntax_Syntax.close_wp =
                                             uu____23303;
                                           FStar_Syntax_Syntax.assert_p =
                                             uu____23304;
                                           FStar_Syntax_Syntax.assume_p =
                                             uu____23305;
                                           FStar_Syntax_Syntax.null_wp =
                                             uu____23306;
                                           FStar_Syntax_Syntax.trivial =
                                             uu____23307;
                                           FStar_Syntax_Syntax.repr =
                                             uu____23308;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____23325;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____23327;
                                           FStar_Syntax_Syntax.actions =
                                             actions1;
                                           FStar_Syntax_Syntax.eff_attrs =
                                             uu____23329
                                         }  in
                                       FStar_Syntax_Syntax.Sig_new_effect
                                         uu____23297
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         uu____23296;
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
                                          fun uu____23355  ->
                                            match uu____23355 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____23369 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____23369
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
                let uu____23393 = desugar_binders env1 eff_binders  in
                match uu____23393 with
                | (env2,binders) ->
                    let uu____23430 =
                      let uu____23441 = head_and_args defn  in
                      match uu____23441 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____23478 ->
                                let uu____23479 =
                                  let uu____23484 =
                                    let uu____23485 =
                                      let uu____23486 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.strcat uu____23486 " not found"
                                       in
                                    Prims.strcat "Effect " uu____23485  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____23484)
                                   in
                                FStar_Errors.raise_error uu____23479
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____23488 =
                            match FStar_List.rev args with
                            | (last_arg,uu____23518)::args_rev ->
                                let uu____23530 =
                                  let uu____23531 = unparen last_arg  in
                                  uu____23531.FStar_Parser_AST.tm  in
                                (match uu____23530 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____23559 -> ([], args))
                            | uu____23568 -> ([], args)  in
                          (match uu____23488 with
                           | (cattributes,args1) ->
                               let uu____23611 = desugar_args env2 args1  in
                               let uu____23612 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____23611, uu____23612))
                       in
                    (match uu____23430 with
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
                          (let uu____23648 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____23648 with
                           | (ed_binders,uu____23662,ed_binders_opening) ->
                               let sub1 uu____23675 =
                                 match uu____23675 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____23689 =
                                         FStar_Syntax_Subst.shift_subst
                                           (FStar_List.length us)
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____23689 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____23693 =
                                       let uu____23694 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____23694)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____23693
                                  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____23703 =
                                   let uu____23704 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____23704
                                    in
                                 let uu____23719 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____23720 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____23721 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____23722 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____23723 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____23724 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____23725 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____23726 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____23727 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____23728 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____23729 =
                                   let uu____23730 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____23730
                                    in
                                 let uu____23745 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____23746 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____23747 =
                                   FStar_List.map
                                     (fun action  ->
                                        let uu____23755 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____23756 =
                                          let uu____23757 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____23757
                                           in
                                        let uu____23772 =
                                          let uu____23773 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____23773
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____23755;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____23756;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____23772
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
                                     uu____23703;
                                   FStar_Syntax_Syntax.ret_wp = uu____23719;
                                   FStar_Syntax_Syntax.bind_wp = uu____23720;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____23721;
                                   FStar_Syntax_Syntax.ite_wp = uu____23722;
                                   FStar_Syntax_Syntax.stronger = uu____23723;
                                   FStar_Syntax_Syntax.close_wp = uu____23724;
                                   FStar_Syntax_Syntax.assert_p = uu____23725;
                                   FStar_Syntax_Syntax.assume_p = uu____23726;
                                   FStar_Syntax_Syntax.null_wp = uu____23727;
                                   FStar_Syntax_Syntax.trivial = uu____23728;
                                   FStar_Syntax_Syntax.repr = uu____23729;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____23745;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____23746;
                                   FStar_Syntax_Syntax.actions = uu____23747;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____23790 =
                                     let uu____23791 =
                                       let uu____23800 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____23800
                                        in
                                     FStar_List.length uu____23791  in
                                   uu____23790 = (Prims.parse_int "1")  in
                                 let uu____23831 =
                                   let uu____23834 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____23834 quals  in
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
                                   FStar_Syntax_Syntax.sigquals = uu____23831;
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
                                             let uu____23856 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____23856
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____23858 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____23858
                                 then
                                   let reflect_lid =
                                     let uu____23862 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____23862
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
    let uu____23872 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____23872 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.strcat "  " (Prims.strcat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____23923 ->
              let uu____23924 =
                let uu____23925 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____23925
                 in
              Prims.strcat "\n  " uu____23924
          | uu____23926 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____23939  ->
               match uu____23939 with
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
          let uu____23957 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____23957
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____23959 =
          let uu____23970 = FStar_Syntax_Syntax.as_arg arg  in [uu____23970]
           in
        FStar_Syntax_Util.mk_app fv uu____23959

and (desugar_decl_aux :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      let uu____24001 = desugar_decl_noattrs env d  in
      match uu____24001 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____24019 = mk_comment_attr d  in uu____24019 :: attrs1  in
          let uu____24020 =
            FStar_List.mapi
              (fun i  ->
                 fun sigelt  ->
                   if i = (Prims.parse_int "0")
                   then
                     let uu___311_24026 = sigelt  in
                     {
                       FStar_Syntax_Syntax.sigel =
                         (uu___311_24026.FStar_Syntax_Syntax.sigel);
                       FStar_Syntax_Syntax.sigrng =
                         (uu___311_24026.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___311_24026.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___311_24026.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs = attrs2
                     }
                   else
                     (let uu___312_24028 = sigelt  in
                      let uu____24029 =
                        FStar_List.filter
                          (fun at1  ->
                             let uu____24035 = get_fail_attr false at1  in
                             FStar_Option.isNone uu____24035) attrs2
                         in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___312_24028.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___312_24028.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___312_24028.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___312_24028.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs = uu____24029
                      })) sigelts
             in
          (env1, uu____24020)

and (desugar_decl :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      let uu____24056 = desugar_decl_aux env d  in
      match uu____24056 with
      | (env1,ses) ->
          let uu____24067 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____24067)

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
          let p1 = trans_pragma p  in
          (FStar_Syntax_Util.process_pragma p1 d.FStar_Parser_AST.drange;
           (let se =
              {
                FStar_Syntax_Syntax.sigel =
                  (FStar_Syntax_Syntax.Sig_pragma p1);
                FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta;
                FStar_Syntax_Syntax.sigattrs = []
              }  in
            (env, [se])))
      | FStar_Parser_AST.Fsdoc uu____24095 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Friend lid ->
          let uu____24100 = FStar_Syntax_DsEnv.iface env  in
          if uu____24100
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____24110 =
               let uu____24111 =
                 let uu____24112 = FStar_Syntax_DsEnv.dep_graph env  in
                 let uu____24113 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Parser_Dep.module_has_interface uu____24112
                   uu____24113
                  in
               Prims.op_Negation uu____24111  in
             if uu____24110
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____24123 =
                  let uu____24124 =
                    let uu____24125 = FStar_Syntax_DsEnv.dep_graph env  in
                    FStar_Parser_Dep.module_has_interface uu____24125 lid  in
                  Prims.op_Negation uu____24124  in
                if uu____24123
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____24135 =
                     let uu____24136 =
                       let uu____24137 = FStar_Syntax_DsEnv.dep_graph env  in
                       FStar_Parser_Dep.deps_has_implementation uu____24137
                         lid
                        in
                     Prims.op_Negation uu____24136  in
                   if uu____24135
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____24151 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____24151, [])
      | FStar_Parser_AST.Tycon (is_effect,typeclass,tcs) ->
          let quals = d.FStar_Parser_AST.quals  in
          let quals1 =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: quals
            else quals  in
          let quals2 =
            if typeclass
            then
              match tcs with
              | (FStar_Parser_AST.TyconRecord uu____24185,uu____24186)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu____24225 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1  in
          let tcs1 =
            FStar_List.map
              (fun uu____24249  ->
                 match uu____24249 with | (x,uu____24257) -> x) tcs
             in
          let uu____24262 =
            let uu____24267 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____24267 tcs1  in
          (match uu____24262 with
           | (env1,ses) ->
               let mkclass lid =
                 let uu____24284 =
                   let uu____24285 =
                     let uu____24292 =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun
                        in
                     FStar_Syntax_Syntax.mk_binder uu____24292  in
                   [uu____24285]  in
                 let uu____24305 =
                   let uu____24308 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____24311 =
                     let uu____24322 =
                       let uu____24331 =
                         let uu____24332 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____24332  in
                       FStar_Syntax_Syntax.as_arg uu____24331  in
                     [uu____24322]  in
                   FStar_Syntax_Util.mk_app uu____24308 uu____24311  in
                 FStar_Syntax_Util.abs uu____24284 uu____24305
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____24371,id1))::uu____24373 ->
                       FStar_Pervasives_Native.Some id1
                   | uu____24376::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____24380 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____24380 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id1 ->
                     let uu____24386 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     [uu____24386]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____24407) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____24417,uu____24418,uu____24419,uu____24420,uu____24421)
                     ->
                     let uu____24430 =
                       let uu____24431 =
                         let uu____24432 =
                           let uu____24439 = mkclass lid  in
                           (meths, uu____24439)  in
                         FStar_Syntax_Syntax.Sig_splice uu____24432  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____24431;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = []
                       }  in
                     [uu____24430]
                 | uu____24442 -> []  in
               let extra =
                 if typeclass
                 then
                   let meths = FStar_List.concatMap get_meths ses  in
                   FStar_List.concatMap (splice_decl meths) ses
                 else []  in
               let env2 =
                 FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt env1
                   extra
                  in
               (env2, (FStar_List.append ses extra)))
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals  in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____24472;
                    FStar_Parser_AST.prange = uu____24473;_},uu____24474)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____24483;
                    FStar_Parser_AST.prange = uu____24484;_},uu____24485)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____24500;
                         FStar_Parser_AST.prange = uu____24501;_},uu____24502);
                    FStar_Parser_AST.prange = uu____24503;_},uu____24504)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____24525;
                         FStar_Parser_AST.prange = uu____24526;_},uu____24527);
                    FStar_Parser_AST.prange = uu____24528;_},uu____24529)::[]
                   -> false
               | (p,uu____24557)::[] ->
                   let uu____24566 = is_app_pattern p  in
                   Prims.op_Negation uu____24566
               | uu____24567 -> false)
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
            let uu____24640 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____24640 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____24652 =
                     let uu____24653 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____24653.FStar_Syntax_Syntax.n  in
                   match uu____24652 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____24663) ->
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
                         | uu____24696::uu____24697 ->
                             FStar_List.map
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____24700 ->
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.collect
                                  (fun uu___276_24715  ->
                                     match uu___276_24715 with
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inl uu____24718;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____24719;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____24720;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____24721;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____24722;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____24723;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____24724;_}
                                         -> []
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____24736;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____24737;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____24738;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____24739;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____24740;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____24741;_}
                                         ->
                                         FStar_Syntax_DsEnv.lookup_letbinding_quals
                                           env
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                          in
                       let quals2 =
                         let uu____24755 =
                           FStar_All.pipe_right lets1
                             (FStar_Util.for_some
                                (fun uu____24786  ->
                                   match uu____24786 with
                                   | (uu____24799,(uu____24800,t)) ->
                                       t.FStar_Parser_AST.level =
                                         FStar_Parser_AST.Formula))
                            in
                         if uu____24755
                         then FStar_Syntax_Syntax.Logic :: quals1
                         else quals1  in
                       let lbs1 =
                         let uu____24818 =
                           FStar_All.pipe_right quals2
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract)
                            in
                         if uu____24818
                         then
                           let uu____24821 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu___313_24835 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___314_24837 = fv  in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___314_24837.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___314_24837.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___313_24835.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___313_24835.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___313_24835.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___313_24835.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___313_24835.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___313_24835.FStar_Syntax_Syntax.lbpos)
                                     }))
                              in
                           ((FStar_Pervasives_Native.fst lbs), uu____24821)
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
                   | uu____24864 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____24870 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____24889 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____24870 with
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
                       let uu___315_24925 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___315_24925.FStar_Parser_AST.prange)
                       }
                   | uu____24932 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___316_24939 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___316_24939.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___316_24939.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___316_24939.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____24975 id1 =
                   match uu____24975 with
                   | (env1,ses) ->
                       let main =
                         let uu____24996 =
                           let uu____24997 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____24997  in
                         FStar_Parser_AST.mk_term uu____24996
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
                       let uu____25047 = desugar_decl env1 id_decl  in
                       (match uu____25047 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____25065 = gather_pattern_bound_vars true pat  in
                   FStar_All.pipe_right uu____25065 FStar_Util.set_elements
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
            let uu____25088 = close_fun env t  in
            desugar_term env uu____25088  in
          let quals1 =
            let uu____25092 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____25092
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let se =
            let uu____25098 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____25098;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in
          let env2 =
            FStar_Syntax_DsEnv.push_doc env1 lid d.FStar_Parser_AST.doc  in
          (env2, [se])
      | FStar_Parser_AST.Exception (id1,t_opt) ->
          let t =
            match t_opt with
            | FStar_Pervasives_Native.None  ->
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_lid env)
                  FStar_Parser_Const.exn_lid
            | FStar_Pervasives_Native.Some term ->
                let t = desugar_term env term  in
                let uu____25112 =
                  let uu____25121 = FStar_Syntax_Syntax.null_binder t  in
                  [uu____25121]  in
                let uu____25140 =
                  let uu____25143 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total
                    uu____25143
                   in
                FStar_Syntax_Util.arrow uu____25112 uu____25140
             in
          let l = FStar_Syntax_DsEnv.qualify env id1  in
          let qual = [FStar_Syntax_Syntax.ExceptionConstructor]  in
          let se =
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_datacon
                   (l, [], t, FStar_Parser_Const.exn_lid,
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
            let uu____25196 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____25196 with
            | FStar_Pervasives_Native.None  ->
                let uu____25199 =
                  let uu____25204 =
                    let uu____25205 =
                      let uu____25206 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.strcat uu____25206 " not found"  in
                    Prims.strcat "Effect name " uu____25205  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____25204)  in
                FStar_Errors.raise_error uu____25199
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____25210 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____25228 =
                  let uu____25231 =
                    let uu____25232 = desugar_term env t  in
                    ([], uu____25232)  in
                  FStar_Pervasives_Native.Some uu____25231  in
                (uu____25228, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____25245 =
                  let uu____25248 =
                    let uu____25249 = desugar_term env wp  in
                    ([], uu____25249)  in
                  FStar_Pervasives_Native.Some uu____25248  in
                let uu____25256 =
                  let uu____25259 =
                    let uu____25260 = desugar_term env t  in
                    ([], uu____25260)  in
                  FStar_Pervasives_Native.Some uu____25259  in
                (uu____25245, uu____25256)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____25272 =
                  let uu____25275 =
                    let uu____25276 = desugar_term env t  in
                    ([], uu____25276)  in
                  FStar_Pervasives_Native.Some uu____25275  in
                (FStar_Pervasives_Native.None, uu____25272)
             in
          (match uu____25210 with
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
      | FStar_Parser_AST.Splice (ids,t) ->
          let t1 = desugar_term env t  in
          let se =
            let uu____25310 =
              let uu____25311 =
                let uu____25318 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____25318, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____25311  in
            {
              FStar_Syntax_Syntax.sigel = uu____25310;
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = [];
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in (env1, [se])

let (desugar_decls :
  env_t ->
    FStar_Parser_AST.decl Prims.list ->
      (env_t,FStar_Syntax_Syntax.sigelt Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun decls  ->
      let uu____25344 =
        FStar_List.fold_left
          (fun uu____25364  ->
             fun d  ->
               match uu____25364 with
               | (env1,sigelts) ->
                   let uu____25384 = desugar_decl env1 d  in
                   (match uu____25384 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____25344 with
      | (env1,sigelts) ->
          let rec forward acc uu___278_25429 =
            match uu___278_25429 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____25443,FStar_Syntax_Syntax.Sig_let uu____25444) ->
                     let uu____25457 =
                       let uu____25460 =
                         let uu___317_25461 = se2  in
                         let uu____25462 =
                           let uu____25465 =
                             FStar_List.filter
                               (fun uu___277_25479  ->
                                  match uu___277_25479 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____25483;
                                           FStar_Syntax_Syntax.vars =
                                             uu____25484;_},uu____25485);
                                      FStar_Syntax_Syntax.pos = uu____25486;
                                      FStar_Syntax_Syntax.vars = uu____25487;_}
                                      when
                                      let uu____25514 =
                                        let uu____25515 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____25515
                                         in
                                      uu____25514 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____25516 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____25465
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___317_25461.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___317_25461.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___317_25461.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___317_25461.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____25462
                         }  in
                       uu____25460 :: se1 :: acc  in
                     forward uu____25457 sigelts1
                 | uu____25521 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____25529 = forward [] sigelts  in (env1, uu____25529)
  
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
          | (FStar_Pervasives_Native.None ,uu____25590) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____25594;
               FStar_Syntax_Syntax.exports = uu____25595;
               FStar_Syntax_Syntax.is_interface = uu____25596;_},FStar_Parser_AST.Module
             (current_lid,uu____25598)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____25606) ->
              let uu____25609 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____25609
           in
        let uu____25614 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____25650 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____25650, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____25667 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____25667, mname, decls, false)
           in
        match uu____25614 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____25697 = desugar_decls env2 decls  in
            (match uu____25697 with
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
          let uu____25759 =
            (FStar_Options.interactive ()) &&
              (let uu____25761 =
                 let uu____25762 =
                   let uu____25763 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____25763  in
                 FStar_Util.get_file_extension uu____25762  in
               FStar_List.mem uu____25761 ["fsti"; "fsi"])
             in
          if uu____25759 then as_interface m else m  in
        let uu____25767 = desugar_modul_common curmod env m1  in
        match uu____25767 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____25785 = FStar_Syntax_DsEnv.pop ()  in
              (uu____25785, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul ->
      (env_t,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun m  ->
      let uu____25805 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____25805 with
      | (env1,modul,pop_when_done) ->
          let uu____25819 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____25819 with
           | (env2,modul1) ->
               ((let uu____25831 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____25831
                 then
                   let uu____25832 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____25832
                 else ());
                (let uu____25834 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____25834, modul1))))
  
let with_options : 'a . (unit -> 'a) -> 'a =
  fun f  ->
    FStar_Options.push ();
    (let res = f ()  in
     let light = FStar_Options.ml_ish ()  in
     FStar_Options.pop ();
     if light then FStar_Options.set_ml_ish () else ();
     res)
  
let (ast_modul_to_modul :
  FStar_Parser_AST.modul ->
    FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun env  ->
      with_options
        (fun uu____25881  ->
           let uu____25882 = desugar_modul env modul  in
           match uu____25882 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____25923  ->
           let uu____25924 = desugar_decls env decls  in
           match uu____25924 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____25978  ->
             let uu____25979 = desugar_partial_modul modul env a_modul  in
             match uu____25979 with | (env1,modul1) -> (modul1, env1))
  
let (add_modul_to_env :
  FStar_Syntax_Syntax.modul ->
    FStar_Syntax_DsEnv.module_inclusion_info ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        unit FStar_Syntax_DsEnv.withenv)
  =
  fun m  ->
    fun mii  ->
      fun erase_univs  ->
        fun en  ->
          let erase_univs_ed ed =
            let erase_binders bs =
              match bs with
              | [] -> []
              | uu____26077 ->
                  let t =
                    let uu____26087 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____26087  in
                  let uu____26100 =
                    let uu____26101 = FStar_Syntax_Subst.compress t  in
                    uu____26101.FStar_Syntax_Syntax.n  in
                  (match uu____26100 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____26113,uu____26114)
                       -> bs1
                   | uu____26139 -> failwith "Impossible")
               in
            let uu____26148 =
              let uu____26155 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____26155
                FStar_Syntax_Syntax.t_unit
               in
            match uu____26148 with
            | (binders,uu____26157,binders_opening) ->
                let erase_term t =
                  let uu____26165 =
                    let uu____26166 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____26166  in
                  FStar_Syntax_Subst.close binders uu____26165  in
                let erase_tscheme uu____26184 =
                  match uu____26184 with
                  | (us,t) ->
                      let t1 =
                        let uu____26204 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____26204 t  in
                      let uu____26207 =
                        let uu____26208 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____26208  in
                      ([], uu____26207)
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
                    | uu____26231 ->
                        let bs =
                          let uu____26241 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____26241  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____26281 =
                          let uu____26282 =
                            let uu____26285 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____26285  in
                          uu____26282.FStar_Syntax_Syntax.n  in
                        (match uu____26281 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____26287,uu____26288) -> bs1
                         | uu____26313 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____26320 =
                      let uu____26321 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____26321  in
                    FStar_Syntax_Subst.close binders uu____26320  in
                  let uu___318_26322 = action  in
                  let uu____26323 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____26324 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___318_26322.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___318_26322.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____26323;
                    FStar_Syntax_Syntax.action_typ = uu____26324
                  }  in
                let uu___319_26325 = ed  in
                let uu____26326 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____26327 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____26328 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____26329 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____26330 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____26331 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____26332 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____26333 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____26334 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____26335 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____26336 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____26337 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____26338 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____26339 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____26340 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____26341 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___319_26325.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___319_26325.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____26326;
                  FStar_Syntax_Syntax.signature = uu____26327;
                  FStar_Syntax_Syntax.ret_wp = uu____26328;
                  FStar_Syntax_Syntax.bind_wp = uu____26329;
                  FStar_Syntax_Syntax.if_then_else = uu____26330;
                  FStar_Syntax_Syntax.ite_wp = uu____26331;
                  FStar_Syntax_Syntax.stronger = uu____26332;
                  FStar_Syntax_Syntax.close_wp = uu____26333;
                  FStar_Syntax_Syntax.assert_p = uu____26334;
                  FStar_Syntax_Syntax.assume_p = uu____26335;
                  FStar_Syntax_Syntax.null_wp = uu____26336;
                  FStar_Syntax_Syntax.trivial = uu____26337;
                  FStar_Syntax_Syntax.repr = uu____26338;
                  FStar_Syntax_Syntax.return_repr = uu____26339;
                  FStar_Syntax_Syntax.bind_repr = uu____26340;
                  FStar_Syntax_Syntax.actions = uu____26341;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___319_26325.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___320_26357 = se  in
                  let uu____26358 =
                    let uu____26359 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____26359  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____26358;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___320_26357.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___320_26357.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___320_26357.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___320_26357.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___321_26363 = se  in
                  let uu____26364 =
                    let uu____26365 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____26365
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____26364;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___321_26363.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___321_26363.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___321_26363.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___321_26363.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____26367 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____26368 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____26368 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____26380 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____26380
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____26382 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____26382)
  