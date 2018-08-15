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
      fun uu___236_237  ->
        match uu___236_237 with
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
  fun uu___237_246  ->
    match uu___237_246 with
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
  fun uu___238_260  ->
    match uu___238_260 with
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
            let uu____508 =
              compile_op_lid arity op.FStar_Ident.idText
                op.FStar_Ident.idRange
               in
            FStar_Syntax_DsEnv.try_lookup_lid env uu____508  in
          match uu____501 with
          | FStar_Pervasives_Native.Some t ->
              FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst t)
          | uu____520 -> fallback ()
  
let (sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list)
  =
  fun ftv  ->
    let uu____538 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv
       in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____538
  
let rec (free_type_vars_b :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Syntax_DsEnv.env,FStar_Ident.ident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____585 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____589 = FStar_Syntax_DsEnv.push_bv env x  in
          (match uu____589 with | (env1,uu____601) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____604,term) ->
          let uu____606 = free_type_vars env term  in (env, uu____606)
      | FStar_Parser_AST.TAnnotated (id1,uu____612) ->
          let uu____613 = FStar_Syntax_DsEnv.push_bv env id1  in
          (match uu____613 with | (env1,uu____625) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____629 = free_type_vars env t  in (env, uu____629)

and (free_type_vars :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun t  ->
      let uu____636 =
        let uu____637 = unparen t  in uu____637.FStar_Parser_AST.tm  in
      match uu____636 with
      | FStar_Parser_AST.Labeled uu____640 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____650 = FStar_Syntax_DsEnv.try_lookup_id env a  in
          (match uu____650 with
           | FStar_Pervasives_Native.None  -> [a]
           | uu____663 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____670 -> []
      | FStar_Parser_AST.Uvar uu____671 -> []
      | FStar_Parser_AST.Var uu____672 -> []
      | FStar_Parser_AST.Projector uu____673 -> []
      | FStar_Parser_AST.Discrim uu____678 -> []
      | FStar_Parser_AST.Name uu____679 -> []
      | FStar_Parser_AST.Requires (t1,uu____681) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____687) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____692,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None  -> []
             | FStar_Pervasives_Native.Some t2 -> [t2])
             in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____710,ts) ->
          FStar_List.collect
            (fun uu____731  ->
               match uu____731 with | (t1,uu____739) -> free_type_vars env t1)
            ts
      | FStar_Parser_AST.Op (uu____740,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____748) ->
          let uu____749 = free_type_vars env t1  in
          let uu____752 = free_type_vars env t2  in
          FStar_List.append uu____749 uu____752
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____757 = free_type_vars_b env b  in
          (match uu____757 with
           | (env1,f) ->
               let uu____772 = free_type_vars env1 t1  in
               FStar_List.append f uu____772)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____781 =
            FStar_List.fold_left
              (fun uu____801  ->
                 fun binder  ->
                   match uu____801 with
                   | (env1,free) ->
                       let uu____821 = free_type_vars_b env1 binder  in
                       (match uu____821 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____781 with
           | (env1,free) ->
               let uu____852 = free_type_vars env1 body  in
               FStar_List.append free uu____852)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____861 =
            FStar_List.fold_left
              (fun uu____881  ->
                 fun binder  ->
                   match uu____881 with
                   | (env1,free) ->
                       let uu____901 = free_type_vars_b env1 binder  in
                       (match uu____901 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____861 with
           | (env1,free) ->
               let uu____932 = free_type_vars env1 body  in
               FStar_List.append free uu____932)
      | FStar_Parser_AST.Project (t1,uu____936) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.Abs uu____940 -> []
      | FStar_Parser_AST.Let uu____947 -> []
      | FStar_Parser_AST.LetOpen uu____968 -> []
      | FStar_Parser_AST.If uu____973 -> []
      | FStar_Parser_AST.QForall uu____980 -> []
      | FStar_Parser_AST.QExists uu____993 -> []
      | FStar_Parser_AST.Record uu____1006 -> []
      | FStar_Parser_AST.Match uu____1019 -> []
      | FStar_Parser_AST.TryWith uu____1034 -> []
      | FStar_Parser_AST.Bind uu____1049 -> []
      | FStar_Parser_AST.Quote uu____1056 -> []
      | FStar_Parser_AST.VQuote uu____1061 -> []
      | FStar_Parser_AST.Antiquote uu____1062 -> []
      | FStar_Parser_AST.Seq uu____1063 -> []

let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term,(FStar_Parser_AST.term,FStar_Parser_AST.imp)
                             FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let rec aux args t1 =
      let uu____1116 =
        let uu____1117 = unparen t1  in uu____1117.FStar_Parser_AST.tm  in
      match uu____1116 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____1159 -> (t1, args)  in
    aux [] t
  
let (close :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____1183 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1183  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1201 =
                     let uu____1202 =
                       let uu____1207 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____1207)  in
                     FStar_Parser_AST.TAnnotated uu____1202  in
                   FStar_Parser_AST.mk_binder uu____1201
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
        let uu____1224 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1224  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1242 =
                     let uu____1243 =
                       let uu____1248 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____1248)  in
                     FStar_Parser_AST.TAnnotated uu____1243  in
                   FStar_Parser_AST.mk_binder uu____1242
                     x.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____1250 =
             let uu____1251 = unparen t  in uu____1251.FStar_Parser_AST.tm
              in
           match uu____1250 with
           | FStar_Parser_AST.Product uu____1252 -> t
           | uu____1259 ->
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
      | uu____1295 -> (bs, t)
  
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild uu____1303 -> true
    | FStar_Parser_AST.PatTvar (uu____1306,uu____1307) -> true
    | FStar_Parser_AST.PatVar (uu____1312,uu____1313) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____1319) -> is_var_pattern p1
    | uu____1332 -> false
  
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____1339) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____1352;
           FStar_Parser_AST.prange = uu____1353;_},uu____1354)
        -> true
    | uu____1365 -> false
  
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
    | uu____1379 -> p
  
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
            let uu____1449 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____1449 with
             | (name,args,uu____1492) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1542);
               FStar_Parser_AST.prange = uu____1543;_},args)
            when is_top_level1 ->
            let uu____1553 =
              let uu____1558 = FStar_Syntax_DsEnv.qualify env id1  in
              FStar_Util.Inr uu____1558  in
            (uu____1553, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1580);
               FStar_Parser_AST.prange = uu____1581;_},args)
            -> ((FStar_Util.Inl id1), args, FStar_Pervasives_Native.None)
        | uu____1611 -> failwith "Not an app pattern"
  
let rec (gather_pattern_bound_vars_maybe_top :
  FStar_Ident.ident FStar_Util.set ->
    FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set)
  =
  fun acc  ->
    fun p  ->
      let gather_pattern_bound_vars_from_list =
        FStar_List.fold_left gather_pattern_bound_vars_maybe_top acc  in
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatWild uu____1661 -> acc
      | FStar_Parser_AST.PatConst uu____1664 -> acc
      | FStar_Parser_AST.PatVar
          (uu____1665,FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit
           ))
          -> acc
      | FStar_Parser_AST.PatName uu____1668 -> acc
      | FStar_Parser_AST.PatTvar uu____1669 -> acc
      | FStar_Parser_AST.PatOp uu____1676 -> acc
      | FStar_Parser_AST.PatApp (phead,pats) ->
          gather_pattern_bound_vars_from_list (phead :: pats)
      | FStar_Parser_AST.PatVar (x,uu____1684) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatTuple (pats,uu____1693) ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu____1708 =
            FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
          gather_pattern_bound_vars_from_list uu____1708
      | FStar_Parser_AST.PatAscribed (pat,uu____1716) ->
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
  FStar_Pervasives_Native.tuple2 
let (uu___is_LocalBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LocalBinder _0 -> true | uu____1778 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____1814 -> false
  
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
  fun uu___239_1860  ->
    match uu___239_1860 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____1867 -> failwith "Impossible"
  
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
  fun uu____1900  ->
    match uu____1900 with
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
      let uu____1980 =
        let uu____1997 =
          let uu____2000 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____2000  in
        let uu____2001 =
          let uu____2012 =
            let uu____2021 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2021)  in
          [uu____2012]  in
        (uu____1997, uu____2001)  in
      FStar_Syntax_Syntax.Tm_app uu____1980  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____2068 =
        let uu____2085 =
          let uu____2088 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____2088  in
        let uu____2089 =
          let uu____2100 =
            let uu____2109 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2109)  in
          [uu____2100]  in
        (uu____2085, uu____2089)  in
      FStar_Syntax_Syntax.Tm_app uu____2068  in
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
          let uu____2170 =
            let uu____2187 =
              let uu____2190 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____2190  in
            let uu____2191 =
              let uu____2202 =
                let uu____2211 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____2211)  in
              let uu____2218 =
                let uu____2229 =
                  let uu____2238 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____2238)  in
                [uu____2229]  in
              uu____2202 :: uu____2218  in
            (uu____2187, uu____2191)  in
          FStar_Syntax_Syntax.Tm_app uu____2170  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let (generalize_annotated_univs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun s  ->
    let bs_univnames bs =
      let uu____2296 =
        let uu____2311 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____2330  ->
               match uu____2330 with
               | ({ FStar_Syntax_Syntax.ppname = uu____2341;
                    FStar_Syntax_Syntax.index = uu____2342;
                    FStar_Syntax_Syntax.sort = t;_},uu____2344)
                   ->
                   let uu____2351 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____2351) uu____2311
         in
      FStar_All.pipe_right bs uu____2296  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____2367 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____2384 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____2410 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____2431,uu____2432,bs,t,uu____2435,uu____2436)
                            ->
                            let uu____2445 = bs_univnames bs  in
                            let uu____2448 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____2445 uu____2448
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____2451,uu____2452,t,uu____2454,uu____2455,uu____2456)
                            -> FStar_Syntax_Free.univnames t
                        | uu____2461 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____2410 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___265_2469 = s  in
        let uu____2470 =
          let uu____2471 =
            let uu____2480 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____2498,bs,t,lids1,lids2) ->
                          let uu___266_2511 = se  in
                          let uu____2512 =
                            let uu____2513 =
                              let uu____2530 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____2531 =
                                let uu____2532 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____2532 t  in
                              (lid, uvs, uu____2530, uu____2531, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____2513
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____2512;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___266_2511.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___266_2511.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___266_2511.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___266_2511.FStar_Syntax_Syntax.sigattrs)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____2546,t,tlid,n1,lids1) ->
                          let uu___267_2555 = se  in
                          let uu____2556 =
                            let uu____2557 =
                              let uu____2572 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____2572, tlid, n1, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____2557  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____2556;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___267_2555.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___267_2555.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___267_2555.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___267_2555.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____2575 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____2480, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____2471  in
        {
          FStar_Syntax_Syntax.sigel = uu____2470;
          FStar_Syntax_Syntax.sigrng =
            (uu___265_2469.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___265_2469.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___265_2469.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___265_2469.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2581,t) ->
        let uvs =
          let uu____2584 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____2584 FStar_Util.set_elements  in
        let uu___268_2589 = s  in
        let uu____2590 =
          let uu____2591 =
            let uu____2598 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____2598)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____2591  in
        {
          FStar_Syntax_Syntax.sigel = uu____2590;
          FStar_Syntax_Syntax.sigrng =
            (uu___268_2589.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___268_2589.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___268_2589.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___268_2589.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____2620 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____2623 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____2630) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____2663,(FStar_Util.Inl t,uu____2665),uu____2666)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____2713,(FStar_Util.Inr c,uu____2715),uu____2716)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____2763 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____2764,(FStar_Util.Inl t,uu____2766),uu____2767) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____2814,(FStar_Util.Inr c,uu____2816),uu____2817) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____2864 -> empty_set  in
          FStar_Util.set_union uu____2620 uu____2623  in
        let all_lb_univs =
          let uu____2868 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____2884 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____2884) empty_set)
             in
          FStar_All.pipe_right uu____2868 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___269_2894 = s  in
        let uu____2895 =
          let uu____2896 =
            let uu____2903 =
              let uu____2904 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___270_2916 = lb  in
                        let uu____2917 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____2920 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___270_2916.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____2917;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___270_2916.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____2920;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___270_2916.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___270_2916.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____2904)  in
            (uu____2903, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____2896  in
        {
          FStar_Syntax_Syntax.sigel = uu____2895;
          FStar_Syntax_Syntax.sigrng =
            (uu___269_2894.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___269_2894.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___269_2894.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___269_2894.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____2928,fml) ->
        let uvs =
          let uu____2931 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____2931 FStar_Util.set_elements  in
        let uu___271_2936 = s  in
        let uu____2937 =
          let uu____2938 =
            let uu____2945 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____2945)  in
          FStar_Syntax_Syntax.Sig_assume uu____2938  in
        {
          FStar_Syntax_Syntax.sigel = uu____2937;
          FStar_Syntax_Syntax.sigrng =
            (uu___271_2936.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___271_2936.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___271_2936.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___271_2936.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____2947,bs,c,flags1) ->
        let uvs =
          let uu____2956 =
            let uu____2959 = bs_univnames bs  in
            let uu____2962 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____2959 uu____2962  in
          FStar_All.pipe_right uu____2956 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___272_2970 = s  in
        let uu____2971 =
          let uu____2972 =
            let uu____2985 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____2986 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____2985, uu____2986, flags1)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____2972  in
        {
          FStar_Syntax_Syntax.sigel = uu____2971;
          FStar_Syntax_Syntax.sigrng =
            (uu___272_2970.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___272_2970.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___272_2970.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___272_2970.FStar_Syntax_Syntax.sigattrs)
        }
    | uu____2989 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___240_2994  ->
    match uu___240_2994 with
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
    | uu____2995 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____3007 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____3007)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____3026 =
      let uu____3027 = unparen t  in uu____3027.FStar_Parser_AST.tm  in
    match uu____3026 with
    | FStar_Parser_AST.Wild  ->
        let uu____3032 =
          let uu____3033 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____3033  in
        FStar_Util.Inr uu____3032
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____3044)) ->
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
             let uu____3109 = sum_to_universe u n1  in
             FStar_Util.Inr uu____3109
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____3120 = sum_to_universe u n1  in
             FStar_Util.Inr uu____3120
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____3131 =
               let uu____3136 =
                 let uu____3137 = FStar_Parser_AST.term_to_string t  in
                 Prims.strcat
                   "This universe might contain a sum of two universe variables "
                   uu____3137
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____3136)
                in
             FStar_Errors.raise_error uu____3131 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____3142 ->
        let rec aux t1 univargs =
          let uu____3176 =
            let uu____3177 = unparen t1  in uu____3177.FStar_Parser_AST.tm
             in
          match uu____3176 with
          | FStar_Parser_AST.App (t2,targ,uu____3184) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___241_3207  ->
                     match uu___241_3207 with
                     | FStar_Util.Inr uu____3212 -> true
                     | uu____3213 -> false) univargs
              then
                let uu____3218 =
                  let uu____3219 =
                    FStar_List.map
                      (fun uu___242_3228  ->
                         match uu___242_3228 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____3219  in
                FStar_Util.Inr uu____3218
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___243_3245  ->
                        match uu___243_3245 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____3251 -> failwith "impossible")
                     univargs
                    in
                 let uu____3252 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____3252)
          | uu____3258 ->
              let uu____3259 =
                let uu____3264 =
                  let uu____3265 =
                    let uu____3266 = FStar_Parser_AST.term_to_string t1  in
                    Prims.strcat uu____3266 " in universe context"  in
                  Prims.strcat "Unexpected term " uu____3265  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3264)  in
              FStar_Errors.raise_error uu____3259 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____3275 ->
        let uu____3276 =
          let uu____3281 =
            let uu____3282 =
              let uu____3283 = FStar_Parser_AST.term_to_string t  in
              Prims.strcat uu____3283 " in universe context"  in
            Prims.strcat "Unexpected term " uu____3282  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3281)  in
        FStar_Errors.raise_error uu____3276 t.FStar_Parser_AST.range
  
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
                   FStar_Syntax_Syntax.antiquotes = uu____3313;_});
            FStar_Syntax_Syntax.pos = uu____3314;
            FStar_Syntax_Syntax.vars = uu____3315;_})::uu____3316
        ->
        let uu____3347 =
          let uu____3352 =
            let uu____3353 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____3353
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____3352)  in
        FStar_Errors.raise_error uu____3347 e.FStar_Syntax_Syntax.pos
    | (bv,e)::uu____3356 ->
        let uu____3375 =
          let uu____3380 =
            let uu____3381 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____3381
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____3380)  in
        FStar_Errors.raise_error uu____3375 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'Auu____3390 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident,'Auu____3390) FStar_Pervasives_Native.tuple2
        Prims.list -> FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____3418 = FStar_List.hd fields  in
        match uu____3418 with
        | (f,uu____3428) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____3440 =
                match uu____3440 with
                | (f',uu____3446) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____3448 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____3448
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
              (let uu____3452 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____3452);
              (match () with | () -> record)))
  
let rec (desugar_data_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern ->
      Prims.bool ->
        (env_t,bnd,annotated_pat Prims.list) FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun p  ->
      fun is_mut  ->
        let check_linear_pattern_variables pats r =
          let rec pat_vars p1 =
            match p1.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_dot_term uu____3841 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_wild uu____3848 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_constant uu____3849 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_var x ->
                FStar_Util.set_add x FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_cons (uu____3851,pats1) ->
                let aux out uu____3889 =
                  match uu____3889 with
                  | (p2,uu____3901) ->
                      let intersection =
                        let uu____3909 = pat_vars p2  in
                        FStar_Util.set_intersect uu____3909 out  in
                      let uu____3912 = FStar_Util.set_is_empty intersection
                         in
                      if uu____3912
                      then
                        let uu____3915 = pat_vars p2  in
                        FStar_Util.set_union out uu____3915
                      else
                        (let duplicate_bv =
                           let uu____3920 =
                             FStar_Util.set_elements intersection  in
                           FStar_List.hd uu____3920  in
                         let uu____3923 =
                           let uu____3928 =
                             FStar_Util.format1
                               "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                               (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                              in
                           (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                             uu____3928)
                            in
                         FStar_Errors.raise_error uu____3923 r)
                   in
                FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
             in
          match pats with
          | [] -> ()
          | p1::[] ->
              let uu____3948 = pat_vars p1  in
              FStar_All.pipe_right uu____3948 (fun a236  -> ())
          | p1::ps ->
              let pvars = pat_vars p1  in
              let aux p2 =
                let uu____3976 =
                  let uu____3977 = pat_vars p2  in
                  FStar_Util.set_eq pvars uu____3977  in
                if uu____3976
                then ()
                else
                  (let nonlinear_vars =
                     let uu____3984 = pat_vars p2  in
                     FStar_Util.set_symmetric_difference pvars uu____3984  in
                   let first_nonlinear_var =
                     let uu____3988 = FStar_Util.set_elements nonlinear_vars
                        in
                     FStar_List.hd uu____3988  in
                   let uu____3991 =
                     let uu____3996 =
                       FStar_Util.format1
                         "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                         (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                        in
                     (FStar_Errors.Fatal_IncoherentPatterns, uu____3996)  in
                   FStar_Errors.raise_error uu____3991 r)
                 in
              FStar_List.iter aux ps
           in
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false ,uu____4000) -> ()
         | (true ,FStar_Parser_AST.PatVar uu____4001) -> ()
         | (true ,uu____4008) ->
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_LetMutableForVariablesOnly,
                 "let-mutable is for variables only")
               p.FStar_Parser_AST.prange);
        (let resolvex l e x =
           let uu____4031 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText))
              in
           match uu____4031 with
           | FStar_Pervasives_Native.Some y -> (l, e, y)
           | uu____4047 ->
               let uu____4050 =
                 if is_mut
                 then FStar_Syntax_DsEnv.push_bv_mutable e x
                 else FStar_Syntax_DsEnv.push_bv e x  in
               (match uu____4050 with | (e1,x1) -> ((x1 :: l), e1, x1))
            in
         let rec aux' top loc env1 p1 =
           let pos q =
             FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange  in
           let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
           let orig = p1  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr uu____4200 -> failwith "impossible"
           | FStar_Parser_AST.PatOp op ->
               let uu____4222 =
                 let uu____4223 =
                   let uu____4224 =
                     let uu____4231 =
                       let uu____4232 =
                         let uu____4237 =
                           FStar_Parser_AST.compile_op (Prims.parse_int "0")
                             op.FStar_Ident.idText op.FStar_Ident.idRange
                            in
                         (uu____4237, (op.FStar_Ident.idRange))  in
                       FStar_Ident.mk_ident uu____4232  in
                     (uu____4231, FStar_Pervasives_Native.None)  in
                   FStar_Parser_AST.PatVar uu____4224  in
                 {
                   FStar_Parser_AST.pat = uu____4223;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 }  in
               aux loc env1 uu____4222
           | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
               ((match tacopt with
                 | FStar_Pervasives_Native.None  -> ()
                 | FStar_Pervasives_Native.Some uu____4254 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                         "Type ascriptions within patterns cannot be associated with a tactic")
                       orig.FStar_Parser_AST.prange);
                (let uu____4255 = aux loc env1 p2  in
                 match uu____4255 with
                 | (loc1,env',binder,p3,annots,imp) ->
                     let annot_pat_var p4 t1 =
                       match p4.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let uu___273_4340 = p4  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var
                                  (let uu___274_4345 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___274_4345.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___274_4345.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }));
                             FStar_Syntax_Syntax.p =
                               (uu___273_4340.FStar_Syntax_Syntax.p)
                           }
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let uu___275_4347 = p4  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild
                                  (let uu___276_4352 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___276_4352.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___276_4352.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }));
                             FStar_Syntax_Syntax.p =
                               (uu___275_4347.FStar_Syntax_Syntax.p)
                           }
                       | uu____4353 when top -> p4
                       | uu____4354 ->
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                               "Type ascriptions within patterns are only allowed on variables")
                             orig.FStar_Parser_AST.prange
                        in
                     let uu____4357 =
                       match binder with
                       | LetBinder uu____4378 -> failwith "impossible"
                       | LocalBinder (x,aq) ->
                           let t1 =
                             let uu____4402 = close_fun env1 t  in
                             desugar_term env1 uu____4402  in
                           let x1 =
                             let uu___277_4404 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___277_4404.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___277_4404.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }  in
                           ([(x1, t1)], (LocalBinder (x1, aq)))
                        in
                     (match uu____4357 with
                      | (annots',binder1) ->
                          (loc1, env', binder1, p3,
                            (FStar_List.append annots' annots), imp))))
           | FStar_Parser_AST.PatWild aq ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual env1 aq  in
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____4469 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
               (loc, env1, (LocalBinder (x, aq1)), uu____4469, [], imp)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____4482 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____4482, [], false)
           | FStar_Parser_AST.PatTvar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual env1 aq  in
               let uu____4503 = resolvex loc env1 x  in
               (match uu____4503 with
                | (loc1,env2,xbv) ->
                    let uu____4531 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____4531, [],
                      imp))
           | FStar_Parser_AST.PatVar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual env1 aq  in
               let uu____4552 = resolvex loc env1 x  in
               (match uu____4552 with
                | (loc1,env2,xbv) ->
                    let uu____4580 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____4580, [],
                      imp))
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
               let uu____4594 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, []))
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____4594, [], false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____4620;_},args)
               ->
               let uu____4626 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____4685  ->
                        match uu____4685 with
                        | (loc1,env2,annots,args1) ->
                            let uu____4762 = aux loc1 env2 arg  in
                            (match uu____4762 with
                             | (loc2,env3,uu____4807,arg1,ans,imp) ->
                                 (loc2, env3, (FStar_List.append ans annots),
                                   ((arg1, imp) :: args1)))) args
                   (loc, env1, [], [])
                  in
               (match uu____4626 with
                | (loc1,env2,annots,args1) ->
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
                    let uu____4929 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                       in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)),
                      uu____4929, annots, false))
           | FStar_Parser_AST.PatApp uu____4944 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                 p1.FStar_Parser_AST.prange
           | FStar_Parser_AST.PatList pats ->
               let uu____4972 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____5023  ->
                        match uu____5023 with
                        | (loc1,env2,annots,pats1) ->
                            let uu____5084 = aux loc1 env2 pat  in
                            (match uu____5084 with
                             | (loc2,env3,uu____5125,pat1,ans,uu____5128) ->
                                 (loc2, env3, (FStar_List.append ans annots),
                                   (pat1 :: pats1)))) pats
                   (loc, env1, [], [])
                  in
               (match uu____4972 with
                | (loc1,env2,annots,pats1) ->
                    let pat =
                      let uu____5222 =
                        let uu____5225 =
                          let uu____5232 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange
                             in
                          pos_r uu____5232  in
                        let uu____5233 =
                          let uu____5234 =
                            let uu____5247 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Parser_Const.nil_lid
                                FStar_Syntax_Syntax.delta_constant
                                (FStar_Pervasives_Native.Some
                                   FStar_Syntax_Syntax.Data_ctor)
                               in
                            (uu____5247, [])  in
                          FStar_Syntax_Syntax.Pat_cons uu____5234  in
                        FStar_All.pipe_left uu____5225 uu____5233  in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p
                                in
                             let uu____5279 =
                               let uu____5280 =
                                 let uu____5293 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.cons_lid
                                     FStar_Syntax_Syntax.delta_constant
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Data_ctor)
                                    in
                                 (uu____5293, [(hd1, false); (tl1, false)])
                                  in
                               FStar_Syntax_Syntax.Pat_cons uu____5280  in
                             FStar_All.pipe_left (pos_r r) uu____5279) pats1
                        uu____5222
                       in
                    let x =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           (p1.FStar_Parser_AST.prange))
                        FStar_Syntax_Syntax.tun
                       in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)), pat,
                      annots, false))
           | FStar_Parser_AST.PatTuple (args,dep1) ->
               let uu____5339 =
                 FStar_List.fold_left
                   (fun uu____5397  ->
                      fun p2  ->
                        match uu____5397 with
                        | (loc1,env2,annots,pats) ->
                            let uu____5475 = aux loc1 env2 p2  in
                            (match uu____5475 with
                             | (loc2,env3,uu____5520,pat,ans,uu____5523) ->
                                 (loc2, env3, (FStar_List.append ans annots),
                                   ((pat, false) :: pats))))
                   (loc, env1, [], []) args
                  in
               (match uu____5339 with
                | (loc1,env2,annots,args1) ->
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
                    let uu____5669 =
                      FStar_Syntax_DsEnv.fail_or env2
                        (FStar_Syntax_DsEnv.try_lookup_lid env2) l
                       in
                    (match uu____5669 with
                     | (constr,uu____5697) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____5700 -> failwith "impossible"  in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (FStar_Pervasives_Native.Some
                                (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun
                            in
                         let uu____5702 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                            in
                         (loc1, env2,
                           (LocalBinder (x, FStar_Pervasives_Native.None)),
                           uu____5702, annots, false)))
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
                      (fun uu____5777  ->
                         match uu____5777 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2)))
                  in
               let args =
                 FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                   (FStar_List.map
                      (fun uu____5807  ->
                         match uu____5807 with
                         | (f,uu____5813) ->
                             let uu____5814 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____5840  ->
                                       match uu____5840 with
                                       | (g,uu____5846) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText))
                                in
                             (match uu____5814 with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Parser_AST.mk_pattern
                                    (FStar_Parser_AST.PatWild
                                       FStar_Pervasives_Native.None)
                                    p1.FStar_Parser_AST.prange
                              | FStar_Pervasives_Native.Some (uu____5851,p2)
                                  -> p2)))
                  in
               let app =
                 let uu____5858 =
                   let uu____5859 =
                     let uu____5866 =
                       let uu____5867 =
                         let uu____5868 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                                [record.FStar_Syntax_DsEnv.constrname])
                            in
                         FStar_Parser_AST.PatName uu____5868  in
                       FStar_Parser_AST.mk_pattern uu____5867
                         p1.FStar_Parser_AST.prange
                        in
                     (uu____5866, args)  in
                   FStar_Parser_AST.PatApp uu____5859  in
                 FStar_Parser_AST.mk_pattern uu____5858
                   p1.FStar_Parser_AST.prange
                  in
               let uu____5871 = aux loc env1 app  in
               (match uu____5871 with
                | (env2,e,b,p2,annots,uu____5915) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____5951 =
                            let uu____5952 =
                              let uu____5965 =
                                let uu___278_5966 = fv  in
                                let uu____5967 =
                                  let uu____5970 =
                                    let uu____5971 =
                                      let uu____5978 =
                                        FStar_All.pipe_right
                                          record.FStar_Syntax_DsEnv.fields
                                          (FStar_List.map
                                             FStar_Pervasives_Native.fst)
                                         in
                                      ((record.FStar_Syntax_DsEnv.typename),
                                        uu____5978)
                                       in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____5971
                                     in
                                  FStar_Pervasives_Native.Some uu____5970  in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___278_5966.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___278_5966.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____5967
                                }  in
                              (uu____5965, args1)  in
                            FStar_Syntax_Syntax.Pat_cons uu____5952  in
                          FStar_All.pipe_left pos uu____5951
                      | uu____6003 -> p2  in
                    (env2, e, b, p3, annots, false))
         
         and aux loc env1 p1 = aux' false loc env1 p1
          in
         let aux_maybe_or env1 p1 =
           let loc = []  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____6085 = aux' true loc env1 p2  in
               (match uu____6085 with
                | (loc1,env2,var,p3,ans,uu____6127) ->
                    let uu____6140 =
                      FStar_List.fold_left
                        (fun uu____6189  ->
                           fun p4  ->
                             match uu____6189 with
                             | (loc2,env3,ps1) ->
                                 let uu____6254 = aux' true loc2 env3 p4  in
                                 (match uu____6254 with
                                  | (loc3,env4,uu____6293,p5,ans1,uu____6296)
                                      -> (loc3, env4, ((p5, ans1) :: ps1))))
                        (loc1, env2, []) ps
                       in
                    (match uu____6140 with
                     | (loc2,env3,ps1) ->
                         let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                         (env3, var, pats)))
           | uu____6455 ->
               let uu____6456 = aux' true loc env1 p1  in
               (match uu____6456 with
                | (loc1,env2,vars,pat,ans,b) -> (env2, vars, [(pat, ans)]))
            in
         let uu____6549 = aux_maybe_or env p  in
         match uu____6549 with
         | (env1,b,pats) ->
             ((let uu____6604 =
                 FStar_List.map FStar_Pervasives_Native.fst pats  in
               check_linear_pattern_variables uu____6604
                 p.FStar_Parser_AST.prange);
              (env1, b, pats)))

and (desugar_binding_pat_maybe_top :
  Prims.bool ->
    FStar_Syntax_DsEnv.env ->
      FStar_Parser_AST.pattern ->
        Prims.bool ->
          (env_t,bnd,annotated_pat Prims.list) FStar_Pervasives_Native.tuple3)
  =
  fun top  ->
    fun env  ->
      fun p  ->
        fun is_mut  ->
          let mklet x =
            let uu____6655 =
              let uu____6656 =
                let uu____6667 = FStar_Syntax_DsEnv.qualify env x  in
                (uu____6667,
                  (FStar_Syntax_Syntax.tun, FStar_Pervasives_Native.None))
                 in
              LetBinder uu____6656  in
            (env, uu____6655, [])  in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____6695 =
                  let uu____6696 =
                    let uu____6701 =
                      FStar_Parser_AST.compile_op (Prims.parse_int "0")
                        x.FStar_Ident.idText x.FStar_Ident.idRange
                       in
                    (uu____6701, (x.FStar_Ident.idRange))  in
                  FStar_Ident.mk_ident uu____6696  in
                mklet uu____6695
            | FStar_Parser_AST.PatVar (x,uu____6703) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____6709);
                   FStar_Parser_AST.prange = uu____6710;_},(t,tacopt))
                ->
                let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)
                   in
                let uu____6730 =
                  let uu____6731 =
                    let uu____6742 = FStar_Syntax_DsEnv.qualify env x  in
                    let uu____6743 =
                      let uu____6750 = desugar_term env t  in
                      (uu____6750, tacopt1)  in
                    (uu____6742, uu____6743)  in
                  LetBinder uu____6731  in
                (env, uu____6730, [])
            | uu____6761 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_UnexpectedPattern,
                    "Unexpected pattern at the top-level")
                  p.FStar_Parser_AST.prange
          else
            (let uu____6771 = desugar_data_pat env p is_mut  in
             match uu____6771 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1 with
                   | ({
                        FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                          uu____6800;
                        FStar_Syntax_Syntax.p = uu____6801;_},uu____6802)::[]
                       -> []
                   | ({
                        FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                          uu____6815;
                        FStar_Syntax_Syntax.p = uu____6816;_},uu____6817)::[]
                       -> []
                   | uu____6830 -> p1  in
                 (env1, binder, p2))

and (desugar_binding_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern ->
      (env_t,bnd,annotated_pat Prims.list) FStar_Pervasives_Native.tuple3)
  = fun env  -> fun p  -> desugar_binding_pat_maybe_top false env p false

and (desugar_match_pat_maybe_top :
  Prims.bool ->
    FStar_Syntax_DsEnv.env ->
      FStar_Parser_AST.pattern ->
        (env_t,annotated_pat Prims.list) FStar_Pervasives_Native.tuple2)
  =
  fun uu____6837  ->
    fun env  ->
      fun pat  ->
        let uu____6840 = desugar_data_pat env pat false  in
        match uu____6840 with | (env1,uu____6856,pat1) -> (env1, pat1)

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
      let uu____6875 = desugar_term_aq env e  in
      match uu____6875 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____6892 = desugar_typ_aq env e  in
      match uu____6892 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness,FStar_Const.width)
        FStar_Pervasives_Native.tuple2 ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____6902  ->
        fun range  ->
          match uu____6902 with
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
              ((let uu____6912 =
                  let uu____6913 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____6913  in
                if uu____6912
                then
                  let uu____6914 =
                    let uu____6919 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____6919)  in
                  FStar_Errors.log_issue range uu____6914
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
                  let uu____6924 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____6924 range  in
                let lid1 =
                  let uu____6928 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____6928 with
                  | FStar_Pervasives_Native.Some (intro_term,uu____6938) ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____6947 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____6947 range  in
                           let private_fv =
                             let uu____6949 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____6949 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___279_6950 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___279_6950.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___279_6950.FStar_Syntax_Syntax.vars)
                           }
                       | uu____6951 ->
                           failwith
                             (Prims.strcat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____6958 =
                        let uu____6963 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____6963)
                         in
                      FStar_Errors.raise_error uu____6958 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____6979 =
                  let uu____6986 =
                    let uu____6987 =
                      let uu____7004 =
                        let uu____7015 =
                          let uu____7024 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____7024)  in
                        [uu____7015]  in
                      (lid1, uu____7004)  in
                    FStar_Syntax_Syntax.Tm_app uu____6987  in
                  FStar_Syntax_Syntax.mk uu____6986  in
                uu____6979 FStar_Pervasives_Native.None range))

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
            let uu____7073 =
              let uu____7082 =
                (if resolve
                 then FStar_Syntax_DsEnv.try_lookup_lid_with_attributes
                 else
                   FStar_Syntax_DsEnv.try_lookup_lid_with_attributes_no_resolve)
                  env
                 in
              FStar_Syntax_DsEnv.fail_or env uu____7082 l  in
            match uu____7073 with
            | (tm,mut,attrs) ->
                let warn_if_deprecated attrs1 =
                  FStar_List.iter
                    (fun a  ->
                       match a.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_app
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____7137;
                              FStar_Syntax_Syntax.vars = uu____7138;_},args)
                           when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____7165 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____7165 " is deprecated"  in
                           let msg1 =
                             if
                               (FStar_List.length args) >
                                 (Prims.parse_int "0")
                             then
                               let uu____7175 =
                                 let uu____7176 =
                                   let uu____7179 = FStar_List.hd args  in
                                   FStar_Pervasives_Native.fst uu____7179  in
                                 uu____7176.FStar_Syntax_Syntax.n  in
                               match uu____7175 with
                               | FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_string (s,uu____7201))
                                   when
                                   Prims.op_Negation
                                     ((FStar_Util.trim_string s) = "")
                                   ->
                                   Prims.strcat msg
                                     (Prims.strcat ", use "
                                        (Prims.strcat s " instead"))
                               | uu____7202 -> msg
                             else msg  in
                           let uu____7204 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____7204
                             (FStar_Errors.Warning_DeprecatedDefinition,
                               msg1)
                       | FStar_Syntax_Syntax.Tm_fvar fv when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____7207 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____7207 " is deprecated"  in
                           let uu____7208 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____7208
                             (FStar_Errors.Warning_DeprecatedDefinition, msg)
                       | uu____7209 -> ()) attrs1
                   in
                (warn_if_deprecated attrs;
                 (let tm1 = setpos tm  in
                  if mut
                  then
                    let uu____7214 =
                      let uu____7215 =
                        let uu____7222 = mk_ref_read tm1  in
                        (uu____7222,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Mutable_rval))
                         in
                      FStar_Syntax_Syntax.Tm_meta uu____7215  in
                    FStar_All.pipe_left mk1 uu____7214
                  else tm1))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____7240 =
          let uu____7241 = unparen t  in uu____7241.FStar_Parser_AST.tm  in
        match uu____7240 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____7242; FStar_Ident.ident = uu____7243;
              FStar_Ident.nsstr = uu____7244; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____7247 ->
            let uu____7248 =
              let uu____7253 =
                let uu____7254 = FStar_Parser_AST.term_to_string t  in
                Prims.strcat "Unknown attribute " uu____7254  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____7253)  in
            FStar_Errors.raise_error uu____7248 t.FStar_Parser_AST.range
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
          let uu___280_7337 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___280_7337.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___280_7337.FStar_Syntax_Syntax.vars)
          }  in
        let uu____7340 =
          let uu____7341 = unparen top  in uu____7341.FStar_Parser_AST.tm  in
        match uu____7340 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____7346 ->
            let uu____7353 = desugar_formula env top  in (uu____7353, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____7360 = desugar_formula env t  in (uu____7360, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____7367 = desugar_formula env t  in (uu____7367, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____7391 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____7391, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____7393 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____7393, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____7401 =
                let uu____7402 =
                  let uu____7409 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____7409, args)  in
                FStar_Parser_AST.Op uu____7402  in
              FStar_Parser_AST.mk_term uu____7401 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____7412 =
              let uu____7413 =
                let uu____7414 =
                  let uu____7421 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____7421, [e])  in
                FStar_Parser_AST.Op uu____7414  in
              FStar_Parser_AST.mk_term uu____7413 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____7412
        | FStar_Parser_AST.Op (op_star,uu____7425::uu____7426::[]) when
            (let uu____7431 = FStar_Ident.text_of_id op_star  in
             uu____7431 = "*") &&
              (let uu____7433 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____7433 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____7448;_},t1::t2::[])
                  ->
                  let uu____7453 = flatten1 t1  in
                  FStar_List.append uu____7453 [t2]
              | uu____7456 -> [t]  in
            let uu____7457 =
              let uu____7482 =
                let uu____7505 =
                  let uu____7508 = unparen top  in flatten1 uu____7508  in
                FStar_All.pipe_right uu____7505
                  (FStar_List.map
                     (fun t  ->
                        let uu____7543 = desugar_typ_aq env t  in
                        match uu____7543 with
                        | (t',aq) ->
                            let uu____7554 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____7554, aq)))
                 in
              FStar_All.pipe_right uu____7482 FStar_List.unzip  in
            (match uu____7457 with
             | (targs,aqs) ->
                 let uu____7663 =
                   let uu____7668 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____7668
                    in
                 (match uu____7663 with
                  | (tup,uu____7686) ->
                      let uu____7687 =
                        mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                      (uu____7687, (join_aqs aqs))))
        | FStar_Parser_AST.Tvar a ->
            let uu____7701 =
              let uu____7702 =
                let uu____7705 =
                  FStar_Syntax_DsEnv.fail_or2
                    (FStar_Syntax_DsEnv.try_lookup_id env) a
                   in
                FStar_Pervasives_Native.fst uu____7705  in
              FStar_All.pipe_left setpos uu____7702  in
            (uu____7701, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____7717 =
              let uu____7722 =
                let uu____7723 =
                  let uu____7724 = FStar_Ident.text_of_id u  in
                  Prims.strcat uu____7724 " in non-universe context"  in
                Prims.strcat "Unexpected universe variable " uu____7723  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____7722)  in
            FStar_Errors.raise_error uu____7717 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____7735 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____7735 with
             | FStar_Pervasives_Native.None  ->
                 let uu____7742 =
                   let uu____7747 =
                     let uu____7748 = FStar_Ident.text_of_id s  in
                     Prims.strcat "Unexpected or unbound operator: "
                       uu____7748
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____7747)
                    in
                 FStar_Errors.raise_error uu____7742
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let uu____7758 =
                     let uu____7783 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____7845 = desugar_term_aq env t  in
                               match uu____7845 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____7783 FStar_List.unzip  in
                   (match uu____7758 with
                    | (args1,aqs) ->
                        let uu____7978 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____7978, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____7994)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____8009 =
              let uu___281_8010 = top  in
              let uu____8011 =
                let uu____8012 =
                  let uu____8019 =
                    let uu___282_8020 = top  in
                    let uu____8021 =
                      let uu____8022 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8022  in
                    {
                      FStar_Parser_AST.tm = uu____8021;
                      FStar_Parser_AST.range =
                        (uu___282_8020.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___282_8020.FStar_Parser_AST.level)
                    }  in
                  (uu____8019, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8012  in
              {
                FStar_Parser_AST.tm = uu____8011;
                FStar_Parser_AST.range =
                  (uu___281_8010.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___281_8010.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8009
        | FStar_Parser_AST.Construct (n1,(a,uu____8025)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____8041 =
                let uu___283_8042 = top  in
                let uu____8043 =
                  let uu____8044 =
                    let uu____8051 =
                      let uu___284_8052 = top  in
                      let uu____8053 =
                        let uu____8054 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____8054  in
                      {
                        FStar_Parser_AST.tm = uu____8053;
                        FStar_Parser_AST.range =
                          (uu___284_8052.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___284_8052.FStar_Parser_AST.level)
                      }  in
                    (uu____8051, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____8044  in
                {
                  FStar_Parser_AST.tm = uu____8043;
                  FStar_Parser_AST.range =
                    (uu___283_8042.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___283_8042.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____8041))
        | FStar_Parser_AST.Construct (n1,(a,uu____8057)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____8072 =
              let uu___285_8073 = top  in
              let uu____8074 =
                let uu____8075 =
                  let uu____8082 =
                    let uu___286_8083 = top  in
                    let uu____8084 =
                      let uu____8085 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8085  in
                    {
                      FStar_Parser_AST.tm = uu____8084;
                      FStar_Parser_AST.range =
                        (uu___286_8083.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___286_8083.FStar_Parser_AST.level)
                    }  in
                  (uu____8082, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8075  in
              {
                FStar_Parser_AST.tm = uu____8074;
                FStar_Parser_AST.range =
                  (uu___285_8073.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___285_8073.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8072
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8086; FStar_Ident.ident = uu____8087;
              FStar_Ident.nsstr = uu____8088; FStar_Ident.str = "Type0";_}
            ->
            let uu____8091 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____8091, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8092; FStar_Ident.ident = uu____8093;
              FStar_Ident.nsstr = uu____8094; FStar_Ident.str = "Type";_}
            ->
            let uu____8097 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____8097, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____8098; FStar_Ident.ident = uu____8099;
               FStar_Ident.nsstr = uu____8100; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____8118 =
              let uu____8119 =
                let uu____8120 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____8120  in
              mk1 uu____8119  in
            (uu____8118, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8121; FStar_Ident.ident = uu____8122;
              FStar_Ident.nsstr = uu____8123; FStar_Ident.str = "Effect";_}
            ->
            let uu____8126 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____8126, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8127; FStar_Ident.ident = uu____8128;
              FStar_Ident.nsstr = uu____8129; FStar_Ident.str = "True";_}
            ->
            let uu____8132 =
              let uu____8133 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8133
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8132, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8134; FStar_Ident.ident = uu____8135;
              FStar_Ident.nsstr = uu____8136; FStar_Ident.str = "False";_}
            ->
            let uu____8139 =
              let uu____8140 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8140
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8139, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____8143;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____8145 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____8145 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____8154 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_constant_at_level
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None
                     in
                  (uu____8154, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____8155 =
                    let uu____8156 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____8156 txt
                     in
                  failwith uu____8155))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8163 = desugar_name mk1 setpos env true l  in
              (uu____8163, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8166 = desugar_name mk1 setpos env true l  in
              (uu____8166, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____8177 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____8177 with
                | FStar_Pervasives_Native.Some uu____8186 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____8191 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____8191 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____8205 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____8222 =
                    let uu____8223 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____8223  in
                  (uu____8222, noaqs)
              | uu____8224 ->
                  let uu____8231 =
                    let uu____8236 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____8236)  in
                  FStar_Errors.raise_error uu____8231
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____8243 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____8243 with
              | FStar_Pervasives_Native.None  ->
                  let uu____8250 =
                    let uu____8255 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____8255)
                     in
                  FStar_Errors.raise_error uu____8250
                    top.FStar_Parser_AST.range
              | uu____8260 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____8264 = desugar_name mk1 setpos env true lid'  in
                  (uu____8264, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8280 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____8280 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____8299 ->
                       let uu____8306 =
                         FStar_Util.take
                           (fun uu____8330  ->
                              match uu____8330 with
                              | (uu____8335,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____8306 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____8380 =
                              let uu____8405 =
                                FStar_List.map
                                  (fun uu____8448  ->
                                     match uu____8448 with
                                     | (t,imp) ->
                                         let uu____8465 =
                                           desugar_term_aq env t  in
                                         (match uu____8465 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____8405
                                FStar_List.unzip
                               in
                            (match uu____8380 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____8606 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____8606, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____8624 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____8624 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.strcat "Constructor "
                             (Prims.strcat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____8631 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.strcat "Effect "
                             (Prims.strcat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____8642 =
              FStar_List.fold_left
                (fun uu____8687  ->
                   fun b  ->
                     match uu____8687 with
                     | (env1,tparams,typs) ->
                         let uu____8744 = desugar_binder env1 b  in
                         (match uu____8744 with
                          | (xopt,t1) ->
                              let uu____8773 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____8782 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____8782)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____8773 with
                               | (env2,x) ->
                                   let uu____8802 =
                                     let uu____8805 =
                                       let uu____8808 =
                                         let uu____8809 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____8809
                                          in
                                       [uu____8808]  in
                                     FStar_List.append typs uu____8805  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___287_8835 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___287_8835.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___287_8835.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____8802)))) (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      FStar_Pervasives_Native.None])
               in
            (match uu____8642 with
             | (env1,uu____8863,targs) ->
                 let uu____8885 =
                   let uu____8890 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____8890
                    in
                 (match uu____8885 with
                  | (tup,uu____8900) ->
                      let uu____8901 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_app (tup, targs))
                         in
                      (uu____8901, noaqs)))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____8920 = uncurry binders t  in
            (match uu____8920 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___244_8964 =
                   match uu___244_8964 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1  in
                       let uu____8980 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____8980
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____9004 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____9004 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____9037 = aux env [] bs  in (uu____9037, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____9046 = desugar_binder env b  in
            (match uu____9046 with
             | (FStar_Pervasives_Native.None ,uu____9057) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____9071 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____9071 with
                  | ((x,uu____9087),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____9100 =
                        let uu____9101 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____9101  in
                      (uu____9100, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let bvss = FStar_List.map gather_pattern_bound_vars binders  in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set1::sets2 ->
                    let i = FStar_Util.set_intersect acc set1  in
                    let uu____9179 = FStar_Util.set_is_empty i  in
                    if uu____9179
                    then
                      let uu____9182 = FStar_Util.set_union acc set1  in
                      aux uu____9182 sets2
                    else
                      (let uu____9186 =
                         let uu____9187 = FStar_Util.set_elements i  in
                         FStar_List.hd uu____9187  in
                       FStar_Pervasives_Native.Some uu____9186)
                 in
              let uu____9190 = FStar_Syntax_Syntax.new_id_set ()  in
              aux uu____9190 sets  in
            ((let uu____9194 = check_disjoint bvss  in
              match uu____9194 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some id1 ->
                  let uu____9198 =
                    let uu____9203 =
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        id1.FStar_Ident.idText
                       in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____9203)
                     in
                  let uu____9204 = FStar_Ident.range_of_id id1  in
                  FStar_Errors.raise_error uu____9198 uu____9204);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern)
                 in
              let uu____9212 =
                FStar_List.fold_left
                  (fun uu____9232  ->
                     fun pat  ->
                       match uu____9232 with
                       | (env1,ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____9258,(t,FStar_Pervasives_Native.None ))
                                ->
                                let uu____9268 =
                                  let uu____9271 = free_type_vars env1 t  in
                                  FStar_List.append uu____9271 ftvs  in
                                (env1, uu____9268)
                            | FStar_Parser_AST.PatAscribed
                                (uu____9276,(t,FStar_Pervasives_Native.Some
                                             tac))
                                ->
                                let uu____9287 =
                                  let uu____9290 = free_type_vars env1 t  in
                                  let uu____9293 =
                                    let uu____9296 = free_type_vars env1 tac
                                       in
                                    FStar_List.append uu____9296 ftvs  in
                                  FStar_List.append uu____9290 uu____9293  in
                                (env1, uu____9287)
                            | uu____9301 -> (env1, ftvs))) (env, []) binders1
                 in
              match uu____9212 with
              | (uu____9310,ftv) ->
                  let ftv1 = sort_ftv ftv  in
                  let binders2 =
                    let uu____9322 =
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
                    FStar_List.append uu____9322 binders1  in
                  let rec aux env1 bs sc_pat_opt uu___245_9379 =
                    match uu___245_9379 with
                    | [] ->
                        let uu____9406 = desugar_term_aq env1 body  in
                        (match uu____9406 with
                         | (body1,aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc,pat) ->
                                   let body2 =
                                     let uu____9443 =
                                       let uu____9444 =
                                         FStar_Syntax_Syntax.pat_bvs pat  in
                                       FStar_All.pipe_right uu____9444
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder)
                                        in
                                     FStar_Syntax_Subst.close uu____9443
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
                             let uu____9513 =
                               let uu____9516 =
                                 no_annot_abs (FStar_List.rev bs) body2  in
                               setpos uu____9516  in
                             (uu____9513, aq))
                    | p::rest ->
                        let uu____9531 = desugar_binding_pat env1 p  in
                        (match uu____9531 with
                         | (env2,b,pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1,uu____9565)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____9580 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange
                                in
                             let uu____9587 =
                               match b with
                               | LetBinder uu____9628 ->
                                   failwith "Impossible"
                               | LocalBinder (x,aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None
                                        ,uu____9696) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.None ) ->
                                         let uu____9750 =
                                           let uu____9759 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____9759, p1)  in
                                         FStar_Pervasives_Native.Some
                                           uu____9750
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.Some
                                        (sc,p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____9821,uu____9822) ->
                                              let tup2 =
                                                let uu____9824 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.parse_int "2")
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____9824
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____9828 =
                                                  let uu____9835 =
                                                    let uu____9836 =
                                                      let uu____9853 =
                                                        mk1
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let uu____9856 =
                                                        let uu____9867 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let uu____9876 =
                                                          let uu____9887 =
                                                            let uu____9896 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____9896
                                                             in
                                                          [uu____9887]  in
                                                        uu____9867 ::
                                                          uu____9876
                                                         in
                                                      (uu____9853,
                                                        uu____9856)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____9836
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____9835
                                                   in
                                                uu____9828
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range
                                                 in
                                              let p2 =
                                                let uu____9947 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____9947
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____9990,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____9992,pats)) ->
                                              let tupn =
                                                let uu____10035 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    ((Prims.parse_int "1") +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10035
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10047 =
                                                  let uu____10048 =
                                                    let uu____10065 =
                                                      mk1
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____10068 =
                                                      let uu____10079 =
                                                        let uu____10090 =
                                                          let uu____10099 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____10099
                                                           in
                                                        [uu____10090]  in
                                                      FStar_List.append args
                                                        uu____10079
                                                       in
                                                    (uu____10065,
                                                      uu____10068)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____10048
                                                   in
                                                mk1 uu____10047  in
                                              let p2 =
                                                let uu____10147 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats [(p1, false)])))
                                                  uu____10147
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____10188 ->
                                              failwith "Impossible")
                                      in
                                   ((x, aq), sc_pat_opt1)
                                in
                             (match uu____9587 with
                              | (b1,sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest))
                     in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____10281,uu____10282,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____10304 =
                let uu____10305 = unparen e  in
                uu____10305.FStar_Parser_AST.tm  in
              match uu____10304 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____10315 ->
                  let uu____10316 = desugar_term_aq env e  in
                  (match uu____10316 with
                   | (head1,aq) ->
                       let uu____10329 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____10329, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____10336 ->
            let rec aux args aqs e =
              let uu____10413 =
                let uu____10414 = unparen e  in
                uu____10414.FStar_Parser_AST.tm  in
              match uu____10413 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____10432 = desugar_term_aq env t  in
                  (match uu____10432 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____10480 ->
                  let uu____10481 = desugar_term_aq env e  in
                  (match uu____10481 with
                   | (head1,aq) ->
                       let uu____10502 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____10502, (join_aqs (aq :: aqs))))
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
            let uu____10562 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____10562
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
            let uu____10614 = desugar_term_aq env t  in
            (match uu____10614 with
             | (tm,s) ->
                 let uu____10625 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____10625, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____10631 =
              let uu____10644 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____10644 then desugar_typ_aq else desugar_term_aq  in
            uu____10631 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____10699 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____10842  ->
                        match uu____10842 with
                        | (attr_opt,(p,def)) ->
                            let uu____10900 = is_app_pattern p  in
                            if uu____10900
                            then
                              let uu____10931 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____10931, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____11013 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____11013, def1)
                               | uu____11058 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____11096);
                                           FStar_Parser_AST.prange =
                                             uu____11097;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____11145 =
                                            let uu____11166 =
                                              let uu____11171 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____11171  in
                                            (uu____11166, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____11145, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____11262) ->
                                        if top_level
                                        then
                                          let uu____11297 =
                                            let uu____11318 =
                                              let uu____11323 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____11323  in
                                            (uu____11318, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____11297, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____11413 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____11444 =
                FStar_List.fold_left
                  (fun uu____11517  ->
                     fun uu____11518  ->
                       match (uu____11517, uu____11518) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____11626,uu____11627),uu____11628))
                           ->
                           let uu____11745 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____11771 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____11771 with
                                  | (env2,xx) ->
                                      let uu____11790 =
                                        let uu____11793 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____11793 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____11790))
                             | FStar_Util.Inr l ->
                                 let uu____11801 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (uu____11801, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____11745 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____11444 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____11949 =
                    match uu____11949 with
                    | (attrs_opt,(uu____11985,args,result_t),def) ->
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
                                let uu____12073 = is_comp_type env1 t  in
                                if uu____12073
                                then
                                  ((let uu____12075 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____12085 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____12085))
                                       in
                                    match uu____12075 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____12088 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____12090 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____12090))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____12088
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
                          | uu____12097 ->
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
                              let uu____12112 =
                                let uu____12113 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____12113
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____12112
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
                  let uu____12190 = desugar_term_aq env' body  in
                  (match uu____12190 with
                   | (body1,aq) ->
                       let uu____12203 =
                         let uu____12206 =
                           let uu____12207 =
                             let uu____12220 =
                               FStar_Syntax_Subst.close rec_bindings1 body1
                                in
                             ((is_rec, lbs1), uu____12220)  in
                           FStar_Syntax_Syntax.Tm_let uu____12207  in
                         FStar_All.pipe_left mk1 uu____12206  in
                       (uu____12203, aq))
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
              let uu____12300 =
                desugar_binding_pat_maybe_top top_level env pat is_mutable
                 in
              match uu____12300 with
              | (env1,binder,pat1) ->
                  let uu____12322 =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let uu____12348 = desugar_term_aq env1 t2  in
                        (match uu____12348 with
                         | (body1,aq) ->
                             let fv =
                               let uu____12362 =
                                 FStar_Syntax_Util.incr_delta_qualifier t12
                                  in
                               FStar_Syntax_Syntax.lid_as_fv l uu____12362
                                 FStar_Pervasives_Native.None
                                in
                             let uu____12363 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t12,
                                            (t12.FStar_Syntax_Syntax.pos))]),
                                      body1))
                                in
                             (uu____12363, aq))
                    | LocalBinder (x,uu____12393) ->
                        let uu____12394 = desugar_term_aq env1 t2  in
                        (match uu____12394 with
                         | (body1,aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | ({
                                    FStar_Syntax_Syntax.v =
                                      FStar_Syntax_Syntax.Pat_wild
                                      uu____12408;
                                    FStar_Syntax_Syntax.p = uu____12409;_},uu____12410)::[]
                                   -> body1
                               | uu____12423 ->
                                   let uu____12426 =
                                     let uu____12433 =
                                       let uu____12434 =
                                         let uu____12457 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         let uu____12460 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1
                                            in
                                         (uu____12457, uu____12460)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____12434
                                        in
                                     FStar_Syntax_Syntax.mk uu____12433  in
                                   uu____12426 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range
                                in
                             let uu____12500 =
                               let uu____12503 =
                                 let uu____12504 =
                                   let uu____12517 =
                                     let uu____12520 =
                                       let uu____12521 =
                                         FStar_Syntax_Syntax.mk_binder x  in
                                       [uu____12521]  in
                                     FStar_Syntax_Subst.close uu____12520
                                       body2
                                      in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t12,
                                           (t12.FStar_Syntax_Syntax.pos))]),
                                     uu____12517)
                                    in
                                 FStar_Syntax_Syntax.Tm_let uu____12504  in
                               FStar_All.pipe_left mk1 uu____12503  in
                             (uu____12500, aq))
                     in
                  (match uu____12322 with
                   | (tm,aq) ->
                       if is_mutable
                       then
                         let uu____12584 =
                           FStar_All.pipe_left mk1
                             (FStar_Syntax_Syntax.Tm_meta
                                (tm,
                                  (FStar_Syntax_Syntax.Meta_desugared
                                     FStar_Syntax_Syntax.Mutable_alloc)))
                            in
                         (uu____12584, aq)
                       else (tm, aq))
               in
            let uu____12596 = FStar_List.hd lbs  in
            (match uu____12596 with
             | (attrs,(head_pat,defn)) ->
                 let uu____12640 = is_rec || (is_app_pattern head_pat)  in
                 if uu____12640
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____12653 =
                let uu____12654 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____12654  in
              mk1 uu____12653  in
            let uu____12655 = desugar_term_aq env t1  in
            (match uu____12655 with
             | (t1',aq1) ->
                 let uu____12666 = desugar_term_aq env t2  in
                 (match uu____12666 with
                  | (t2',aq2) ->
                      let uu____12677 = desugar_term_aq env t3  in
                      (match uu____12677 with
                       | (t3',aq3) ->
                           let uu____12688 =
                             let uu____12689 =
                               let uu____12690 =
                                 let uu____12713 =
                                   let uu____12730 =
                                     let uu____12745 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t2.FStar_Parser_AST.range
                                        in
                                     (uu____12745,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____12758 =
                                     let uu____12775 =
                                       let uu____12790 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t3.FStar_Parser_AST.range
                                          in
                                       (uu____12790,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____12775]  in
                                   uu____12730 :: uu____12758  in
                                 (t1', uu____12713)  in
                               FStar_Syntax_Syntax.Tm_match uu____12690  in
                             mk1 uu____12689  in
                           (uu____12688, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____12981 =
              match uu____12981 with
              | (pat,wopt,b) ->
                  let uu____13003 = desugar_match_pat env pat  in
                  (match uu____13003 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____13034 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____13034
                          in
                       let uu____13039 = desugar_term_aq env1 b  in
                       (match uu____13039 with
                        | (b1,aq) ->
                            let uu____13052 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____13052, aq)))
               in
            let uu____13057 = desugar_term_aq env e  in
            (match uu____13057 with
             | (e1,aq) ->
                 let uu____13068 =
                   let uu____13099 =
                     let uu____13132 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____13132 FStar_List.unzip  in
                   FStar_All.pipe_right uu____13099
                     (fun uu____13262  ->
                        match uu____13262 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____13068 with
                  | (brs,aqs) ->
                      let uu____13481 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____13481, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____13515 =
              let uu____13536 = is_comp_type env t  in
              if uu____13536
              then
                let comp = desugar_comp t.FStar_Parser_AST.range env t  in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____13587 = desugar_term_aq env t  in
                 match uu____13587 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____13515 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____13679 = desugar_term_aq env e  in
                 (match uu____13679 with
                  | (e1,aq) ->
                      let uu____13690 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____13690, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____13729,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____13770 = FStar_List.hd fields  in
              match uu____13770 with | (f,uu____13782) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____13828  ->
                        match uu____13828 with
                        | (g,uu____13834) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____13840,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____13854 =
                         let uu____13859 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____13859)
                          in
                       FStar_Errors.raise_error uu____13854
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
                  let uu____13867 =
                    let uu____13878 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____13909  ->
                              match uu____13909 with
                              | (f,uu____13919) ->
                                  let uu____13920 =
                                    let uu____13921 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____13921
                                     in
                                  (uu____13920, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____13878)  in
                  FStar_Parser_AST.Construct uu____13867
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____13939 =
                      let uu____13940 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____13940  in
                    FStar_Parser_AST.mk_term uu____13939
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____13942 =
                      let uu____13955 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____13985  ->
                                match uu____13985 with
                                | (f,uu____13995) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____13955)  in
                    FStar_Parser_AST.Record uu____13942  in
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
            let uu____14055 = desugar_term_aq env recterm1  in
            (match uu____14055 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____14071;
                         FStar_Syntax_Syntax.vars = uu____14072;_},args)
                      ->
                      let uu____14098 =
                        let uu____14099 =
                          let uu____14100 =
                            let uu____14117 =
                              let uu____14120 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____14121 =
                                let uu____14124 =
                                  let uu____14125 =
                                    let uu____14132 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____14132)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____14125
                                   in
                                FStar_Pervasives_Native.Some uu____14124  in
                              FStar_Syntax_Syntax.fvar uu____14120
                                FStar_Syntax_Syntax.delta_constant
                                uu____14121
                               in
                            (uu____14117, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____14100  in
                        FStar_All.pipe_left mk1 uu____14099  in
                      (uu____14098, s)
                  | uu____14161 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____14165 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____14165 with
              | (constrname,is_rec) ->
                  let uu____14180 = desugar_term_aq env e  in
                  (match uu____14180 with
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
                       let uu____14198 =
                         let uu____14199 =
                           let uu____14200 =
                             let uu____14217 =
                               let uu____14220 =
                                 let uu____14221 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____14221
                                  in
                               FStar_Syntax_Syntax.fvar uu____14220
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1")) qual
                                in
                             let uu____14222 =
                               let uu____14233 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____14233]  in
                             (uu____14217, uu____14222)  in
                           FStar_Syntax_Syntax.Tm_app uu____14200  in
                         FStar_All.pipe_left mk1 uu____14199  in
                       (uu____14198, s))))
        | FStar_Parser_AST.NamedTyp (uu____14270,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____14279 =
              let uu____14280 = FStar_Syntax_Subst.compress tm  in
              uu____14280.FStar_Syntax_Syntax.n  in
            (match uu____14279 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____14288 =
                   let uu___288_14289 =
                     let uu____14290 =
                       let uu____14291 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____14291  in
                     FStar_Syntax_Util.exp_string uu____14290  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___288_14289.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___288_14289.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____14288, noaqs)
             | uu____14292 ->
                 let uu____14293 =
                   let uu____14298 =
                     let uu____14299 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.strcat "VQuote, expected an fvar, got: "
                       uu____14299
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____14298)  in
                 FStar_Errors.raise_error uu____14293
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____14305 = desugar_term_aq env e  in
            (match uu____14305 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____14317 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____14317, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____14322 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____14323 =
              let uu____14324 =
                let uu____14331 = desugar_term env e  in (bv, uu____14331)
                 in
              [uu____14324]  in
            (uu____14322, uu____14323)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____14356 =
              let uu____14357 =
                let uu____14358 =
                  let uu____14365 = desugar_term env e  in (uu____14365, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____14358  in
              FStar_All.pipe_left mk1 uu____14357  in
            (uu____14356, noaqs)
        | uu____14370 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____14371 = desugar_formula env top  in
            (uu____14371, noaqs)
        | uu____14372 ->
            let uu____14373 =
              let uu____14378 =
                let uu____14379 = FStar_Parser_AST.term_to_string top  in
                Prims.strcat "Unexpected term: " uu____14379  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____14378)  in
            FStar_Errors.raise_error uu____14373 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____14385 -> false
    | uu____14394 -> true

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
           (fun uu____14431  ->
              match uu____14431 with
              | (a,imp) ->
                  let uu____14444 = desugar_term env a  in
                  arg_withimp_e imp uu____14444))

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
        let is_requires uu____14476 =
          match uu____14476 with
          | (t1,uu____14482) ->
              let uu____14483 =
                let uu____14484 = unparen t1  in
                uu____14484.FStar_Parser_AST.tm  in
              (match uu____14483 with
               | FStar_Parser_AST.Requires uu____14485 -> true
               | uu____14492 -> false)
           in
        let is_ensures uu____14502 =
          match uu____14502 with
          | (t1,uu____14508) ->
              let uu____14509 =
                let uu____14510 = unparen t1  in
                uu____14510.FStar_Parser_AST.tm  in
              (match uu____14509 with
               | FStar_Parser_AST.Ensures uu____14511 -> true
               | uu____14518 -> false)
           in
        let is_app head1 uu____14533 =
          match uu____14533 with
          | (t1,uu____14539) ->
              let uu____14540 =
                let uu____14541 = unparen t1  in
                uu____14541.FStar_Parser_AST.tm  in
              (match uu____14540 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____14543;
                      FStar_Parser_AST.level = uu____14544;_},uu____14545,uu____14546)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____14547 -> false)
           in
        let is_smt_pat uu____14557 =
          match uu____14557 with
          | (t1,uu____14563) ->
              let uu____14564 =
                let uu____14565 = unparen t1  in
                uu____14565.FStar_Parser_AST.tm  in
              (match uu____14564 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____14568);
                             FStar_Parser_AST.range = uu____14569;
                             FStar_Parser_AST.level = uu____14570;_},uu____14571)::uu____14572::[])
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
                             FStar_Parser_AST.range = uu____14611;
                             FStar_Parser_AST.level = uu____14612;_},uu____14613)::uu____14614::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
               | uu____14639 -> false)
           in
        let is_decreases = is_app "decreases"  in
        let pre_process_comp_typ t1 =
          let uu____14671 = head_and_args t1  in
          match uu____14671 with
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
                   let thunk_ens uu____14769 =
                     match uu____14769 with
                     | (e,i) ->
                         let uu____14780 = thunk_ens_ e  in (uu____14780, i)
                      in
                   let fail_lemma uu____14792 =
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
                         let uu____14872 =
                           let uu____14879 =
                             let uu____14886 = thunk_ens ens  in
                             [uu____14886; nil_pat]  in
                           req_true :: uu____14879  in
                         unit_tm :: uu____14872
                     | req::ens::[] when
                         (is_requires req) && (is_ensures ens) ->
                         let uu____14933 =
                           let uu____14940 =
                             let uu____14947 = thunk_ens ens  in
                             [uu____14947; nil_pat]  in
                           req :: uu____14940  in
                         unit_tm :: uu____14933
                     | ens::smtpat::[] when
                         (((let uu____14996 = is_requires ens  in
                            Prims.op_Negation uu____14996) &&
                             (let uu____14998 = is_smt_pat ens  in
                              Prims.op_Negation uu____14998))
                            &&
                            (let uu____15000 = is_decreases ens  in
                             Prims.op_Negation uu____15000))
                           && (is_smt_pat smtpat)
                         ->
                         let uu____15001 =
                           let uu____15008 =
                             let uu____15015 = thunk_ens ens  in
                             [uu____15015; smtpat]  in
                           req_true :: uu____15008  in
                         unit_tm :: uu____15001
                     | ens::dec::[] when
                         (is_ensures ens) && (is_decreases dec) ->
                         let uu____15062 =
                           let uu____15069 =
                             let uu____15076 = thunk_ens ens  in
                             [uu____15076; nil_pat; dec]  in
                           req_true :: uu____15069  in
                         unit_tm :: uu____15062
                     | ens::dec::smtpat::[] when
                         ((is_ensures ens) && (is_decreases dec)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____15136 =
                           let uu____15143 =
                             let uu____15150 = thunk_ens ens  in
                             [uu____15150; smtpat; dec]  in
                           req_true :: uu____15143  in
                         unit_tm :: uu____15136
                     | req::ens::dec::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_decreases dec)
                         ->
                         let uu____15210 =
                           let uu____15217 =
                             let uu____15224 = thunk_ens ens  in
                             [uu____15224; nil_pat; dec]  in
                           req :: uu____15217  in
                         unit_tm :: uu____15210
                     | req::ens::smtpat::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____15284 =
                           let uu____15291 =
                             let uu____15298 = thunk_ens ens  in
                             [uu____15298; smtpat]  in
                           req :: uu____15291  in
                         unit_tm :: uu____15284
                     | req::ens::dec::smtpat::[] when
                         (((is_requires req) && (is_ensures ens)) &&
                            (is_smt_pat smtpat))
                           && (is_decreases dec)
                         ->
                         let uu____15363 =
                           let uu____15370 =
                             let uu____15377 = thunk_ens ens  in
                             [uu____15377; dec; smtpat]  in
                           req :: uu____15370  in
                         unit_tm :: uu____15363
                     | _other -> fail_lemma ()  in
                   let head_and_attributes =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) lemma
                      in
                   (head_and_attributes, args1)
               | FStar_Parser_AST.Name l when
                   FStar_Syntax_DsEnv.is_effect_name env l ->
                   let uu____15439 =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) l
                      in
                   (uu____15439, args)
               | FStar_Parser_AST.Name l when
                   (let uu____15467 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____15467
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   let uu____15468 =
                     let uu____15475 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_Tot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____15475, [])  in
                   (uu____15468, args)
               | FStar_Parser_AST.Name l when
                   (let uu____15493 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____15493
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                   ->
                   let uu____15494 =
                     let uu____15501 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_GTot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____15501, [])  in
                   (uu____15494, args)
               | FStar_Parser_AST.Name l when
                   (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                      ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                     || ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                   ->
                   let uu____15517 =
                     let uu____15524 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_Tot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____15524, [])  in
                   (uu____15517, [(t1, FStar_Parser_AST.Nothing)])
               | uu____15547 ->
                   let default_effect =
                     let uu____15549 = FStar_Options.ml_ish ()  in
                     if uu____15549
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____15552 =
                           FStar_Options.warn_default_effects ()  in
                         if uu____15552
                         then
                           FStar_Errors.log_issue
                             head1.FStar_Parser_AST.range
                             (FStar_Errors.Warning_UseDefaultEffect,
                               "Using default effect Tot")
                         else ());
                        FStar_Parser_Const.effect_Tot_lid)
                      in
                   let uu____15554 =
                     let uu____15561 =
                       FStar_Ident.set_lid_range default_effect
                         head1.FStar_Parser_AST.range
                        in
                     (uu____15561, [])  in
                   (uu____15554, [(t1, FStar_Parser_AST.Nothing)]))
           in
        let uu____15584 = pre_process_comp_typ t  in
        match uu____15584 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____15633 =
                  let uu____15638 =
                    let uu____15639 = FStar_Syntax_Print.lid_to_string eff
                       in
                    FStar_Util.format1 "Not enough args to effect %s"
                      uu____15639
                     in
                  (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____15638)  in
                fail1 uu____15633)
             else ();
             (let is_universe uu____15650 =
                match uu____15650 with
                | (uu____15655,imp) -> imp = FStar_Parser_AST.UnivApp  in
              let uu____15657 = FStar_Util.take is_universe args  in
              match uu____15657 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____15716  ->
                         match uu____15716 with
                         | (u,imp) -> desugar_universe u) universes
                     in
                  let uu____15723 =
                    let uu____15738 = FStar_List.hd args1  in
                    let uu____15747 = FStar_List.tl args1  in
                    (uu____15738, uu____15747)  in
                  (match uu____15723 with
                   | (result_arg,rest) ->
                       let result_typ =
                         desugar_typ env
                           (FStar_Pervasives_Native.fst result_arg)
                          in
                       let rest1 = desugar_args env rest  in
                       let uu____15802 =
                         let is_decrease uu____15840 =
                           match uu____15840 with
                           | (t1,uu____15850) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.pos = uu____15860;
                                       FStar_Syntax_Syntax.vars = uu____15861;_},uu____15862::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.decreases_lid
                                | uu____15901 -> false)
                            in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease)
                          in
                       (match uu____15802 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____16017  ->
                                      match uu____16017 with
                                      | (t1,uu____16027) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____16036,(arg,uu____16038)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____16077 -> failwith "impos")))
                               in
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
                                | uu____16094 -> false  in
                              (((is_empty decreases_clause) &&
                                  (is_empty rest2))
                                 && (is_empty cattributes))
                                && (is_empty universes1)
                               in
                            let uu____16105 =
                              no_additional_args &&
                                (FStar_Ident.lid_equals eff
                                   FStar_Parser_Const.effect_Tot_lid)
                               in
                            if uu____16105
                            then FStar_Syntax_Syntax.mk_Total result_typ
                            else
                              (let uu____16109 =
                                 no_additional_args &&
                                   (FStar_Ident.lid_equals eff
                                      FStar_Parser_Const.effect_GTot_lid)
                                  in
                               if uu____16109
                               then FStar_Syntax_Syntax.mk_GTotal result_typ
                               else
                                 (let flags1 =
                                    let uu____16116 =
                                      FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_Lemma_lid
                                       in
                                    if uu____16116
                                    then [FStar_Syntax_Syntax.LEMMA]
                                    else
                                      (let uu____16120 =
                                         FStar_Ident.lid_equals eff
                                           FStar_Parser_Const.effect_Tot_lid
                                          in
                                       if uu____16120
                                       then [FStar_Syntax_Syntax.TOTAL]
                                       else
                                         (let uu____16124 =
                                            FStar_Ident.lid_equals eff
                                              FStar_Parser_Const.effect_ML_lid
                                             in
                                          if uu____16124
                                          then [FStar_Syntax_Syntax.MLEFFECT]
                                          else
                                            (let uu____16128 =
                                               FStar_Ident.lid_equals eff
                                                 FStar_Parser_Const.effect_GTot_lid
                                                in
                                             if uu____16128
                                             then
                                               [FStar_Syntax_Syntax.SOMETRIVIAL]
                                             else [])))
                                     in
                                  let flags2 =
                                    FStar_List.append flags1 cattributes  in
                                  let rest3 =
                                    let uu____16146 =
                                      FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_Lemma_lid
                                       in
                                    if uu____16146
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
                                                  let uu____16235 =
                                                    FStar_Ident.set_lid_range
                                                      FStar_Parser_Const.pattern_lid
                                                      pat.FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_Syntax.fvar
                                                    uu____16235
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
                                            | uu____16256 -> pat  in
                                          let uu____16257 =
                                            let uu____16268 =
                                              let uu____16279 =
                                                let uu____16288 =
                                                  FStar_Syntax_Syntax.mk
                                                    (FStar_Syntax_Syntax.Tm_meta
                                                       (pat1,
                                                         (FStar_Syntax_Syntax.Meta_desugared
                                                            FStar_Syntax_Syntax.Meta_smt_pat)))
                                                    FStar_Pervasives_Native.None
                                                    pat1.FStar_Syntax_Syntax.pos
                                                   in
                                                (uu____16288, aq)  in
                                              [uu____16279]  in
                                            ens :: uu____16268  in
                                          req :: uu____16257
                                      | uu____16329 -> rest2
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
        | uu____16353 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___289_16374 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___289_16374.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___289_16374.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___290_16416 = b  in
             {
               FStar_Parser_AST.b = (uu___290_16416.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___290_16416.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___290_16416.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____16479 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____16479)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____16492 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____16492 with
             | (env1,a1) ->
                 let a2 =
                   let uu___291_16502 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___291_16502.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___291_16502.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____16528 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____16542 =
                     let uu____16545 =
                       let uu____16546 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____16546]  in
                     no_annot_abs uu____16545 body2  in
                   FStar_All.pipe_left setpos uu____16542  in
                 let uu____16567 =
                   let uu____16568 =
                     let uu____16585 =
                       let uu____16588 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____16588
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____16589 =
                       let uu____16600 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____16600]  in
                     (uu____16585, uu____16589)  in
                   FStar_Syntax_Syntax.Tm_app uu____16568  in
                 FStar_All.pipe_left mk1 uu____16567)
        | uu____16639 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____16719 = q (rest, pats, body)  in
              let uu____16726 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____16719 uu____16726
                FStar_Parser_AST.Formula
               in
            let uu____16727 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____16727 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____16736 -> failwith "impossible"  in
      let uu____16739 =
        let uu____16740 = unparen f  in uu____16740.FStar_Parser_AST.tm  in
      match uu____16739 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____16747,uu____16748) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____16759,uu____16760) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____16791 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____16791
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____16827 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____16827
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____16870 -> desugar_term env f

and (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                FStar_Pervasives_Native.tuple2 Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bs  ->
      let uu____16875 =
        FStar_List.fold_left
          (fun uu____16908  ->
             fun b  ->
               match uu____16908 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___292_16952 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___292_16952.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___292_16952.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___292_16952.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____16967 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____16967 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___293_16985 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___293_16985.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___293_16985.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____16986 =
                               let uu____16993 =
                                 let uu____16998 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____16998)  in
                               uu____16993 :: out  in
                             (env2, uu____16986))
                    | uu____17009 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____16875 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

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
          let uu____17080 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____17080)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____17085 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____17085)
      | FStar_Parser_AST.TVariable x ->
          let uu____17089 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____17089)
      | FStar_Parser_AST.NoName t ->
          let uu____17093 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____17093)
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
      fun uu___246_17101  ->
        match uu___246_17101 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____17123 = FStar_Syntax_Syntax.null_binder k  in
            (uu____17123, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____17140 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____17140 with
             | (env1,a1) ->
                 let uu____17157 =
                   let uu____17164 = trans_aqual env1 imp  in
                   ((let uu___294_17170 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___294_17170.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___294_17170.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____17164)
                    in
                 (uu____17157, env1))

and (trans_aqual :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___247_17178  ->
      match uu___247_17178 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____17182 =
            let uu____17183 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____17183  in
          FStar_Pervasives_Native.Some uu____17182
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None

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
               (fun uu___248_17219  ->
                  match uu___248_17219 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____17220 -> false))
           in
        let quals2 q =
          let uu____17233 =
            (let uu____17236 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____17236) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____17233
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____17250 = FStar_Ident.range_of_lid disc_name  in
                let uu____17251 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____17250;
                  FStar_Syntax_Syntax.sigquals = uu____17251;
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
            let uu____17290 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____17328  ->
                        match uu____17328 with
                        | (x,uu____17338) ->
                            let uu____17343 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____17343 with
                             | (field_name,uu____17351) ->
                                 let only_decl =
                                   ((let uu____17355 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____17355)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____17357 =
                                        let uu____17358 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____17358.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____17357)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____17374 =
                                       FStar_List.filter
                                         (fun uu___249_17378  ->
                                            match uu___249_17378 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____17379 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____17374
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___250_17392  ->
                                             match uu___250_17392 with
                                             | FStar_Syntax_Syntax.NoExtract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____17393 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____17395 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____17395;
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____17400 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____17400
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          (FStar_Syntax_Syntax.Delta_equational_at_level
                                             (Prims.parse_int "1"))
                                      else
                                        FStar_Syntax_Syntax.Delta_equational_at_level
                                          (Prims.parse_int "1")
                                       in
                                    let lb =
                                      let uu____17405 =
                                        let uu____17410 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____17410  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____17405;
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
                                      let uu____17414 =
                                        let uu____17415 =
                                          let uu____17422 =
                                            let uu____17425 =
                                              let uu____17426 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____17426
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____17425]  in
                                          ((false, [lb]), uu____17422)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____17415
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____17414;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____17290 FStar_List.flatten
  
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
            (lid,uu____17470,t,uu____17472,n1,uu____17474) when
            let uu____17479 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____17479 ->
            let uu____17480 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____17480 with
             | (formals,uu____17498) ->
                 (match formals with
                  | [] -> []
                  | uu____17527 ->
                      let filter_records uu___251_17543 =
                        match uu___251_17543 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____17546,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____17558 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____17560 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____17560 with
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
                      let uu____17570 = FStar_Util.first_N n1 formals  in
                      (match uu____17570 with
                       | (uu____17599,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____17633 -> []
  
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
                    let uu____17711 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____17711
                    then
                      let uu____17714 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____17714
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____17717 =
                      let uu____17722 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____17722  in
                    let uu____17723 =
                      if FStar_Util.is_some kopt
                      then
                        let uu____17728 =
                          let uu____17731 =
                            FStar_All.pipe_right kopt FStar_Util.must  in
                          FStar_Syntax_Syntax.mk_Total uu____17731  in
                        FStar_Syntax_Util.arrow typars uu____17728
                      else FStar_Syntax_Syntax.tun  in
                    let uu____17735 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____17717;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____17723;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____17735;
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
          let tycon_id uu___252_17786 =
            match uu___252_17786 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____17788,uu____17789) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____17799,uu____17800,uu____17801) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____17811,uu____17812,uu____17813) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____17843,uu____17844,uu____17845) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____17889) ->
                let uu____17890 =
                  let uu____17891 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____17891  in
                FStar_Parser_AST.mk_term uu____17890 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____17893 =
                  let uu____17894 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____17894  in
                FStar_Parser_AST.mk_term uu____17893 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____17896) ->
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
              | uu____17927 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____17935 =
                     let uu____17936 =
                       let uu____17943 = binder_to_term b  in
                       (out, uu____17943, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____17936  in
                   FStar_Parser_AST.mk_term uu____17935
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___253_17955 =
            match uu___253_17955 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____18011  ->
                       match uu____18011 with
                       | (x,t,uu____18022) ->
                           let uu____18027 =
                             let uu____18028 =
                               let uu____18033 =
                                 FStar_Syntax_Util.mangle_field_name x  in
                               (uu____18033, t)  in
                             FStar_Parser_AST.Annotated uu____18028  in
                           FStar_Parser_AST.mk_binder uu____18027
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____18035 =
                    let uu____18036 =
                      let uu____18037 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____18037  in
                    FStar_Parser_AST.mk_term uu____18036
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____18035 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let uu____18041 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____18068  ->
                          match uu____18068 with
                          | (x,uu____18078,uu____18079) ->
                              FStar_Syntax_Util.unmangle_field_name x))
                   in
                ((FStar_Parser_AST.TyconVariant
                    (id1, parms, kopt,
                      [(constrName, (FStar_Pervasives_Native.Some constrTyp),
                         FStar_Pervasives_Native.None, false)])),
                  uu____18041)
            | uu____18132 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___254_18171 =
            match uu___254_18171 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____18195 = typars_of_binders _env binders  in
                (match uu____18195 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____18231 =
                         let uu____18232 =
                           let uu____18233 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____18233  in
                         FStar_Parser_AST.mk_term uu____18232
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____18231 binders  in
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
            | uu____18244 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____18286 =
              FStar_List.fold_left
                (fun uu____18320  ->
                   fun uu____18321  ->
                     match (uu____18320, uu____18321) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____18390 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____18390 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____18286 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____18481 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____18481
                | uu____18482 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____18490 = desugar_abstract_tc quals env [] tc  in
              (match uu____18490 with
               | (uu____18503,uu____18504,se,uu____18506) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____18509,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____18526 =
                                 let uu____18527 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____18527  in
                               if uu____18526
                               then
                                 let uu____18528 =
                                   let uu____18533 =
                                     let uu____18534 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____18534
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____18533)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____18528
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
                           | uu____18543 ->
                               let uu____18544 =
                                 let uu____18551 =
                                   let uu____18552 =
                                     let uu____18567 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____18567)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____18552
                                    in
                                 FStar_Syntax_Syntax.mk uu____18551  in
                               uu____18544 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___295_18583 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___295_18583.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___295_18583.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___295_18583.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____18584 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____18587 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____18587
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____18600 = typars_of_binders env binders  in
              (match uu____18600 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____18634 =
                           FStar_Util.for_some
                             (fun uu___255_18636  ->
                                match uu___255_18636 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____18637 -> false) quals
                            in
                         if uu____18634
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____18642 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____18642
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____18647 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___256_18651  ->
                               match uu___256_18651 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____18652 -> false))
                        in
                     if uu____18647
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____18661 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____18661
                     then
                       let uu____18664 =
                         let uu____18671 =
                           let uu____18672 = unparen t  in
                           uu____18672.FStar_Parser_AST.tm  in
                         match uu____18671 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____18693 =
                               match FStar_List.rev args with
                               | (last_arg,uu____18723)::args_rev ->
                                   let uu____18735 =
                                     let uu____18736 = unparen last_arg  in
                                     uu____18736.FStar_Parser_AST.tm  in
                                   (match uu____18735 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____18764 -> ([], args))
                               | uu____18773 -> ([], args)  in
                             (match uu____18693 with
                              | (cattributes,args1) ->
                                  let uu____18812 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____18812))
                         | uu____18823 -> (t, [])  in
                       match uu____18664 with
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
                                  (fun uu___257_18845  ->
                                     match uu___257_18845 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____18846 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____18853)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____18877 = tycon_record_as_variant trec  in
              (match uu____18877 with
               | (t,fs) ->
                   let uu____18894 =
                     let uu____18897 =
                       let uu____18898 =
                         let uu____18907 =
                           let uu____18910 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____18910  in
                         (uu____18907, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____18898  in
                     uu____18897 :: quals  in
                   desugar_tycon env d uu____18894 [t])
          | uu____18915::uu____18916 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____19083 = et  in
                match uu____19083 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____19308 ->
                         let trec = tc  in
                         let uu____19332 = tycon_record_as_variant trec  in
                         (match uu____19332 with
                          | (t,fs) ->
                              let uu____19391 =
                                let uu____19394 =
                                  let uu____19395 =
                                    let uu____19404 =
                                      let uu____19407 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____19407  in
                                    (uu____19404, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____19395
                                   in
                                uu____19394 :: quals1  in
                              collect_tcs uu____19391 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____19494 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____19494 with
                          | (env2,uu____19554,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____19703 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____19703 with
                          | (env2,uu____19763,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____19888 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____19935 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____19935 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___259_20440  ->
                             match uu___259_20440 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____20505,uu____20506);
                                    FStar_Syntax_Syntax.sigrng = uu____20507;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____20508;
                                    FStar_Syntax_Syntax.sigmeta = uu____20509;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____20510;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____20573 =
                                     typars_of_binders env1 binders  in
                                   match uu____20573 with
                                   | (env2,tpars1) ->
                                       let uu____20600 =
                                         push_tparams env2 tpars1  in
                                       (match uu____20600 with
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
                                 let uu____20629 =
                                   let uu____20648 =
                                     mk_typ_abbrev id1 uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____20648)
                                    in
                                 [uu____20629]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____20708);
                                    FStar_Syntax_Syntax.sigrng = uu____20709;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____20711;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____20712;_},constrs,tconstr,quals1)
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
                                 let uu____20810 = push_tparams env1 tpars
                                    in
                                 (match uu____20810 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____20877  ->
                                             match uu____20877 with
                                             | (x,uu____20889) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____20893 =
                                        let uu____20920 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____21028  ->
                                                  match uu____21028 with
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
                                                        let uu____21082 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____21082
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
                                                                uu___258_21093
                                                                 ->
                                                                match uu___258_21093
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____21105
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____21113 =
                                                        let uu____21132 =
                                                          let uu____21133 =
                                                            let uu____21134 =
                                                              let uu____21149
                                                                =
                                                                let uu____21150
                                                                  =
                                                                  let uu____21153
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____21153
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____21150
                                                                 in
                                                              (name, univs1,
                                                                uu____21149,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____21134
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____21133;
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
                                                          uu____21132)
                                                         in
                                                      (name, uu____21113)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____20920
                                         in
                                      (match uu____20893 with
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
                             | uu____21368 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____21494  ->
                             match uu____21494 with
                             | (name_doc,uu____21520,uu____21521) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____21593  ->
                             match uu____21593 with
                             | (uu____21612,uu____21613,se) -> se))
                      in
                   let uu____21639 =
                     let uu____21646 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____21646 rng
                      in
                   (match uu____21639 with
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
                               (fun uu____21708  ->
                                  match uu____21708 with
                                  | (uu____21729,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____21776,tps,k,uu____21779,constrs)
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
                                  | uu____21798 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____21815  ->
                                 match uu____21815 with
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
      let uu____21858 =
        FStar_List.fold_left
          (fun uu____21893  ->
             fun b  ->
               match uu____21893 with
               | (env1,binders1) ->
                   let uu____21937 = desugar_binder env1 b  in
                   (match uu____21937 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____21960 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____21960 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____22013 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____21858 with
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
          let uu____22114 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___260_22119  ->
                    match uu___260_22119 with
                    | FStar_Syntax_Syntax.Reflectable uu____22120 -> true
                    | uu____22121 -> false))
             in
          if uu____22114
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____22124 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____22124
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
      let uu____22156 = FStar_Syntax_Util.head_and_args at1  in
      match uu____22156 with
      | (hd1,args) ->
          let uu____22207 =
            let uu____22222 =
              let uu____22223 = FStar_Syntax_Subst.compress hd1  in
              uu____22223.FStar_Syntax_Syntax.n  in
            (uu____22222, args)  in
          (match uu____22207 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(a1,uu____22246)::[]) when
               (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr)
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.fail_lax_attr)
               ->
               let uu____22281 =
                 let uu____22286 =
                   let uu____22295 =
                     FStar_Syntax_Embeddings.e_list
                       FStar_Syntax_Embeddings.e_int
                      in
                   FStar_Syntax_Embeddings.unembed uu____22295 a1  in
                 uu____22286 true FStar_Syntax_Embeddings.id_norm_cb  in
               (match uu____22281 with
                | FStar_Pervasives_Native.Some es when
                    (FStar_List.length es) > (Prims.parse_int "0") ->
                    let b =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.fail_lax_attr
                       in
                    let uu____22320 =
                      let uu____22327 =
                        FStar_List.map FStar_BigInt.to_int_fs es  in
                      (uu____22327, b)  in
                    FStar_Pervasives_Native.Some uu____22320
                | uu____22338 ->
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
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____22380) when
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
           | uu____22409 -> FStar_Pervasives_Native.None)
  
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
                  let uu____22578 = desugar_binders monad_env eff_binders  in
                  match uu____22578 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let for_free =
                        let uu____22617 =
                          let uu____22618 =
                            let uu____22627 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____22627  in
                          FStar_List.length uu____22618  in
                        uu____22617 = (Prims.parse_int "1")  in
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
                            (uu____22673,uu____22674,(FStar_Parser_AST.TyconAbbrev
                                                      (name,uu____22676,uu____22677,uu____22678),uu____22679)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____22712 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____22713 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____22725 = name_of_eff_decl decl  in
                             FStar_List.mem uu____22725 mandatory_members)
                          eff_decls
                         in
                      (match uu____22713 with
                       | (mandatory_members_decls,actions) ->
                           let uu____22742 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____22771  ->
                                     fun decl  ->
                                       match uu____22771 with
                                       | (env2,out) ->
                                           let uu____22791 =
                                             desugar_decl env2 decl  in
                                           (match uu____22791 with
                                            | (env3,ses) ->
                                                let uu____22804 =
                                                  let uu____22807 =
                                                    FStar_List.hd ses  in
                                                  uu____22807 :: out  in
                                                (env3, uu____22804)))
                                  (env1, []))
                              in
                           (match uu____22742 with
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
                                              (uu____22876,uu____22877,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____22880,
                                                 {
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.Construct
                                                     (uu____22881,(def,uu____22883)::
                                                      (cps_type,uu____22885)::[]);
                                                   FStar_Parser_AST.range =
                                                     uu____22886;
                                                   FStar_Parser_AST.level =
                                                     uu____22887;_}),doc1)::[])
                                              when Prims.op_Negation for_free
                                              ->
                                              let uu____22939 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____22939 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____22977 =
                                                     let uu____22978 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____22979 =
                                                       let uu____22980 =
                                                         desugar_term env3
                                                           def
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____22980
                                                        in
                                                     let uu____22987 =
                                                       let uu____22988 =
                                                         desugar_typ env3
                                                           cps_type
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____22988
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____22978;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____22979;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____22987
                                                     }  in
                                                   (uu____22977, doc1))
                                          | FStar_Parser_AST.Tycon
                                              (uu____22997,uu____22998,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____23001,defn),doc1)::[])
                                              when for_free ->
                                              let uu____23036 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____23036 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____23074 =
                                                     let uu____23075 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____23076 =
                                                       let uu____23077 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____23077
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____23075;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____23076;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____23074, doc1))
                                          | uu____23086 ->
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
                                    let uu____23118 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____23118
                                     in
                                  let uu____23119 =
                                    let uu____23120 =
                                      FStar_Syntax_DsEnv.fail_or env2
                                        (FStar_Syntax_DsEnv.try_lookup_definition
                                           env2) l
                                       in
                                    FStar_All.pipe_left
                                      (FStar_Syntax_Subst.close binders1)
                                      uu____23120
                                     in
                                  ([], uu____23119)  in
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
                                      let uu____23137 =
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      ([], uu____23137)  in
                                    let uu____23144 =
                                      let uu____23145 =
                                        let uu____23146 =
                                          let uu____23147 = lookup1 "repr"
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____23147
                                           in
                                        let uu____23156 = lookup1 "return"
                                           in
                                        let uu____23157 = lookup1 "bind"  in
                                        let uu____23158 =
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
                                            uu____23146;
                                          FStar_Syntax_Syntax.return_repr =
                                            uu____23156;
                                          FStar_Syntax_Syntax.bind_repr =
                                            uu____23157;
                                          FStar_Syntax_Syntax.actions =
                                            actions1;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            uu____23158
                                        }  in
                                      FStar_Syntax_Syntax.Sig_new_effect_for_free
                                        uu____23145
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____23144;
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
                                         (fun uu___261_23164  ->
                                            match uu___261_23164 with
                                            | FStar_Syntax_Syntax.Reifiable 
                                                -> true
                                            | FStar_Syntax_Syntax.Reflectable
                                                uu____23165 -> true
                                            | uu____23166 -> false)
                                         qualifiers
                                        in
                                     let un_ts =
                                       ([], FStar_Syntax_Syntax.tun)  in
                                     let uu____23180 =
                                       let uu____23181 =
                                         let uu____23182 =
                                           lookup1 "return_wp"  in
                                         let uu____23183 = lookup1 "bind_wp"
                                            in
                                         let uu____23184 =
                                           lookup1 "if_then_else"  in
                                         let uu____23185 = lookup1 "ite_wp"
                                            in
                                         let uu____23186 = lookup1 "stronger"
                                            in
                                         let uu____23187 = lookup1 "close_wp"
                                            in
                                         let uu____23188 = lookup1 "assert_p"
                                            in
                                         let uu____23189 = lookup1 "assume_p"
                                            in
                                         let uu____23190 = lookup1 "null_wp"
                                            in
                                         let uu____23191 = lookup1 "trivial"
                                            in
                                         let uu____23192 =
                                           if rr
                                           then
                                             let uu____23193 = lookup1 "repr"
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.snd
                                               uu____23193
                                           else FStar_Syntax_Syntax.tun  in
                                         let uu____23209 =
                                           if rr
                                           then lookup1 "return"
                                           else un_ts  in
                                         let uu____23211 =
                                           if rr
                                           then lookup1 "bind"
                                           else un_ts  in
                                         let uu____23213 =
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
                                             uu____23182;
                                           FStar_Syntax_Syntax.bind_wp =
                                             uu____23183;
                                           FStar_Syntax_Syntax.if_then_else =
                                             uu____23184;
                                           FStar_Syntax_Syntax.ite_wp =
                                             uu____23185;
                                           FStar_Syntax_Syntax.stronger =
                                             uu____23186;
                                           FStar_Syntax_Syntax.close_wp =
                                             uu____23187;
                                           FStar_Syntax_Syntax.assert_p =
                                             uu____23188;
                                           FStar_Syntax_Syntax.assume_p =
                                             uu____23189;
                                           FStar_Syntax_Syntax.null_wp =
                                             uu____23190;
                                           FStar_Syntax_Syntax.trivial =
                                             uu____23191;
                                           FStar_Syntax_Syntax.repr =
                                             uu____23192;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____23209;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____23211;
                                           FStar_Syntax_Syntax.actions =
                                             actions1;
                                           FStar_Syntax_Syntax.eff_attrs =
                                             uu____23213
                                         }  in
                                       FStar_Syntax_Syntax.Sig_new_effect
                                         uu____23181
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         uu____23180;
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
                                          fun uu____23239  ->
                                            match uu____23239 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____23253 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____23253
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
                let uu____23277 = desugar_binders env1 eff_binders  in
                match uu____23277 with
                | (env2,binders) ->
                    let uu____23314 =
                      let uu____23325 = head_and_args defn  in
                      match uu____23325 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____23362 ->
                                let uu____23363 =
                                  let uu____23368 =
                                    let uu____23369 =
                                      let uu____23370 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.strcat uu____23370 " not found"
                                       in
                                    Prims.strcat "Effect " uu____23369  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____23368)
                                   in
                                FStar_Errors.raise_error uu____23363
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____23372 =
                            match FStar_List.rev args with
                            | (last_arg,uu____23402)::args_rev ->
                                let uu____23414 =
                                  let uu____23415 = unparen last_arg  in
                                  uu____23415.FStar_Parser_AST.tm  in
                                (match uu____23414 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____23443 -> ([], args))
                            | uu____23452 -> ([], args)  in
                          (match uu____23372 with
                           | (cattributes,args1) ->
                               let uu____23495 = desugar_args env2 args1  in
                               let uu____23496 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____23495, uu____23496))
                       in
                    (match uu____23314 with
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
                          (let uu____23532 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____23532 with
                           | (ed_binders,uu____23546,ed_binders_opening) ->
                               let sub1 uu____23559 =
                                 match uu____23559 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____23573 =
                                         FStar_Syntax_Subst.shift_subst
                                           (FStar_List.length us)
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____23573 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____23577 =
                                       let uu____23578 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____23578)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____23577
                                  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____23587 =
                                   let uu____23588 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____23588
                                    in
                                 let uu____23603 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____23604 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____23605 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____23606 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____23607 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____23608 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____23609 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____23610 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____23611 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____23612 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____23613 =
                                   let uu____23614 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____23614
                                    in
                                 let uu____23629 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____23630 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____23631 =
                                   FStar_List.map
                                     (fun action  ->
                                        let uu____23639 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____23640 =
                                          let uu____23641 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____23641
                                           in
                                        let uu____23656 =
                                          let uu____23657 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____23657
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____23639;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____23640;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____23656
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
                                     uu____23587;
                                   FStar_Syntax_Syntax.ret_wp = uu____23603;
                                   FStar_Syntax_Syntax.bind_wp = uu____23604;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____23605;
                                   FStar_Syntax_Syntax.ite_wp = uu____23606;
                                   FStar_Syntax_Syntax.stronger = uu____23607;
                                   FStar_Syntax_Syntax.close_wp = uu____23608;
                                   FStar_Syntax_Syntax.assert_p = uu____23609;
                                   FStar_Syntax_Syntax.assume_p = uu____23610;
                                   FStar_Syntax_Syntax.null_wp = uu____23611;
                                   FStar_Syntax_Syntax.trivial = uu____23612;
                                   FStar_Syntax_Syntax.repr = uu____23613;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____23629;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____23630;
                                   FStar_Syntax_Syntax.actions = uu____23631;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____23674 =
                                     let uu____23675 =
                                       let uu____23684 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____23684
                                        in
                                     FStar_List.length uu____23675  in
                                   uu____23674 = (Prims.parse_int "1")  in
                                 let uu____23715 =
                                   let uu____23718 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____23718 quals  in
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
                                   FStar_Syntax_Syntax.sigquals = uu____23715;
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
                                             let uu____23740 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____23740
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____23742 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____23742
                                 then
                                   let reflect_lid =
                                     let uu____23746 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____23746
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
    let uu____23756 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____23756 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.strcat "  " (Prims.strcat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____23807 ->
              let uu____23808 =
                let uu____23809 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____23809
                 in
              Prims.strcat "\n  " uu____23808
          | uu____23810 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____23823  ->
               match uu____23823 with
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
          let uu____23841 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____23841
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____23843 =
          let uu____23854 = FStar_Syntax_Syntax.as_arg arg  in [uu____23854]
           in
        FStar_Syntax_Util.mk_app fv uu____23843

and (desugar_decl_aux :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      let uu____23885 = desugar_decl_noattrs env d  in
      match uu____23885 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____23903 = mk_comment_attr d  in uu____23903 :: attrs1  in
          let uu____23904 =
            FStar_List.mapi
              (fun i  ->
                 fun sigelt  ->
                   if i = (Prims.parse_int "0")
                   then
                     let uu___296_23910 = sigelt  in
                     {
                       FStar_Syntax_Syntax.sigel =
                         (uu___296_23910.FStar_Syntax_Syntax.sigel);
                       FStar_Syntax_Syntax.sigrng =
                         (uu___296_23910.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___296_23910.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___296_23910.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs = attrs2
                     }
                   else
                     (let uu___297_23912 = sigelt  in
                      let uu____23913 =
                        FStar_List.filter
                          (fun at1  ->
                             let uu____23919 = get_fail_attr false at1  in
                             FStar_Option.isNone uu____23919) attrs2
                         in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___297_23912.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___297_23912.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___297_23912.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___297_23912.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs = uu____23913
                      })) sigelts
             in
          (env1, uu____23904)

and (desugar_decl :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      let uu____23940 = desugar_decl_aux env d  in
      match uu____23940 with
      | (env1,ses) ->
          let uu____23951 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____23951)

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
      | FStar_Parser_AST.Fsdoc uu____23979 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____23987 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____23987, [])
      | FStar_Parser_AST.Tycon (is_effect,typeclass,tcs) ->
          let quals = d.FStar_Parser_AST.quals  in
          let quals1 =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: quals
            else quals  in
          let quals2 =
            if typeclass then FStar_Parser_AST.Noeq :: quals1 else quals1  in
          let tcs1 =
            FStar_List.map
              (fun uu____24032  ->
                 match uu____24032 with | (x,uu____24040) -> x) tcs
             in
          let uu____24045 =
            let uu____24050 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____24050 tcs1  in
          (match uu____24045 with
           | (env1,ses) ->
               let mkclass lid =
                 let uu____24067 =
                   let uu____24068 =
                     let uu____24075 =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun
                        in
                     FStar_Syntax_Syntax.mk_binder uu____24075  in
                   [uu____24068]  in
                 let uu____24088 =
                   let uu____24091 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____24094 =
                     let uu____24105 =
                       let uu____24114 =
                         let uu____24115 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____24115  in
                       FStar_Syntax_Syntax.as_arg uu____24114  in
                     [uu____24105]  in
                   FStar_Syntax_Util.mk_app uu____24091 uu____24094  in
                 FStar_Syntax_Util.abs uu____24067 uu____24088
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____24154,id1))::uu____24156 ->
                       FStar_Pervasives_Native.Some id1
                   | uu____24159::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____24163 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____24163 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id1 ->
                     let id2 = FStar_Syntax_Util.unmangle_field_name id1  in
                     let uu____24170 = FStar_Syntax_DsEnv.qualify env1 id2
                        in
                     [uu____24170]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____24191) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____24201,uu____24202,uu____24203,uu____24204,uu____24205)
                     ->
                     let uu____24214 =
                       let uu____24215 =
                         let uu____24216 =
                           let uu____24223 = mkclass lid  in
                           (meths, uu____24223)  in
                         FStar_Syntax_Syntax.Sig_splice uu____24216  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____24215;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = []
                       }  in
                     [uu____24214]
                 | uu____24226 -> []  in
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
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____24256;
                    FStar_Parser_AST.prange = uu____24257;_},uu____24258)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____24267;
                    FStar_Parser_AST.prange = uu____24268;_},uu____24269)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____24284;
                         FStar_Parser_AST.prange = uu____24285;_},uu____24286);
                    FStar_Parser_AST.prange = uu____24287;_},uu____24288)::[]
                   -> false
               | (p,uu____24316)::[] ->
                   let uu____24325 = is_app_pattern p  in
                   Prims.op_Negation uu____24325
               | uu____24326 -> false)
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
            let uu____24399 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____24399 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____24411 =
                     let uu____24412 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____24412.FStar_Syntax_Syntax.n  in
                   match uu____24411 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____24422) ->
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
                         | uu____24455::uu____24456 ->
                             FStar_List.map
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____24459 ->
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.collect
                                  (fun uu___262_24474  ->
                                     match uu___262_24474 with
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inl uu____24477;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____24478;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____24479;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____24480;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____24481;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____24482;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____24483;_}
                                         -> []
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____24495;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____24496;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____24497;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____24498;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____24499;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____24500;_}
                                         ->
                                         FStar_Syntax_DsEnv.lookup_letbinding_quals
                                           env
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                          in
                       let quals2 =
                         let uu____24514 =
                           FStar_All.pipe_right lets1
                             (FStar_Util.for_some
                                (fun uu____24545  ->
                                   match uu____24545 with
                                   | (uu____24558,(uu____24559,t)) ->
                                       t.FStar_Parser_AST.level =
                                         FStar_Parser_AST.Formula))
                            in
                         if uu____24514
                         then FStar_Syntax_Syntax.Logic :: quals1
                         else quals1  in
                       let lbs1 =
                         let uu____24577 =
                           FStar_All.pipe_right quals2
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract)
                            in
                         if uu____24577
                         then
                           let uu____24580 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu___298_24594 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___299_24596 = fv  in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___299_24596.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___299_24596.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___298_24594.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___298_24594.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___298_24594.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___298_24594.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___298_24594.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___298_24594.FStar_Syntax_Syntax.lbpos)
                                     }))
                              in
                           ((FStar_Pervasives_Native.fst lbs), uu____24580)
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
                   | uu____24623 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____24629 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____24648 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____24629 with
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
                       let uu___300_24684 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___300_24684.FStar_Parser_AST.prange)
                       }
                   | uu____24691 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___301_24698 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___301_24698.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___301_24698.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___301_24698.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____24734 id1 =
                   match uu____24734 with
                   | (env1,ses) ->
                       let main =
                         let uu____24755 =
                           let uu____24756 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____24756  in
                         FStar_Parser_AST.mk_term uu____24755
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
                       let uu____24806 = desugar_decl env1 id_decl  in
                       (match uu____24806 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____24824 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____24824 FStar_Util.set_elements
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
            let uu____24847 = close_fun env t  in
            desugar_term env uu____24847  in
          let quals1 =
            let uu____24851 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____24851
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let se =
            let uu____24857 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____24857;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in
          let env2 =
            FStar_Syntax_DsEnv.push_doc env1 lid d.FStar_Parser_AST.doc  in
          (env2, [se])
      | FStar_Parser_AST.Exception (id1,FStar_Pervasives_Native.None ) ->
          let uu____24865 =
            FStar_Syntax_DsEnv.fail_or env
              (FStar_Syntax_DsEnv.try_lookup_lid env)
              FStar_Parser_Const.exn_lid
             in
          (match uu____24865 with
           | (t,uu____24879) ->
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
            let uu____24909 =
              let uu____24918 = FStar_Syntax_Syntax.null_binder t  in
              [uu____24918]  in
            let uu____24937 =
              let uu____24940 =
                let uu____24941 =
                  FStar_Syntax_DsEnv.fail_or env
                    (FStar_Syntax_DsEnv.try_lookup_lid env)
                    FStar_Parser_Const.exn_lid
                   in
                FStar_Pervasives_Native.fst uu____24941  in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____24940
               in
            FStar_Syntax_Util.arrow uu____24909 uu____24937  in
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
            let uu____25002 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____25002 with
            | FStar_Pervasives_Native.None  ->
                let uu____25005 =
                  let uu____25010 =
                    let uu____25011 =
                      let uu____25012 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.strcat uu____25012 " not found"  in
                    Prims.strcat "Effect name " uu____25011  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____25010)  in
                FStar_Errors.raise_error uu____25005
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____25016 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____25034 =
                  let uu____25037 =
                    let uu____25038 = desugar_term env t  in
                    ([], uu____25038)  in
                  FStar_Pervasives_Native.Some uu____25037  in
                (uu____25034, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____25051 =
                  let uu____25054 =
                    let uu____25055 = desugar_term env wp  in
                    ([], uu____25055)  in
                  FStar_Pervasives_Native.Some uu____25054  in
                let uu____25062 =
                  let uu____25065 =
                    let uu____25066 = desugar_term env t  in
                    ([], uu____25066)  in
                  FStar_Pervasives_Native.Some uu____25065  in
                (uu____25051, uu____25062)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____25078 =
                  let uu____25081 =
                    let uu____25082 = desugar_term env t  in
                    ([], uu____25082)  in
                  FStar_Pervasives_Native.Some uu____25081  in
                (FStar_Pervasives_Native.None, uu____25078)
             in
          (match uu____25016 with
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
            let uu____25116 =
              let uu____25117 =
                let uu____25124 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____25124, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____25117  in
            {
              FStar_Syntax_Syntax.sigel = uu____25116;
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
      let uu____25150 =
        FStar_List.fold_left
          (fun uu____25170  ->
             fun d  ->
               match uu____25170 with
               | (env1,sigelts) ->
                   let uu____25190 = desugar_decl env1 d  in
                   (match uu____25190 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____25150 with
      | (env1,sigelts) ->
          let rec forward acc uu___264_25235 =
            match uu___264_25235 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____25249,FStar_Syntax_Syntax.Sig_let uu____25250) ->
                     let uu____25263 =
                       let uu____25266 =
                         let uu___302_25267 = se2  in
                         let uu____25268 =
                           let uu____25271 =
                             FStar_List.filter
                               (fun uu___263_25285  ->
                                  match uu___263_25285 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____25289;
                                           FStar_Syntax_Syntax.vars =
                                             uu____25290;_},uu____25291);
                                      FStar_Syntax_Syntax.pos = uu____25292;
                                      FStar_Syntax_Syntax.vars = uu____25293;_}
                                      when
                                      let uu____25320 =
                                        let uu____25321 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____25321
                                         in
                                      uu____25320 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____25322 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____25271
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___302_25267.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___302_25267.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___302_25267.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___302_25267.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____25268
                         }  in
                       uu____25266 :: se1 :: acc  in
                     forward uu____25263 sigelts1
                 | uu____25327 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____25335 = forward [] sigelts  in (env1, uu____25335)
  
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
          | (FStar_Pervasives_Native.None ,uu____25396) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____25400;
               FStar_Syntax_Syntax.exports = uu____25401;
               FStar_Syntax_Syntax.is_interface = uu____25402;_},FStar_Parser_AST.Module
             (current_lid,uu____25404)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____25412) ->
              let uu____25415 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____25415
           in
        let uu____25420 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____25456 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____25456, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____25473 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____25473, mname, decls, false)
           in
        match uu____25420 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____25503 = desugar_decls env2 decls  in
            (match uu____25503 with
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
          let uu____25565 =
            (FStar_Options.interactive ()) &&
              (let uu____25567 =
                 let uu____25568 =
                   let uu____25569 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____25569  in
                 FStar_Util.get_file_extension uu____25568  in
               FStar_List.mem uu____25567 ["fsti"; "fsi"])
             in
          if uu____25565 then as_interface m else m  in
        let uu____25573 = desugar_modul_common curmod env m1  in
        match uu____25573 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____25591 = FStar_Syntax_DsEnv.pop ()  in
              (uu____25591, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul ->
      (env_t,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun m  ->
      let uu____25611 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____25611 with
      | (env1,modul,pop_when_done) ->
          let uu____25625 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____25625 with
           | (env2,modul1) ->
               ((let uu____25637 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____25637
                 then
                   let uu____25638 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____25638
                 else ());
                (let uu____25640 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____25640, modul1))))
  
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
        (fun uu____25687  ->
           let uu____25688 = desugar_modul env modul  in
           match uu____25688 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____25729  ->
           let uu____25730 = desugar_decls env decls  in
           match uu____25730 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____25784  ->
             let uu____25785 = desugar_partial_modul modul env a_modul  in
             match uu____25785 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____25883 ->
                  let t =
                    let uu____25893 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____25893  in
                  let uu____25906 =
                    let uu____25907 = FStar_Syntax_Subst.compress t  in
                    uu____25907.FStar_Syntax_Syntax.n  in
                  (match uu____25906 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____25919,uu____25920)
                       -> bs1
                   | uu____25945 -> failwith "Impossible")
               in
            let uu____25954 =
              let uu____25961 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____25961
                FStar_Syntax_Syntax.t_unit
               in
            match uu____25954 with
            | (binders,uu____25963,binders_opening) ->
                let erase_term t =
                  let uu____25971 =
                    let uu____25972 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____25972  in
                  FStar_Syntax_Subst.close binders uu____25971  in
                let erase_tscheme uu____25990 =
                  match uu____25990 with
                  | (us,t) ->
                      let t1 =
                        let uu____26010 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____26010 t  in
                      let uu____26013 =
                        let uu____26014 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____26014  in
                      ([], uu____26013)
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
                    | uu____26037 ->
                        let bs =
                          let uu____26047 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____26047  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____26087 =
                          let uu____26088 =
                            let uu____26091 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____26091  in
                          uu____26088.FStar_Syntax_Syntax.n  in
                        (match uu____26087 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____26093,uu____26094) -> bs1
                         | uu____26119 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____26126 =
                      let uu____26127 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____26127  in
                    FStar_Syntax_Subst.close binders uu____26126  in
                  let uu___303_26128 = action  in
                  let uu____26129 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____26130 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___303_26128.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___303_26128.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____26129;
                    FStar_Syntax_Syntax.action_typ = uu____26130
                  }  in
                let uu___304_26131 = ed  in
                let uu____26132 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____26133 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____26134 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____26135 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____26136 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____26137 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____26138 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____26139 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____26140 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____26141 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____26142 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____26143 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____26144 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____26145 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____26146 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____26147 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___304_26131.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___304_26131.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____26132;
                  FStar_Syntax_Syntax.signature = uu____26133;
                  FStar_Syntax_Syntax.ret_wp = uu____26134;
                  FStar_Syntax_Syntax.bind_wp = uu____26135;
                  FStar_Syntax_Syntax.if_then_else = uu____26136;
                  FStar_Syntax_Syntax.ite_wp = uu____26137;
                  FStar_Syntax_Syntax.stronger = uu____26138;
                  FStar_Syntax_Syntax.close_wp = uu____26139;
                  FStar_Syntax_Syntax.assert_p = uu____26140;
                  FStar_Syntax_Syntax.assume_p = uu____26141;
                  FStar_Syntax_Syntax.null_wp = uu____26142;
                  FStar_Syntax_Syntax.trivial = uu____26143;
                  FStar_Syntax_Syntax.repr = uu____26144;
                  FStar_Syntax_Syntax.return_repr = uu____26145;
                  FStar_Syntax_Syntax.bind_repr = uu____26146;
                  FStar_Syntax_Syntax.actions = uu____26147;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___304_26131.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___305_26163 = se  in
                  let uu____26164 =
                    let uu____26165 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____26165  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____26164;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___305_26163.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___305_26163.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___305_26163.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___305_26163.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___306_26169 = se  in
                  let uu____26170 =
                    let uu____26171 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____26171
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____26170;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___306_26169.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___306_26169.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___306_26169.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___306_26169.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____26173 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____26174 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____26174 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____26186 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____26186
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____26188 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____26188)
  