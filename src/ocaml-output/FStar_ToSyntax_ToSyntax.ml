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
      fun uu___232_237  ->
        match uu___232_237 with
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
  fun uu___233_246  ->
    match uu___233_246 with
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
  fun uu___234_260  ->
    match uu___234_260 with
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
    | FStar_Parser_AST.PatWild  -> true
    | FStar_Parser_AST.PatTvar (uu____1303,uu____1304) -> true
    | FStar_Parser_AST.PatVar (uu____1309,uu____1310) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____1316) -> is_var_pattern p1
    | uu____1329 -> false
  
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____1336) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____1349;
           FStar_Parser_AST.prange = uu____1350;_},uu____1351)
        -> true
    | uu____1362 -> false
  
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
    | uu____1376 -> p
  
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
            let uu____1446 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____1446 with
             | (name,args,uu____1489) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1539);
               FStar_Parser_AST.prange = uu____1540;_},args)
            when is_top_level1 ->
            let uu____1550 =
              let uu____1555 = FStar_Syntax_DsEnv.qualify env id1  in
              FStar_Util.Inr uu____1555  in
            (uu____1550, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1577);
               FStar_Parser_AST.prange = uu____1578;_},args)
            -> ((FStar_Util.Inl id1), args, FStar_Pervasives_Native.None)
        | uu____1608 -> failwith "Not an app pattern"
  
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
      | FStar_Parser_AST.PatConst uu____1658 -> acc
      | FStar_Parser_AST.PatVar
          (uu____1659,FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit
           ))
          -> acc
      | FStar_Parser_AST.PatName uu____1662 -> acc
      | FStar_Parser_AST.PatTvar uu____1663 -> acc
      | FStar_Parser_AST.PatOp uu____1670 -> acc
      | FStar_Parser_AST.PatApp (phead,pats) ->
          gather_pattern_bound_vars_from_list (phead :: pats)
      | FStar_Parser_AST.PatVar (x,uu____1678) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatTuple (pats,uu____1687) ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu____1702 =
            FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
          gather_pattern_bound_vars_from_list uu____1702
      | FStar_Parser_AST.PatAscribed (pat,uu____1710) ->
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
    match projectee with | LocalBinder _0 -> true | uu____1772 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____1808 -> false
  
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
  fun uu___235_1854  ->
    match uu___235_1854 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____1861 -> failwith "Impossible"
  
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
  fun uu____1894  ->
    match uu____1894 with
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
      let uu____1974 =
        let uu____1991 =
          let uu____1994 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____1994  in
        let uu____1995 =
          let uu____2006 =
            let uu____2015 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2015)  in
          [uu____2006]  in
        (uu____1991, uu____1995)  in
      FStar_Syntax_Syntax.Tm_app uu____1974  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____2062 =
        let uu____2079 =
          let uu____2082 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____2082  in
        let uu____2083 =
          let uu____2094 =
            let uu____2103 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2103)  in
          [uu____2094]  in
        (uu____2079, uu____2083)  in
      FStar_Syntax_Syntax.Tm_app uu____2062  in
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
          let uu____2164 =
            let uu____2181 =
              let uu____2184 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____2184  in
            let uu____2185 =
              let uu____2196 =
                let uu____2205 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____2205)  in
              let uu____2212 =
                let uu____2223 =
                  let uu____2232 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____2232)  in
                [uu____2223]  in
              uu____2196 :: uu____2212  in
            (uu____2181, uu____2185)  in
          FStar_Syntax_Syntax.Tm_app uu____2164  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let (generalize_annotated_univs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun s  ->
    let bs_univnames bs =
      let uu____2290 =
        let uu____2305 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____2324  ->
               match uu____2324 with
               | ({ FStar_Syntax_Syntax.ppname = uu____2335;
                    FStar_Syntax_Syntax.index = uu____2336;
                    FStar_Syntax_Syntax.sort = t;_},uu____2338)
                   ->
                   let uu____2345 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____2345) uu____2305
         in
      FStar_All.pipe_right bs uu____2290  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____2361 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____2378 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____2404 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____2425,uu____2426,bs,t,uu____2429,uu____2430)
                            ->
                            let uu____2439 = bs_univnames bs  in
                            let uu____2442 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____2439 uu____2442
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____2445,uu____2446,t,uu____2448,uu____2449,uu____2450)
                            -> FStar_Syntax_Free.univnames t
                        | uu____2455 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____2404 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___261_2463 = s  in
        let uu____2464 =
          let uu____2465 =
            let uu____2474 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____2492,bs,t,lids1,lids2) ->
                          let uu___262_2505 = se  in
                          let uu____2506 =
                            let uu____2507 =
                              let uu____2524 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____2525 =
                                let uu____2526 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____2526 t  in
                              (lid, uvs, uu____2524, uu____2525, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____2507
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____2506;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___262_2505.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___262_2505.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___262_2505.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___262_2505.FStar_Syntax_Syntax.sigattrs)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____2540,t,tlid,n1,lids1) ->
                          let uu___263_2549 = se  in
                          let uu____2550 =
                            let uu____2551 =
                              let uu____2566 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____2566, tlid, n1, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____2551  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____2550;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___263_2549.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___263_2549.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___263_2549.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___263_2549.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____2569 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____2474, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____2465  in
        {
          FStar_Syntax_Syntax.sigel = uu____2464;
          FStar_Syntax_Syntax.sigrng =
            (uu___261_2463.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___261_2463.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___261_2463.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___261_2463.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2575,t) ->
        let uvs =
          let uu____2578 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____2578 FStar_Util.set_elements  in
        let uu___264_2583 = s  in
        let uu____2584 =
          let uu____2585 =
            let uu____2592 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____2592)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____2585  in
        {
          FStar_Syntax_Syntax.sigel = uu____2584;
          FStar_Syntax_Syntax.sigrng =
            (uu___264_2583.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___264_2583.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___264_2583.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___264_2583.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____2614 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____2617 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____2624) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____2657,(FStar_Util.Inl t,uu____2659),uu____2660)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____2707,(FStar_Util.Inr c,uu____2709),uu____2710)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____2757 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____2758,(FStar_Util.Inl t,uu____2760),uu____2761) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____2808,(FStar_Util.Inr c,uu____2810),uu____2811) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____2858 -> empty_set  in
          FStar_Util.set_union uu____2614 uu____2617  in
        let all_lb_univs =
          let uu____2862 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____2878 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____2878) empty_set)
             in
          FStar_All.pipe_right uu____2862 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___265_2888 = s  in
        let uu____2889 =
          let uu____2890 =
            let uu____2897 =
              let uu____2898 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___266_2910 = lb  in
                        let uu____2911 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____2914 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___266_2910.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____2911;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___266_2910.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____2914;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___266_2910.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___266_2910.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____2898)  in
            (uu____2897, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____2890  in
        {
          FStar_Syntax_Syntax.sigel = uu____2889;
          FStar_Syntax_Syntax.sigrng =
            (uu___265_2888.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___265_2888.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___265_2888.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___265_2888.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____2922,fml) ->
        let uvs =
          let uu____2925 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____2925 FStar_Util.set_elements  in
        let uu___267_2930 = s  in
        let uu____2931 =
          let uu____2932 =
            let uu____2939 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____2939)  in
          FStar_Syntax_Syntax.Sig_assume uu____2932  in
        {
          FStar_Syntax_Syntax.sigel = uu____2931;
          FStar_Syntax_Syntax.sigrng =
            (uu___267_2930.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___267_2930.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___267_2930.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___267_2930.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____2941,bs,c,flags1) ->
        let uvs =
          let uu____2950 =
            let uu____2953 = bs_univnames bs  in
            let uu____2956 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____2953 uu____2956  in
          FStar_All.pipe_right uu____2950 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___268_2964 = s  in
        let uu____2965 =
          let uu____2966 =
            let uu____2979 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____2980 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____2979, uu____2980, flags1)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____2966  in
        {
          FStar_Syntax_Syntax.sigel = uu____2965;
          FStar_Syntax_Syntax.sigrng =
            (uu___268_2964.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___268_2964.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___268_2964.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___268_2964.FStar_Syntax_Syntax.sigattrs)
        }
    | uu____2983 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___236_2988  ->
    match uu___236_2988 with
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
    | uu____2989 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____3001 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____3001)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____3020 =
      let uu____3021 = unparen t  in uu____3021.FStar_Parser_AST.tm  in
    match uu____3020 with
    | FStar_Parser_AST.Wild  ->
        let uu____3026 =
          let uu____3027 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____3027  in
        FStar_Util.Inr uu____3026
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____3038)) ->
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
             let uu____3103 = sum_to_universe u n1  in
             FStar_Util.Inr uu____3103
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____3114 = sum_to_universe u n1  in
             FStar_Util.Inr uu____3114
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____3125 =
               let uu____3130 =
                 let uu____3131 = FStar_Parser_AST.term_to_string t  in
                 Prims.strcat
                   "This universe might contain a sum of two universe variables "
                   uu____3131
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____3130)
                in
             FStar_Errors.raise_error uu____3125 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____3136 ->
        let rec aux t1 univargs =
          let uu____3170 =
            let uu____3171 = unparen t1  in uu____3171.FStar_Parser_AST.tm
             in
          match uu____3170 with
          | FStar_Parser_AST.App (t2,targ,uu____3178) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___237_3201  ->
                     match uu___237_3201 with
                     | FStar_Util.Inr uu____3206 -> true
                     | uu____3207 -> false) univargs
              then
                let uu____3212 =
                  let uu____3213 =
                    FStar_List.map
                      (fun uu___238_3222  ->
                         match uu___238_3222 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____3213  in
                FStar_Util.Inr uu____3212
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___239_3239  ->
                        match uu___239_3239 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____3245 -> failwith "impossible")
                     univargs
                    in
                 let uu____3246 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____3246)
          | uu____3252 ->
              let uu____3253 =
                let uu____3258 =
                  let uu____3259 =
                    let uu____3260 = FStar_Parser_AST.term_to_string t1  in
                    Prims.strcat uu____3260 " in universe context"  in
                  Prims.strcat "Unexpected term " uu____3259  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3258)  in
              FStar_Errors.raise_error uu____3253 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____3269 ->
        let uu____3270 =
          let uu____3275 =
            let uu____3276 =
              let uu____3277 = FStar_Parser_AST.term_to_string t  in
              Prims.strcat uu____3277 " in universe context"  in
            Prims.strcat "Unexpected term " uu____3276  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3275)  in
        FStar_Errors.raise_error uu____3270 t.FStar_Parser_AST.range
  
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
                   FStar_Syntax_Syntax.antiquotes = uu____3307;_});
            FStar_Syntax_Syntax.pos = uu____3308;
            FStar_Syntax_Syntax.vars = uu____3309;_})::uu____3310
        ->
        let uu____3341 =
          let uu____3346 =
            let uu____3347 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____3347
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____3346)  in
        FStar_Errors.raise_error uu____3341 e.FStar_Syntax_Syntax.pos
    | (bv,e)::uu____3350 ->
        let uu____3369 =
          let uu____3374 =
            let uu____3375 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____3375
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____3374)  in
        FStar_Errors.raise_error uu____3369 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'Auu____3384 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident,'Auu____3384) FStar_Pervasives_Native.tuple2
        Prims.list -> FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____3412 = FStar_List.hd fields  in
        match uu____3412 with
        | (f,uu____3422) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____3434 =
                match uu____3434 with
                | (f',uu____3440) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____3442 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____3442
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
              (let uu____3446 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____3446);
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
            | FStar_Syntax_Syntax.Pat_dot_term uu____3835 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_wild uu____3842 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_constant uu____3843 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_var x ->
                FStar_Util.set_add x FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_cons (uu____3845,pats1) ->
                let aux out uu____3883 =
                  match uu____3883 with
                  | (p2,uu____3895) ->
                      let intersection =
                        let uu____3903 = pat_vars p2  in
                        FStar_Util.set_intersect uu____3903 out  in
                      let uu____3906 = FStar_Util.set_is_empty intersection
                         in
                      if uu____3906
                      then
                        let uu____3909 = pat_vars p2  in
                        FStar_Util.set_union out uu____3909
                      else
                        (let duplicate_bv =
                           let uu____3914 =
                             FStar_Util.set_elements intersection  in
                           FStar_List.hd uu____3914  in
                         let uu____3917 =
                           let uu____3922 =
                             FStar_Util.format1
                               "Non-linear patterns are not permitted. %s appears more than once in this pattern."
                               (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                              in
                           (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                             uu____3922)
                            in
                         FStar_Errors.raise_error uu____3917 r)
                   in
                FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
             in
          match pats with
          | [] -> ()
          | p1::[] ->
              let uu____3942 = pat_vars p1  in
              FStar_All.pipe_right uu____3942 (fun a236  -> ())
          | p1::ps ->
              let pvars = pat_vars p1  in
              let aux p2 =
                let uu____3970 =
                  let uu____3971 = pat_vars p2  in
                  FStar_Util.set_eq pvars uu____3971  in
                if uu____3970
                then ()
                else
                  (let nonlinear_vars =
                     let uu____3978 = pat_vars p2  in
                     FStar_Util.set_symmetric_difference pvars uu____3978  in
                   let first_nonlinear_var =
                     let uu____3982 = FStar_Util.set_elements nonlinear_vars
                        in
                     FStar_List.hd uu____3982  in
                   let uu____3985 =
                     let uu____3990 =
                       FStar_Util.format1
                         "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                         (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                        in
                     (FStar_Errors.Fatal_IncoherentPatterns, uu____3990)  in
                   FStar_Errors.raise_error uu____3985 r)
                 in
              FStar_List.iter aux ps
           in
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false ,uu____3994) -> ()
         | (true ,FStar_Parser_AST.PatVar uu____3995) -> ()
         | (true ,uu____4002) ->
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_LetMutableForVariablesOnly,
                 "let-mutable is for variables only")
               p.FStar_Parser_AST.prange);
        (let resolvex l e x =
           let uu____4025 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText))
              in
           match uu____4025 with
           | FStar_Pervasives_Native.Some y -> (l, e, y)
           | uu____4041 ->
               let uu____4044 =
                 if is_mut
                 then FStar_Syntax_DsEnv.push_bv_mutable e x
                 else FStar_Syntax_DsEnv.push_bv e x  in
               (match uu____4044 with | (e1,x1) -> ((x1 :: l), e1, x1))
            in
         let rec aux' top loc env1 p1 =
           let pos q =
             FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange  in
           let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
           let orig = p1  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr uu____4194 -> failwith "impossible"
           | FStar_Parser_AST.PatOp op ->
               let uu____4216 =
                 let uu____4217 =
                   let uu____4218 =
                     let uu____4225 =
                       let uu____4226 =
                         let uu____4231 =
                           FStar_Parser_AST.compile_op (Prims.parse_int "0")
                             op.FStar_Ident.idText op.FStar_Ident.idRange
                            in
                         (uu____4231, (op.FStar_Ident.idRange))  in
                       FStar_Ident.mk_ident uu____4226  in
                     (uu____4225, FStar_Pervasives_Native.None)  in
                   FStar_Parser_AST.PatVar uu____4218  in
                 {
                   FStar_Parser_AST.pat = uu____4217;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 }  in
               aux loc env1 uu____4216
           | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
               ((match tacopt with
                 | FStar_Pervasives_Native.None  -> ()
                 | FStar_Pervasives_Native.Some uu____4248 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                         "Type ascriptions within patterns are cannot be associated with a tactic")
                       orig.FStar_Parser_AST.prange);
                (let uu____4249 = aux loc env1 p2  in
                 match uu____4249 with
                 | (loc1,env',binder,p3,annots,imp) ->
                     let annot_pat_var p4 t1 =
                       match p4.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let uu___269_4334 = p4  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var
                                  (let uu___270_4339 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___270_4339.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___270_4339.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }));
                             FStar_Syntax_Syntax.p =
                               (uu___269_4334.FStar_Syntax_Syntax.p)
                           }
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let uu___271_4341 = p4  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild
                                  (let uu___272_4346 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___272_4346.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___272_4346.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }));
                             FStar_Syntax_Syntax.p =
                               (uu___271_4341.FStar_Syntax_Syntax.p)
                           }
                       | uu____4347 when top -> p4
                       | uu____4348 ->
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                               "Type ascriptions within patterns are only allowed on variables")
                             orig.FStar_Parser_AST.prange
                        in
                     let uu____4351 =
                       match binder with
                       | LetBinder uu____4372 -> failwith "impossible"
                       | LocalBinder (x,aq) ->
                           let t1 =
                             let uu____4396 = close_fun env1 t  in
                             desugar_term env1 uu____4396  in
                           let x1 =
                             let uu___273_4398 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___273_4398.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___273_4398.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }  in
                           ([(x1, t1)], (LocalBinder (x1, aq)))
                        in
                     (match uu____4351 with
                      | (annots',binder1) ->
                          (loc1, env', binder1, p3,
                            (FStar_List.append annots' annots), imp))))
           | FStar_Parser_AST.PatWild  ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____4456 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____4456, [], false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____4469 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____4469, [], false)
           | FStar_Parser_AST.PatTvar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual env1 aq  in
               let uu____4490 = resolvex loc env1 x  in
               (match uu____4490 with
                | (loc1,env2,xbv) ->
                    let uu____4518 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____4518, [],
                      imp))
           | FStar_Parser_AST.PatVar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual env1 aq  in
               let uu____4539 = resolvex loc env1 x  in
               (match uu____4539 with
                | (loc1,env2,xbv) ->
                    let uu____4567 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____4567, [],
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
               let uu____4581 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, []))
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____4581, [], false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____4607;_},args)
               ->
               let uu____4613 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____4672  ->
                        match uu____4672 with
                        | (loc1,env2,annots,args1) ->
                            let uu____4749 = aux loc1 env2 arg  in
                            (match uu____4749 with
                             | (loc2,env3,uu____4794,arg1,ans,imp) ->
                                 (loc2, env3, (FStar_List.append ans annots),
                                   ((arg1, imp) :: args1)))) args
                   (loc, env1, [], [])
                  in
               (match uu____4613 with
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
                    let uu____4916 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                       in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)),
                      uu____4916, annots, false))
           | FStar_Parser_AST.PatApp uu____4931 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                 p1.FStar_Parser_AST.prange
           | FStar_Parser_AST.PatList pats ->
               let uu____4959 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____5010  ->
                        match uu____5010 with
                        | (loc1,env2,annots,pats1) ->
                            let uu____5071 = aux loc1 env2 pat  in
                            (match uu____5071 with
                             | (loc2,env3,uu____5112,pat1,ans,uu____5115) ->
                                 (loc2, env3, (FStar_List.append ans annots),
                                   (pat1 :: pats1)))) pats
                   (loc, env1, [], [])
                  in
               (match uu____4959 with
                | (loc1,env2,annots,pats1) ->
                    let pat =
                      let uu____5209 =
                        let uu____5212 =
                          let uu____5219 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange
                             in
                          pos_r uu____5219  in
                        let uu____5220 =
                          let uu____5221 =
                            let uu____5234 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Parser_Const.nil_lid
                                FStar_Syntax_Syntax.delta_constant
                                (FStar_Pervasives_Native.Some
                                   FStar_Syntax_Syntax.Data_ctor)
                               in
                            (uu____5234, [])  in
                          FStar_Syntax_Syntax.Pat_cons uu____5221  in
                        FStar_All.pipe_left uu____5212 uu____5220  in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p
                                in
                             let uu____5266 =
                               let uu____5267 =
                                 let uu____5280 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.cons_lid
                                     FStar_Syntax_Syntax.delta_constant
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Data_ctor)
                                    in
                                 (uu____5280, [(hd1, false); (tl1, false)])
                                  in
                               FStar_Syntax_Syntax.Pat_cons uu____5267  in
                             FStar_All.pipe_left (pos_r r) uu____5266) pats1
                        uu____5209
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
               let uu____5326 =
                 FStar_List.fold_left
                   (fun uu____5384  ->
                      fun p2  ->
                        match uu____5384 with
                        | (loc1,env2,annots,pats) ->
                            let uu____5462 = aux loc1 env2 p2  in
                            (match uu____5462 with
                             | (loc2,env3,uu____5507,pat,ans,uu____5510) ->
                                 (loc2, env3, (FStar_List.append ans annots),
                                   ((pat, false) :: pats))))
                   (loc, env1, [], []) args
                  in
               (match uu____5326 with
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
                    let uu____5656 =
                      FStar_Syntax_DsEnv.fail_or env2
                        (FStar_Syntax_DsEnv.try_lookup_lid env2) l
                       in
                    (match uu____5656 with
                     | (constr,uu____5684) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____5687 -> failwith "impossible"  in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (FStar_Pervasives_Native.Some
                                (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun
                            in
                         let uu____5689 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                            in
                         (loc1, env2,
                           (LocalBinder (x, FStar_Pervasives_Native.None)),
                           uu____5689, annots, false)))
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
                      (fun uu____5764  ->
                         match uu____5764 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2)))
                  in
               let args =
                 FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                   (FStar_List.map
                      (fun uu____5794  ->
                         match uu____5794 with
                         | (f,uu____5800) ->
                             let uu____5801 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____5827  ->
                                       match uu____5827 with
                                       | (g,uu____5833) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText))
                                in
                             (match uu____5801 with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
                              | FStar_Pervasives_Native.Some (uu____5838,p2)
                                  -> p2)))
                  in
               let app =
                 let uu____5845 =
                   let uu____5846 =
                     let uu____5853 =
                       let uu____5854 =
                         let uu____5855 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                                [record.FStar_Syntax_DsEnv.constrname])
                            in
                         FStar_Parser_AST.PatName uu____5855  in
                       FStar_Parser_AST.mk_pattern uu____5854
                         p1.FStar_Parser_AST.prange
                        in
                     (uu____5853, args)  in
                   FStar_Parser_AST.PatApp uu____5846  in
                 FStar_Parser_AST.mk_pattern uu____5845
                   p1.FStar_Parser_AST.prange
                  in
               let uu____5858 = aux loc env1 app  in
               (match uu____5858 with
                | (env2,e,b,p2,annots,uu____5902) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____5938 =
                            let uu____5939 =
                              let uu____5952 =
                                let uu___274_5953 = fv  in
                                let uu____5954 =
                                  let uu____5957 =
                                    let uu____5958 =
                                      let uu____5965 =
                                        FStar_All.pipe_right
                                          record.FStar_Syntax_DsEnv.fields
                                          (FStar_List.map
                                             FStar_Pervasives_Native.fst)
                                         in
                                      ((record.FStar_Syntax_DsEnv.typename),
                                        uu____5965)
                                       in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____5958
                                     in
                                  FStar_Pervasives_Native.Some uu____5957  in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___274_5953.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___274_5953.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____5954
                                }  in
                              (uu____5952, args1)  in
                            FStar_Syntax_Syntax.Pat_cons uu____5939  in
                          FStar_All.pipe_left pos uu____5938
                      | uu____5990 -> p2  in
                    (env2, e, b, p3, annots, false))
         
         and aux loc env1 p1 = aux' false loc env1 p1
          in
         let aux_maybe_or env1 p1 =
           let loc = []  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____6072 = aux' true loc env1 p2  in
               (match uu____6072 with
                | (loc1,env2,var,p3,ans,uu____6114) ->
                    let uu____6127 =
                      FStar_List.fold_left
                        (fun uu____6176  ->
                           fun p4  ->
                             match uu____6176 with
                             | (loc2,env3,ps1) ->
                                 let uu____6241 = aux' true loc2 env3 p4  in
                                 (match uu____6241 with
                                  | (loc3,env4,uu____6280,p5,ans1,uu____6283)
                                      -> (loc3, env4, ((p5, ans1) :: ps1))))
                        (loc1, env2, []) ps
                       in
                    (match uu____6127 with
                     | (loc2,env3,ps1) ->
                         let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                         (env3, var, pats)))
           | uu____6442 ->
               let uu____6443 = aux' true loc env1 p1  in
               (match uu____6443 with
                | (loc1,env2,vars,pat,ans,b) -> (env2, vars, [(pat, ans)]))
            in
         let uu____6536 = aux_maybe_or env p  in
         match uu____6536 with
         | (env1,b,pats) ->
             ((let uu____6591 =
                 FStar_List.map FStar_Pervasives_Native.fst pats  in
               check_linear_pattern_variables uu____6591
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
            let uu____6642 =
              let uu____6643 =
                let uu____6654 = FStar_Syntax_DsEnv.qualify env x  in
                (uu____6654,
                  (FStar_Syntax_Syntax.tun, FStar_Pervasives_Native.None))
                 in
              LetBinder uu____6643  in
            (env, uu____6642, [])  in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____6682 =
                  let uu____6683 =
                    let uu____6688 =
                      FStar_Parser_AST.compile_op (Prims.parse_int "0")
                        x.FStar_Ident.idText x.FStar_Ident.idRange
                       in
                    (uu____6688, (x.FStar_Ident.idRange))  in
                  FStar_Ident.mk_ident uu____6683  in
                mklet uu____6682
            | FStar_Parser_AST.PatVar (x,uu____6690) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____6696);
                   FStar_Parser_AST.prange = uu____6697;_},(t,tacopt))
                ->
                let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)
                   in
                let uu____6717 =
                  let uu____6718 =
                    let uu____6729 = FStar_Syntax_DsEnv.qualify env x  in
                    let uu____6730 =
                      let uu____6737 = desugar_term env t  in
                      (uu____6737, tacopt1)  in
                    (uu____6729, uu____6730)  in
                  LetBinder uu____6718  in
                (env, uu____6717, [])
            | uu____6748 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_UnexpectedPattern,
                    "Unexpected pattern at the top-level")
                  p.FStar_Parser_AST.prange
          else
            (let uu____6758 = desugar_data_pat env p is_mut  in
             match uu____6758 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1 with
                   | ({
                        FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                          uu____6787;
                        FStar_Syntax_Syntax.p = uu____6788;_},uu____6789)::[]
                       -> []
                   | ({
                        FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                          uu____6802;
                        FStar_Syntax_Syntax.p = uu____6803;_},uu____6804)::[]
                       -> []
                   | uu____6817 -> p1  in
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
  fun uu____6824  ->
    fun env  ->
      fun pat  ->
        let uu____6827 = desugar_data_pat env pat false  in
        match uu____6827 with | (env1,uu____6843,pat1) -> (env1, pat1)

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
      let uu____6862 = desugar_term_aq env e  in
      match uu____6862 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____6879 = desugar_typ_aq env e  in
      match uu____6879 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness,FStar_Const.width)
        FStar_Pervasives_Native.tuple2 ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____6889  ->
        fun range  ->
          match uu____6889 with
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
              ((let uu____6899 =
                  let uu____6900 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____6900  in
                if uu____6899
                then
                  let uu____6901 =
                    let uu____6906 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____6906)  in
                  FStar_Errors.log_issue range uu____6901
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
                  let uu____6911 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____6911 range  in
                let lid1 =
                  let uu____6915 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____6915 with
                  | FStar_Pervasives_Native.Some (intro_term,uu____6925) ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____6934 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____6934 range  in
                           let private_fv =
                             let uu____6936 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____6936 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___275_6937 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___275_6937.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___275_6937.FStar_Syntax_Syntax.vars)
                           }
                       | uu____6938 ->
                           failwith
                             (Prims.strcat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____6945 =
                        let uu____6950 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____6950)
                         in
                      FStar_Errors.raise_error uu____6945 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____6966 =
                  let uu____6973 =
                    let uu____6974 =
                      let uu____6991 =
                        let uu____7002 =
                          let uu____7011 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____7011)  in
                        [uu____7002]  in
                      (lid1, uu____6991)  in
                    FStar_Syntax_Syntax.Tm_app uu____6974  in
                  FStar_Syntax_Syntax.mk uu____6973  in
                uu____6966 FStar_Pervasives_Native.None range))

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
            let uu____7060 =
              let uu____7069 =
                (if resolve
                 then FStar_Syntax_DsEnv.try_lookup_lid_with_attributes
                 else
                   FStar_Syntax_DsEnv.try_lookup_lid_with_attributes_no_resolve)
                  env
                 in
              FStar_Syntax_DsEnv.fail_or env uu____7069 l  in
            match uu____7060 with
            | (tm,mut,attrs) ->
                let warn_if_deprecated attrs1 =
                  FStar_List.iter
                    (fun a  ->
                       match a.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_app
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____7124;
                              FStar_Syntax_Syntax.vars = uu____7125;_},args)
                           when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____7152 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____7152 " is deprecated"  in
                           let msg1 =
                             if
                               (FStar_List.length args) >
                                 (Prims.parse_int "0")
                             then
                               let uu____7162 =
                                 let uu____7163 =
                                   let uu____7166 = FStar_List.hd args  in
                                   FStar_Pervasives_Native.fst uu____7166  in
                                 uu____7163.FStar_Syntax_Syntax.n  in
                               match uu____7162 with
                               | FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_string (s,uu____7188))
                                   when
                                   Prims.op_Negation
                                     ((FStar_Util.trim_string s) = "")
                                   ->
                                   Prims.strcat msg
                                     (Prims.strcat ", use "
                                        (Prims.strcat s " instead"))
                               | uu____7189 -> msg
                             else msg  in
                           let uu____7191 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____7191
                             (FStar_Errors.Warning_DeprecatedDefinition,
                               msg1)
                       | FStar_Syntax_Syntax.Tm_fvar fv when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____7194 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____7194 " is deprecated"  in
                           let uu____7195 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____7195
                             (FStar_Errors.Warning_DeprecatedDefinition, msg)
                       | uu____7196 -> ()) attrs1
                   in
                (warn_if_deprecated attrs;
                 (let tm1 = setpos tm  in
                  if mut
                  then
                    let uu____7201 =
                      let uu____7202 =
                        let uu____7209 = mk_ref_read tm1  in
                        (uu____7209,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Mutable_rval))
                         in
                      FStar_Syntax_Syntax.Tm_meta uu____7202  in
                    FStar_All.pipe_left mk1 uu____7201
                  else tm1))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____7227 =
          let uu____7228 = unparen t  in uu____7228.FStar_Parser_AST.tm  in
        match uu____7227 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____7229; FStar_Ident.ident = uu____7230;
              FStar_Ident.nsstr = uu____7231; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____7234 ->
            let uu____7235 =
              let uu____7240 =
                let uu____7241 = FStar_Parser_AST.term_to_string t  in
                Prims.strcat "Unknown attribute " uu____7241  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____7240)  in
            FStar_Errors.raise_error uu____7235 t.FStar_Parser_AST.range
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
          let uu___276_7324 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___276_7324.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___276_7324.FStar_Syntax_Syntax.vars)
          }  in
        let uu____7327 =
          let uu____7328 = unparen top  in uu____7328.FStar_Parser_AST.tm  in
        match uu____7327 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____7333 ->
            let uu____7340 = desugar_formula env top  in (uu____7340, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____7347 = desugar_formula env t  in (uu____7347, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____7354 = desugar_formula env t  in (uu____7354, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____7378 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____7378, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____7380 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____7380, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____7388 =
                let uu____7389 =
                  let uu____7396 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____7396, args)  in
                FStar_Parser_AST.Op uu____7389  in
              FStar_Parser_AST.mk_term uu____7388 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____7399 =
              let uu____7400 =
                let uu____7401 =
                  let uu____7408 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____7408, [e])  in
                FStar_Parser_AST.Op uu____7401  in
              FStar_Parser_AST.mk_term uu____7400 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____7399
        | FStar_Parser_AST.Op (op_star,uu____7412::uu____7413::[]) when
            (let uu____7418 = FStar_Ident.text_of_id op_star  in
             uu____7418 = "*") &&
              (let uu____7420 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____7420 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____7435;_},t1::t2::[])
                  ->
                  let uu____7440 = flatten1 t1  in
                  FStar_List.append uu____7440 [t2]
              | uu____7443 -> [t]  in
            let uu____7444 =
              let uu____7469 =
                let uu____7492 =
                  let uu____7495 = unparen top  in flatten1 uu____7495  in
                FStar_All.pipe_right uu____7492
                  (FStar_List.map
                     (fun t  ->
                        let uu____7530 = desugar_typ_aq env t  in
                        match uu____7530 with
                        | (t',aq) ->
                            let uu____7541 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____7541, aq)))
                 in
              FStar_All.pipe_right uu____7469 FStar_List.unzip  in
            (match uu____7444 with
             | (targs,aqs) ->
                 let uu____7650 =
                   let uu____7655 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____7655
                    in
                 (match uu____7650 with
                  | (tup,uu____7673) ->
                      let uu____7674 =
                        mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                      (uu____7674, (join_aqs aqs))))
        | FStar_Parser_AST.Tvar a ->
            let uu____7688 =
              let uu____7689 =
                let uu____7692 =
                  FStar_Syntax_DsEnv.fail_or2
                    (FStar_Syntax_DsEnv.try_lookup_id env) a
                   in
                FStar_Pervasives_Native.fst uu____7692  in
              FStar_All.pipe_left setpos uu____7689  in
            (uu____7688, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____7704 =
              let uu____7709 =
                let uu____7710 =
                  let uu____7711 = FStar_Ident.text_of_id u  in
                  Prims.strcat uu____7711 " in non-universe context"  in
                Prims.strcat "Unexpected universe variable " uu____7710  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____7709)  in
            FStar_Errors.raise_error uu____7704 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____7722 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____7722 with
             | FStar_Pervasives_Native.None  ->
                 let uu____7729 =
                   let uu____7734 =
                     let uu____7735 = FStar_Ident.text_of_id s  in
                     Prims.strcat "Unexpected or unbound operator: "
                       uu____7735
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____7734)
                    in
                 FStar_Errors.raise_error uu____7729
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let uu____7745 =
                     let uu____7770 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____7832 = desugar_term_aq env t  in
                               match uu____7832 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____7770 FStar_List.unzip  in
                   (match uu____7745 with
                    | (args1,aqs) ->
                        let uu____7965 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____7965, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____7981)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____7996 =
              let uu___277_7997 = top  in
              let uu____7998 =
                let uu____7999 =
                  let uu____8006 =
                    let uu___278_8007 = top  in
                    let uu____8008 =
                      let uu____8009 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8009  in
                    {
                      FStar_Parser_AST.tm = uu____8008;
                      FStar_Parser_AST.range =
                        (uu___278_8007.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___278_8007.FStar_Parser_AST.level)
                    }  in
                  (uu____8006, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____7999  in
              {
                FStar_Parser_AST.tm = uu____7998;
                FStar_Parser_AST.range =
                  (uu___277_7997.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___277_7997.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____7996
        | FStar_Parser_AST.Construct (n1,(a,uu____8012)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____8028 =
                let uu___279_8029 = top  in
                let uu____8030 =
                  let uu____8031 =
                    let uu____8038 =
                      let uu___280_8039 = top  in
                      let uu____8040 =
                        let uu____8041 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____8041  in
                      {
                        FStar_Parser_AST.tm = uu____8040;
                        FStar_Parser_AST.range =
                          (uu___280_8039.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___280_8039.FStar_Parser_AST.level)
                      }  in
                    (uu____8038, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____8031  in
                {
                  FStar_Parser_AST.tm = uu____8030;
                  FStar_Parser_AST.range =
                    (uu___279_8029.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___279_8029.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____8028))
        | FStar_Parser_AST.Construct (n1,(a,uu____8044)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____8059 =
              let uu___281_8060 = top  in
              let uu____8061 =
                let uu____8062 =
                  let uu____8069 =
                    let uu___282_8070 = top  in
                    let uu____8071 =
                      let uu____8072 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8072  in
                    {
                      FStar_Parser_AST.tm = uu____8071;
                      FStar_Parser_AST.range =
                        (uu___282_8070.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___282_8070.FStar_Parser_AST.level)
                    }  in
                  (uu____8069, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8062  in
              {
                FStar_Parser_AST.tm = uu____8061;
                FStar_Parser_AST.range =
                  (uu___281_8060.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___281_8060.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8059
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8073; FStar_Ident.ident = uu____8074;
              FStar_Ident.nsstr = uu____8075; FStar_Ident.str = "Type0";_}
            ->
            let uu____8078 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____8078, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8079; FStar_Ident.ident = uu____8080;
              FStar_Ident.nsstr = uu____8081; FStar_Ident.str = "Type";_}
            ->
            let uu____8084 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____8084, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____8085; FStar_Ident.ident = uu____8086;
               FStar_Ident.nsstr = uu____8087; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____8105 =
              let uu____8106 =
                let uu____8107 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____8107  in
              mk1 uu____8106  in
            (uu____8105, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8108; FStar_Ident.ident = uu____8109;
              FStar_Ident.nsstr = uu____8110; FStar_Ident.str = "Effect";_}
            ->
            let uu____8113 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____8113, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8114; FStar_Ident.ident = uu____8115;
              FStar_Ident.nsstr = uu____8116; FStar_Ident.str = "True";_}
            ->
            let uu____8119 =
              let uu____8120 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8120
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8119, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8121; FStar_Ident.ident = uu____8122;
              FStar_Ident.nsstr = uu____8123; FStar_Ident.str = "False";_}
            ->
            let uu____8126 =
              let uu____8127 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8127
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8126, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____8130;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____8132 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____8132 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____8141 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_constant_at_level
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None
                     in
                  (uu____8141, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____8142 =
                    let uu____8143 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____8143 txt
                     in
                  failwith uu____8142))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8150 = desugar_name mk1 setpos env true l  in
              (uu____8150, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8153 = desugar_name mk1 setpos env true l  in
              (uu____8153, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____8164 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____8164 with
                | FStar_Pervasives_Native.Some uu____8173 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____8178 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____8178 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____8192 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____8209 =
                    let uu____8210 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____8210  in
                  (uu____8209, noaqs)
              | uu____8211 ->
                  let uu____8218 =
                    let uu____8223 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____8223)  in
                  FStar_Errors.raise_error uu____8218
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____8230 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____8230 with
              | FStar_Pervasives_Native.None  ->
                  let uu____8237 =
                    let uu____8242 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____8242)
                     in
                  FStar_Errors.raise_error uu____8237
                    top.FStar_Parser_AST.range
              | uu____8247 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____8251 = desugar_name mk1 setpos env true lid'  in
                  (uu____8251, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8267 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____8267 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____8286 ->
                       let uu____8293 =
                         FStar_Util.take
                           (fun uu____8317  ->
                              match uu____8317 with
                              | (uu____8322,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____8293 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____8367 =
                              let uu____8392 =
                                FStar_List.map
                                  (fun uu____8435  ->
                                     match uu____8435 with
                                     | (t,imp) ->
                                         let uu____8452 =
                                           desugar_term_aq env t  in
                                         (match uu____8452 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____8392
                                FStar_List.unzip
                               in
                            (match uu____8367 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____8593 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____8593, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____8611 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____8611 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.strcat "Constructor "
                             (Prims.strcat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____8618 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.strcat "Effect "
                             (Prims.strcat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____8629 =
              FStar_List.fold_left
                (fun uu____8674  ->
                   fun b  ->
                     match uu____8674 with
                     | (env1,tparams,typs) ->
                         let uu____8731 = desugar_binder env1 b  in
                         (match uu____8731 with
                          | (xopt,t1) ->
                              let uu____8760 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____8769 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____8769)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____8760 with
                               | (env2,x) ->
                                   let uu____8789 =
                                     let uu____8792 =
                                       let uu____8795 =
                                         let uu____8796 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____8796
                                          in
                                       [uu____8795]  in
                                     FStar_List.append typs uu____8792  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___283_8822 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___283_8822.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___283_8822.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____8789)))) (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      FStar_Pervasives_Native.None])
               in
            (match uu____8629 with
             | (env1,uu____8850,targs) ->
                 let uu____8872 =
                   let uu____8877 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____8877
                    in
                 (match uu____8872 with
                  | (tup,uu____8887) ->
                      let uu____8888 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_app (tup, targs))
                         in
                      (uu____8888, noaqs)))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____8907 = uncurry binders t  in
            (match uu____8907 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___240_8951 =
                   match uu___240_8951 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1  in
                       let uu____8967 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____8967
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____8991 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____8991 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____9024 = aux env [] bs  in (uu____9024, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____9033 = desugar_binder env b  in
            (match uu____9033 with
             | (FStar_Pervasives_Native.None ,uu____9044) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____9058 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____9058 with
                  | ((x,uu____9074),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____9087 =
                        let uu____9088 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____9088  in
                      (uu____9087, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern)
               in
            let uu____9106 =
              FStar_List.fold_left
                (fun uu____9126  ->
                   fun pat  ->
                     match uu____9126 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed
                              (uu____9152,(t,FStar_Pervasives_Native.None ))
                              ->
                              let uu____9162 =
                                let uu____9165 = free_type_vars env1 t  in
                                FStar_List.append uu____9165 ftvs  in
                              (env1, uu____9162)
                          | FStar_Parser_AST.PatAscribed
                              (uu____9170,(t,FStar_Pervasives_Native.Some
                                           tac))
                              ->
                              let uu____9181 =
                                let uu____9184 = free_type_vars env1 t  in
                                let uu____9187 =
                                  let uu____9190 = free_type_vars env1 tac
                                     in
                                  FStar_List.append uu____9190 ftvs  in
                                FStar_List.append uu____9184 uu____9187  in
                              (env1, uu____9181)
                          | uu____9195 -> (env1, ftvs))) (env, []) binders1
               in
            (match uu____9106 with
             | (uu____9204,ftv) ->
                 let ftv1 = sort_ftv ftv  in
                 let binders2 =
                   let uu____9216 =
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
                   FStar_List.append uu____9216 binders1  in
                 let rec aux env1 bs sc_pat_opt uu___241_9273 =
                   match uu___241_9273 with
                   | [] ->
                       let uu____9300 = desugar_term_aq env1 body  in
                       (match uu____9300 with
                        | (body1,aq) ->
                            let body2 =
                              match sc_pat_opt with
                              | FStar_Pervasives_Native.Some (sc,pat) ->
                                  let body2 =
                                    let uu____9337 =
                                      let uu____9338 =
                                        FStar_Syntax_Syntax.pat_bvs pat  in
                                      FStar_All.pipe_right uu____9338
                                        (FStar_List.map
                                           FStar_Syntax_Syntax.mk_binder)
                                       in
                                    FStar_Syntax_Subst.close uu____9337 body1
                                     in
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_match
                                       (sc,
                                         [(pat, FStar_Pervasives_Native.None,
                                            body2)]))
                                    FStar_Pervasives_Native.None
                                    body2.FStar_Syntax_Syntax.pos
                              | FStar_Pervasives_Native.None  -> body1  in
                            let uu____9407 =
                              let uu____9410 =
                                no_annot_abs (FStar_List.rev bs) body2  in
                              setpos uu____9410  in
                            (uu____9407, aq))
                   | p::rest ->
                       let uu____9425 = desugar_binding_pat env1 p  in
                       (match uu____9425 with
                        | (env2,b,pat) ->
                            let pat1 =
                              match pat with
                              | [] -> FStar_Pervasives_Native.None
                              | (p1,uu____9459)::[] ->
                                  FStar_Pervasives_Native.Some p1
                              | uu____9474 ->
                                  FStar_Errors.raise_error
                                    (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                      "Disjunctive patterns are not supported in abstractions")
                                    p.FStar_Parser_AST.prange
                               in
                            let uu____9481 =
                              match b with
                              | LetBinder uu____9522 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat1, sc_pat_opt) with
                                    | (FStar_Pervasives_Native.None
                                       ,uu____9590) -> sc_pat_opt
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.None ) ->
                                        let uu____9644 =
                                          let uu____9653 =
                                            FStar_Syntax_Syntax.bv_to_name x
                                             in
                                          (uu____9653, p1)  in
                                        FStar_Pervasives_Native.Some
                                          uu____9644
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.Some
                                       (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____9715,uu____9716) ->
                                             let tup2 =
                                               let uu____9718 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____9718
                                                 FStar_Syntax_Syntax.delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____9722 =
                                                 let uu____9729 =
                                                   let uu____9730 =
                                                     let uu____9747 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2)
                                                        in
                                                     let uu____9750 =
                                                       let uu____9761 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc
                                                          in
                                                       let uu____9770 =
                                                         let uu____9781 =
                                                           let uu____9790 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x
                                                              in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____9790
                                                            in
                                                         [uu____9781]  in
                                                       uu____9761 ::
                                                         uu____9770
                                                        in
                                                     (uu____9747, uu____9750)
                                                      in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____9730
                                                    in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____9729
                                                  in
                                               uu____9722
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Parser_AST.range
                                                in
                                             let p2 =
                                               let uu____9841 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p1, false)]))
                                                 uu____9841
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____9884,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____9886,pats)) ->
                                             let tupn =
                                               let uu____9929 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____9929
                                                 FStar_Syntax_Syntax.delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____9941 =
                                                 let uu____9942 =
                                                   let uu____9959 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn)
                                                      in
                                                   let uu____9962 =
                                                     let uu____9973 =
                                                       let uu____9984 =
                                                         let uu____9993 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____9993
                                                          in
                                                       [uu____9984]  in
                                                     FStar_List.append args
                                                       uu____9973
                                                      in
                                                   (uu____9959, uu____9962)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____9942
                                                  in
                                               mk1 uu____9941  in
                                             let p2 =
                                               let uu____10041 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p1, false)])))
                                                 uu____10041
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | uu____10082 ->
                                             failwith "Impossible")
                                     in
                                  ((x, aq), sc_pat_opt1)
                               in
                            (match uu____9481 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest))
                    in
                 aux env [] FStar_Pervasives_Native.None binders2)
        | FStar_Parser_AST.App
            (uu____10175,uu____10176,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____10198 =
                let uu____10199 = unparen e  in
                uu____10199.FStar_Parser_AST.tm  in
              match uu____10198 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____10209 ->
                  let uu____10210 = desugar_term_aq env e  in
                  (match uu____10210 with
                   | (head1,aq) ->
                       let uu____10223 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____10223, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____10230 ->
            let rec aux args aqs e =
              let uu____10307 =
                let uu____10308 = unparen e  in
                uu____10308.FStar_Parser_AST.tm  in
              match uu____10307 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____10326 = desugar_term_aq env t  in
                  (match uu____10326 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____10374 ->
                  let uu____10375 = desugar_term_aq env e  in
                  (match uu____10375 with
                   | (head1,aq) ->
                       let uu____10396 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____10396, (join_aqs (aq :: aqs))))
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
            let uu____10456 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____10456
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
            let uu____10508 = desugar_term_aq env t  in
            (match uu____10508 with
             | (tm,s) ->
                 let uu____10519 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____10519, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____10525 =
              let uu____10538 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____10538 then desugar_typ_aq else desugar_term_aq  in
            uu____10525 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____10593 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____10736  ->
                        match uu____10736 with
                        | (attr_opt,(p,def)) ->
                            let uu____10794 = is_app_pattern p  in
                            if uu____10794
                            then
                              let uu____10825 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____10825, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____10907 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____10907, def1)
                               | uu____10952 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____10990);
                                           FStar_Parser_AST.prange =
                                             uu____10991;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____11039 =
                                            let uu____11060 =
                                              let uu____11065 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____11065  in
                                            (uu____11060, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____11039, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____11156) ->
                                        if top_level
                                        then
                                          let uu____11191 =
                                            let uu____11212 =
                                              let uu____11217 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____11217  in
                                            (uu____11212, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____11191, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____11307 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____11338 =
                FStar_List.fold_left
                  (fun uu____11411  ->
                     fun uu____11412  ->
                       match (uu____11411, uu____11412) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____11520,uu____11521),uu____11522))
                           ->
                           let uu____11639 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____11665 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____11665 with
                                  | (env2,xx) ->
                                      let uu____11684 =
                                        let uu____11687 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____11687 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____11684))
                             | FStar_Util.Inr l ->
                                 let uu____11695 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (uu____11695, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____11639 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____11338 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____11843 =
                    match uu____11843 with
                    | (attrs_opt,(uu____11879,args,result_t),def) ->
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
                                let uu____11967 = is_comp_type env1 t  in
                                if uu____11967
                                then
                                  ((let uu____11969 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____11979 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____11979))
                                       in
                                    match uu____11969 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____11982 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____11984 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____11984))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____11982
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
                          | uu____11991 ->
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
                              let uu____12006 =
                                let uu____12007 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____12007
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____12006
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
                  let uu____12084 = desugar_term_aq env' body  in
                  (match uu____12084 with
                   | (body1,aq) ->
                       let uu____12097 =
                         let uu____12100 =
                           let uu____12101 =
                             let uu____12114 =
                               FStar_Syntax_Subst.close rec_bindings1 body1
                                in
                             ((is_rec, lbs1), uu____12114)  in
                           FStar_Syntax_Syntax.Tm_let uu____12101  in
                         FStar_All.pipe_left mk1 uu____12100  in
                       (uu____12097, aq))
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
              let uu____12194 =
                desugar_binding_pat_maybe_top top_level env pat is_mutable
                 in
              match uu____12194 with
              | (env1,binder,pat1) ->
                  let uu____12216 =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let uu____12242 = desugar_term_aq env1 t2  in
                        (match uu____12242 with
                         | (body1,aq) ->
                             let fv =
                               let uu____12256 =
                                 FStar_Syntax_Util.incr_delta_qualifier t12
                                  in
                               FStar_Syntax_Syntax.lid_as_fv l uu____12256
                                 FStar_Pervasives_Native.None
                                in
                             let uu____12257 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t12,
                                            (t12.FStar_Syntax_Syntax.pos))]),
                                      body1))
                                in
                             (uu____12257, aq))
                    | LocalBinder (x,uu____12287) ->
                        let uu____12288 = desugar_term_aq env1 t2  in
                        (match uu____12288 with
                         | (body1,aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | ({
                                    FStar_Syntax_Syntax.v =
                                      FStar_Syntax_Syntax.Pat_wild
                                      uu____12302;
                                    FStar_Syntax_Syntax.p = uu____12303;_},uu____12304)::[]
                                   -> body1
                               | uu____12317 ->
                                   let uu____12320 =
                                     let uu____12327 =
                                       let uu____12328 =
                                         let uu____12351 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         let uu____12354 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1
                                            in
                                         (uu____12351, uu____12354)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____12328
                                        in
                                     FStar_Syntax_Syntax.mk uu____12327  in
                                   uu____12320 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range
                                in
                             let uu____12394 =
                               let uu____12397 =
                                 let uu____12398 =
                                   let uu____12411 =
                                     let uu____12414 =
                                       let uu____12415 =
                                         FStar_Syntax_Syntax.mk_binder x  in
                                       [uu____12415]  in
                                     FStar_Syntax_Subst.close uu____12414
                                       body2
                                      in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t12,
                                           (t12.FStar_Syntax_Syntax.pos))]),
                                     uu____12411)
                                    in
                                 FStar_Syntax_Syntax.Tm_let uu____12398  in
                               FStar_All.pipe_left mk1 uu____12397  in
                             (uu____12394, aq))
                     in
                  (match uu____12216 with
                   | (tm,aq) ->
                       if is_mutable
                       then
                         let uu____12478 =
                           FStar_All.pipe_left mk1
                             (FStar_Syntax_Syntax.Tm_meta
                                (tm,
                                  (FStar_Syntax_Syntax.Meta_desugared
                                     FStar_Syntax_Syntax.Mutable_alloc)))
                            in
                         (uu____12478, aq)
                       else (tm, aq))
               in
            let uu____12490 = FStar_List.hd lbs  in
            (match uu____12490 with
             | (attrs,(head_pat,defn)) ->
                 let uu____12534 = is_rec || (is_app_pattern head_pat)  in
                 if uu____12534
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____12547 =
                let uu____12548 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____12548  in
              mk1 uu____12547  in
            let uu____12549 = desugar_term_aq env t1  in
            (match uu____12549 with
             | (t1',aq1) ->
                 let uu____12560 = desugar_term_aq env t2  in
                 (match uu____12560 with
                  | (t2',aq2) ->
                      let uu____12571 = desugar_term_aq env t3  in
                      (match uu____12571 with
                       | (t3',aq3) ->
                           let uu____12582 =
                             let uu____12583 =
                               let uu____12584 =
                                 let uu____12607 =
                                   let uu____12624 =
                                     let uu____12639 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t2.FStar_Parser_AST.range
                                        in
                                     (uu____12639,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____12652 =
                                     let uu____12669 =
                                       let uu____12684 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t3.FStar_Parser_AST.range
                                          in
                                       (uu____12684,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____12669]  in
                                   uu____12624 :: uu____12652  in
                                 (t1', uu____12607)  in
                               FStar_Syntax_Syntax.Tm_match uu____12584  in
                             mk1 uu____12583  in
                           (uu____12582, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____12875 =
              match uu____12875 with
              | (pat,wopt,b) ->
                  let uu____12897 = desugar_match_pat env pat  in
                  (match uu____12897 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____12928 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____12928
                          in
                       let uu____12933 = desugar_term_aq env1 b  in
                       (match uu____12933 with
                        | (b1,aq) ->
                            let uu____12946 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____12946, aq)))
               in
            let uu____12951 = desugar_term_aq env e  in
            (match uu____12951 with
             | (e1,aq) ->
                 let uu____12962 =
                   let uu____12993 =
                     let uu____13026 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____13026 FStar_List.unzip  in
                   FStar_All.pipe_right uu____12993
                     (fun uu____13244  ->
                        match uu____13244 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____12962 with
                  | (brs,aqs) ->
                      let uu____13463 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____13463, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____13506 = is_comp_type env t  in
              if uu____13506
              then
                let uu____13515 = desugar_comp t.FStar_Parser_AST.range env t
                   in
                FStar_Util.Inr uu____13515
              else
                (let uu____13523 = desugar_term env t  in
                 FStar_Util.Inl uu____13523)
               in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)  in
            let uu____13537 = desugar_term_aq env e  in
            (match uu____13537 with
             | (e1,aq) ->
                 let uu____13548 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_ascribed
                        (e1, (annot, tac_opt1), FStar_Pervasives_Native.None))
                    in
                 (uu____13548, aq))
        | FStar_Parser_AST.Record (uu____13581,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____13622 = FStar_List.hd fields  in
              match uu____13622 with | (f,uu____13634) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____13680  ->
                        match uu____13680 with
                        | (g,uu____13686) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____13692,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____13706 =
                         let uu____13711 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____13711)
                          in
                       FStar_Errors.raise_error uu____13706
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
                  let uu____13719 =
                    let uu____13730 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____13761  ->
                              match uu____13761 with
                              | (f,uu____13771) ->
                                  let uu____13772 =
                                    let uu____13773 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____13773
                                     in
                                  (uu____13772, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____13730)  in
                  FStar_Parser_AST.Construct uu____13719
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____13791 =
                      let uu____13792 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____13792  in
                    FStar_Parser_AST.mk_term uu____13791
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____13794 =
                      let uu____13807 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____13837  ->
                                match uu____13837 with
                                | (f,uu____13847) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____13807)  in
                    FStar_Parser_AST.Record uu____13794  in
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
            let uu____13907 = desugar_term_aq env recterm1  in
            (match uu____13907 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____13923;
                         FStar_Syntax_Syntax.vars = uu____13924;_},args)
                      ->
                      let uu____13950 =
                        let uu____13951 =
                          let uu____13952 =
                            let uu____13969 =
                              let uu____13972 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____13973 =
                                let uu____13976 =
                                  let uu____13977 =
                                    let uu____13984 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____13984)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____13977
                                   in
                                FStar_Pervasives_Native.Some uu____13976  in
                              FStar_Syntax_Syntax.fvar uu____13972
                                FStar_Syntax_Syntax.delta_constant
                                uu____13973
                               in
                            (uu____13969, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____13952  in
                        FStar_All.pipe_left mk1 uu____13951  in
                      (uu____13950, s)
                  | uu____14013 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____14017 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____14017 with
              | (constrname,is_rec) ->
                  let uu____14032 = desugar_term_aq env e  in
                  (match uu____14032 with
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
                       let uu____14050 =
                         let uu____14051 =
                           let uu____14052 =
                             let uu____14069 =
                               let uu____14072 =
                                 let uu____14073 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____14073
                                  in
                               FStar_Syntax_Syntax.fvar uu____14072
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1")) qual
                                in
                             let uu____14074 =
                               let uu____14085 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____14085]  in
                             (uu____14069, uu____14074)  in
                           FStar_Syntax_Syntax.Tm_app uu____14052  in
                         FStar_All.pipe_left mk1 uu____14051  in
                       (uu____14050, s))))
        | FStar_Parser_AST.NamedTyp (uu____14122,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____14131 =
              let uu____14132 = FStar_Syntax_Subst.compress tm  in
              uu____14132.FStar_Syntax_Syntax.n  in
            (match uu____14131 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____14140 =
                   let uu___284_14141 =
                     let uu____14142 =
                       let uu____14143 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____14143  in
                     FStar_Syntax_Util.exp_string uu____14142  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___284_14141.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___284_14141.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____14140, noaqs)
             | uu____14144 ->
                 let uu____14145 =
                   let uu____14150 =
                     let uu____14151 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.strcat "VQuote, expected an fvar, got: "
                       uu____14151
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____14150)  in
                 FStar_Errors.raise_error uu____14145
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____14157 = desugar_term_aq env e  in
            (match uu____14157 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____14169 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____14169, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____14174 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____14175 =
              let uu____14176 =
                let uu____14183 = desugar_term env e  in (bv, uu____14183)
                 in
              [uu____14176]  in
            (uu____14174, uu____14175)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____14208 =
              let uu____14209 =
                let uu____14210 =
                  let uu____14217 = desugar_term env e  in (uu____14217, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____14210  in
              FStar_All.pipe_left mk1 uu____14209  in
            (uu____14208, noaqs)
        | uu____14222 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____14223 = desugar_formula env top  in
            (uu____14223, noaqs)
        | uu____14224 ->
            let uu____14225 =
              let uu____14230 =
                let uu____14231 = FStar_Parser_AST.term_to_string top  in
                Prims.strcat "Unexpected term: " uu____14231  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____14230)  in
            FStar_Errors.raise_error uu____14225 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____14237 -> false
    | uu____14246 -> true

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
           (fun uu____14283  ->
              match uu____14283 with
              | (a,imp) ->
                  let uu____14296 = desugar_term env a  in
                  arg_withimp_e imp uu____14296))

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
        let is_requires uu____14328 =
          match uu____14328 with
          | (t1,uu____14334) ->
              let uu____14335 =
                let uu____14336 = unparen t1  in
                uu____14336.FStar_Parser_AST.tm  in
              (match uu____14335 with
               | FStar_Parser_AST.Requires uu____14337 -> true
               | uu____14344 -> false)
           in
        let is_ensures uu____14354 =
          match uu____14354 with
          | (t1,uu____14360) ->
              let uu____14361 =
                let uu____14362 = unparen t1  in
                uu____14362.FStar_Parser_AST.tm  in
              (match uu____14361 with
               | FStar_Parser_AST.Ensures uu____14363 -> true
               | uu____14370 -> false)
           in
        let is_app head1 uu____14385 =
          match uu____14385 with
          | (t1,uu____14391) ->
              let uu____14392 =
                let uu____14393 = unparen t1  in
                uu____14393.FStar_Parser_AST.tm  in
              (match uu____14392 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____14395;
                      FStar_Parser_AST.level = uu____14396;_},uu____14397,uu____14398)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____14399 -> false)
           in
        let is_smt_pat uu____14409 =
          match uu____14409 with
          | (t1,uu____14415) ->
              let uu____14416 =
                let uu____14417 = unparen t1  in
                uu____14417.FStar_Parser_AST.tm  in
              (match uu____14416 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____14420);
                             FStar_Parser_AST.range = uu____14421;
                             FStar_Parser_AST.level = uu____14422;_},uu____14423)::uu____14424::[])
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
                             FStar_Parser_AST.range = uu____14463;
                             FStar_Parser_AST.level = uu____14464;_},uu____14465)::uu____14466::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
               | uu____14491 -> false)
           in
        let is_decreases = is_app "decreases"  in
        let pre_process_comp_typ t1 =
          let uu____14523 = head_and_args t1  in
          match uu____14523 with
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
                   let thunk_ens uu____14621 =
                     match uu____14621 with
                     | (e,i) ->
                         let uu____14632 = thunk_ens_ e  in (uu____14632, i)
                      in
                   let fail_lemma uu____14644 =
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
                         let uu____14724 =
                           let uu____14731 =
                             let uu____14738 = thunk_ens ens  in
                             [uu____14738; nil_pat]  in
                           req_true :: uu____14731  in
                         unit_tm :: uu____14724
                     | req::ens::[] when
                         (is_requires req) && (is_ensures ens) ->
                         let uu____14785 =
                           let uu____14792 =
                             let uu____14799 = thunk_ens ens  in
                             [uu____14799; nil_pat]  in
                           req :: uu____14792  in
                         unit_tm :: uu____14785
                     | ens::smtpat::[] when
                         (((let uu____14848 = is_requires ens  in
                            Prims.op_Negation uu____14848) &&
                             (let uu____14850 = is_smt_pat ens  in
                              Prims.op_Negation uu____14850))
                            &&
                            (let uu____14852 = is_decreases ens  in
                             Prims.op_Negation uu____14852))
                           && (is_smt_pat smtpat)
                         ->
                         let uu____14853 =
                           let uu____14860 =
                             let uu____14867 = thunk_ens ens  in
                             [uu____14867; smtpat]  in
                           req_true :: uu____14860  in
                         unit_tm :: uu____14853
                     | ens::dec::[] when
                         (is_ensures ens) && (is_decreases dec) ->
                         let uu____14914 =
                           let uu____14921 =
                             let uu____14928 = thunk_ens ens  in
                             [uu____14928; nil_pat; dec]  in
                           req_true :: uu____14921  in
                         unit_tm :: uu____14914
                     | ens::dec::smtpat::[] when
                         ((is_ensures ens) && (is_decreases dec)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____14988 =
                           let uu____14995 =
                             let uu____15002 = thunk_ens ens  in
                             [uu____15002; smtpat; dec]  in
                           req_true :: uu____14995  in
                         unit_tm :: uu____14988
                     | req::ens::dec::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_decreases dec)
                         ->
                         let uu____15062 =
                           let uu____15069 =
                             let uu____15076 = thunk_ens ens  in
                             [uu____15076; nil_pat; dec]  in
                           req :: uu____15069  in
                         unit_tm :: uu____15062
                     | req::ens::smtpat::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____15136 =
                           let uu____15143 =
                             let uu____15150 = thunk_ens ens  in
                             [uu____15150; smtpat]  in
                           req :: uu____15143  in
                         unit_tm :: uu____15136
                     | req::ens::dec::smtpat::[] when
                         (((is_requires req) && (is_ensures ens)) &&
                            (is_smt_pat smtpat))
                           && (is_decreases dec)
                         ->
                         let uu____15215 =
                           let uu____15222 =
                             let uu____15229 = thunk_ens ens  in
                             [uu____15229; dec; smtpat]  in
                           req :: uu____15222  in
                         unit_tm :: uu____15215
                     | _other -> fail_lemma ()  in
                   let head_and_attributes =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) lemma
                      in
                   (head_and_attributes, args1)
               | FStar_Parser_AST.Name l when
                   FStar_Syntax_DsEnv.is_effect_name env l ->
                   let uu____15291 =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) l
                      in
                   (uu____15291, args)
               | FStar_Parser_AST.Name l when
                   (let uu____15319 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____15319
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   let uu____15320 =
                     let uu____15327 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_Tot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____15327, [])  in
                   (uu____15320, args)
               | FStar_Parser_AST.Name l when
                   (let uu____15345 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____15345
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                   ->
                   let uu____15346 =
                     let uu____15353 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_GTot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____15353, [])  in
                   (uu____15346, args)
               | FStar_Parser_AST.Name l when
                   (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                      ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                     || ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                   ->
                   let uu____15369 =
                     let uu____15376 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_Tot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____15376, [])  in
                   (uu____15369, [(t1, FStar_Parser_AST.Nothing)])
               | uu____15399 ->
                   let default_effect =
                     let uu____15401 = FStar_Options.ml_ish ()  in
                     if uu____15401
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____15404 =
                           FStar_Options.warn_default_effects ()  in
                         if uu____15404
                         then
                           FStar_Errors.log_issue
                             head1.FStar_Parser_AST.range
                             (FStar_Errors.Warning_UseDefaultEffect,
                               "Using default effect Tot")
                         else ());
                        FStar_Parser_Const.effect_Tot_lid)
                      in
                   let uu____15406 =
                     let uu____15413 =
                       FStar_Ident.set_lid_range default_effect
                         head1.FStar_Parser_AST.range
                        in
                     (uu____15413, [])  in
                   (uu____15406, [(t1, FStar_Parser_AST.Nothing)]))
           in
        let uu____15436 = pre_process_comp_typ t  in
        match uu____15436 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____15485 =
                  let uu____15490 =
                    let uu____15491 = FStar_Syntax_Print.lid_to_string eff
                       in
                    FStar_Util.format1 "Not enough args to effect %s"
                      uu____15491
                     in
                  (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____15490)  in
                fail1 uu____15485)
             else ();
             (let is_universe uu____15502 =
                match uu____15502 with
                | (uu____15507,imp) -> imp = FStar_Parser_AST.UnivApp  in
              let uu____15509 = FStar_Util.take is_universe args  in
              match uu____15509 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____15568  ->
                         match uu____15568 with
                         | (u,imp) -> desugar_universe u) universes
                     in
                  let uu____15575 =
                    let uu____15590 = FStar_List.hd args1  in
                    let uu____15599 = FStar_List.tl args1  in
                    (uu____15590, uu____15599)  in
                  (match uu____15575 with
                   | (result_arg,rest) ->
                       let result_typ =
                         desugar_typ env
                           (FStar_Pervasives_Native.fst result_arg)
                          in
                       let rest1 = desugar_args env rest  in
                       let uu____15654 =
                         let is_decrease uu____15692 =
                           match uu____15692 with
                           | (t1,uu____15702) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.pos = uu____15712;
                                       FStar_Syntax_Syntax.vars = uu____15713;_},uu____15714::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.decreases_lid
                                | uu____15753 -> false)
                            in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease)
                          in
                       (match uu____15654 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____15869  ->
                                      match uu____15869 with
                                      | (t1,uu____15879) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____15888,(arg,uu____15890)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____15929 -> failwith "impos")))
                               in
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
                                | uu____15946 -> false  in
                              (((is_empty decreases_clause) &&
                                  (is_empty rest2))
                                 && (is_empty cattributes))
                                && (is_empty universes1)
                               in
                            let uu____15957 =
                              no_additional_args &&
                                (FStar_Ident.lid_equals eff
                                   FStar_Parser_Const.effect_Tot_lid)
                               in
                            if uu____15957
                            then FStar_Syntax_Syntax.mk_Total result_typ
                            else
                              (let uu____15961 =
                                 no_additional_args &&
                                   (FStar_Ident.lid_equals eff
                                      FStar_Parser_Const.effect_GTot_lid)
                                  in
                               if uu____15961
                               then FStar_Syntax_Syntax.mk_GTotal result_typ
                               else
                                 (let flags1 =
                                    let uu____15968 =
                                      FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_Lemma_lid
                                       in
                                    if uu____15968
                                    then [FStar_Syntax_Syntax.LEMMA]
                                    else
                                      (let uu____15972 =
                                         FStar_Ident.lid_equals eff
                                           FStar_Parser_Const.effect_Tot_lid
                                          in
                                       if uu____15972
                                       then [FStar_Syntax_Syntax.TOTAL]
                                       else
                                         (let uu____15976 =
                                            FStar_Ident.lid_equals eff
                                              FStar_Parser_Const.effect_ML_lid
                                             in
                                          if uu____15976
                                          then [FStar_Syntax_Syntax.MLEFFECT]
                                          else
                                            (let uu____15980 =
                                               FStar_Ident.lid_equals eff
                                                 FStar_Parser_Const.effect_GTot_lid
                                                in
                                             if uu____15980
                                             then
                                               [FStar_Syntax_Syntax.SOMETRIVIAL]
                                             else [])))
                                     in
                                  let flags2 =
                                    FStar_List.append flags1 cattributes  in
                                  let rest3 =
                                    let uu____15998 =
                                      FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_Lemma_lid
                                       in
                                    if uu____15998
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
                                                  let uu____16087 =
                                                    FStar_Ident.set_lid_range
                                                      FStar_Parser_Const.pattern_lid
                                                      pat.FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_Syntax.fvar
                                                    uu____16087
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
                                            | uu____16108 -> pat  in
                                          let uu____16109 =
                                            let uu____16120 =
                                              let uu____16131 =
                                                let uu____16140 =
                                                  FStar_Syntax_Syntax.mk
                                                    (FStar_Syntax_Syntax.Tm_meta
                                                       (pat1,
                                                         (FStar_Syntax_Syntax.Meta_desugared
                                                            FStar_Syntax_Syntax.Meta_smt_pat)))
                                                    FStar_Pervasives_Native.None
                                                    pat1.FStar_Syntax_Syntax.pos
                                                   in
                                                (uu____16140, aq)  in
                                              [uu____16131]  in
                                            ens :: uu____16120  in
                                          req :: uu____16109
                                      | uu____16181 -> rest2
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
        | uu____16205 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___285_16226 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___285_16226.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___285_16226.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___286_16268 = b  in
             {
               FStar_Parser_AST.b = (uu___286_16268.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___286_16268.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___286_16268.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____16331 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____16331)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____16344 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____16344 with
             | (env1,a1) ->
                 let a2 =
                   let uu___287_16354 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___287_16354.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___287_16354.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____16380 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____16394 =
                     let uu____16397 =
                       let uu____16398 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____16398]  in
                     no_annot_abs uu____16397 body2  in
                   FStar_All.pipe_left setpos uu____16394  in
                 let uu____16419 =
                   let uu____16420 =
                     let uu____16437 =
                       let uu____16440 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____16440
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____16441 =
                       let uu____16452 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____16452]  in
                     (uu____16437, uu____16441)  in
                   FStar_Syntax_Syntax.Tm_app uu____16420  in
                 FStar_All.pipe_left mk1 uu____16419)
        | uu____16491 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____16571 = q (rest, pats, body)  in
              let uu____16578 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____16571 uu____16578
                FStar_Parser_AST.Formula
               in
            let uu____16579 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____16579 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____16588 -> failwith "impossible"  in
      let uu____16591 =
        let uu____16592 = unparen f  in uu____16592.FStar_Parser_AST.tm  in
      match uu____16591 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____16599,uu____16600) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____16611,uu____16612) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____16643 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____16643
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____16679 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____16679
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____16722 -> desugar_term env f

and (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                FStar_Pervasives_Native.tuple2 Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bs  ->
      let uu____16727 =
        FStar_List.fold_left
          (fun uu____16760  ->
             fun b  ->
               match uu____16760 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___288_16804 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___288_16804.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___288_16804.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___288_16804.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____16819 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____16819 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___289_16837 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___289_16837.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___289_16837.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____16838 =
                               let uu____16845 =
                                 let uu____16850 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____16850)  in
                               uu____16845 :: out  in
                             (env2, uu____16838))
                    | uu____16861 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____16727 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

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
          let uu____16932 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____16932)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____16937 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____16937)
      | FStar_Parser_AST.TVariable x ->
          let uu____16941 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____16941)
      | FStar_Parser_AST.NoName t ->
          let uu____16945 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____16945)
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
      fun uu___242_16953  ->
        match uu___242_16953 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____16975 = FStar_Syntax_Syntax.null_binder k  in
            (uu____16975, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____16992 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____16992 with
             | (env1,a1) ->
                 let uu____17009 =
                   let uu____17016 = trans_aqual env1 imp  in
                   ((let uu___290_17022 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___290_17022.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___290_17022.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____17016)
                    in
                 (uu____17009, env1))

and (trans_aqual :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___243_17030  ->
      match uu___243_17030 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____17034 =
            let uu____17035 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____17035  in
          FStar_Pervasives_Native.Some uu____17034
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
               (fun uu___244_17071  ->
                  match uu___244_17071 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____17072 -> false))
           in
        let quals2 q =
          let uu____17085 =
            (let uu____17088 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____17088) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____17085
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____17102 = FStar_Ident.range_of_lid disc_name  in
                let uu____17103 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____17102;
                  FStar_Syntax_Syntax.sigquals = uu____17103;
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
            let uu____17142 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____17180  ->
                        match uu____17180 with
                        | (x,uu____17190) ->
                            let uu____17195 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____17195 with
                             | (field_name,uu____17203) ->
                                 let only_decl =
                                   ((let uu____17207 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____17207)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____17209 =
                                        let uu____17210 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____17210.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____17209)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____17226 =
                                       FStar_List.filter
                                         (fun uu___245_17230  ->
                                            match uu___245_17230 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____17231 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____17226
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___246_17244  ->
                                             match uu___246_17244 with
                                             | FStar_Syntax_Syntax.NoExtract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____17245 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____17247 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____17247;
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____17252 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____17252
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          (FStar_Syntax_Syntax.Delta_equational_at_level
                                             (Prims.parse_int "1"))
                                      else
                                        FStar_Syntax_Syntax.Delta_equational_at_level
                                          (Prims.parse_int "1")
                                       in
                                    let lb =
                                      let uu____17257 =
                                        let uu____17262 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____17262  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____17257;
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
                                      let uu____17266 =
                                        let uu____17267 =
                                          let uu____17274 =
                                            let uu____17277 =
                                              let uu____17278 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____17278
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____17277]  in
                                          ((false, [lb]), uu____17274)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____17267
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____17266;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____17142 FStar_List.flatten
  
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
            (lid,uu____17322,t,uu____17324,n1,uu____17326) when
            let uu____17331 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____17331 ->
            let uu____17332 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____17332 with
             | (formals,uu____17350) ->
                 (match formals with
                  | [] -> []
                  | uu____17379 ->
                      let filter_records uu___247_17395 =
                        match uu___247_17395 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____17398,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____17410 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____17412 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____17412 with
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
                      let uu____17422 = FStar_Util.first_N n1 formals  in
                      (match uu____17422 with
                       | (uu____17451,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____17485 -> []
  
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
                    let uu____17563 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____17563
                    then
                      let uu____17566 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____17566
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____17569 =
                      let uu____17574 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____17574  in
                    let uu____17575 =
                      if FStar_Util.is_some kopt
                      then
                        let uu____17580 =
                          let uu____17583 =
                            FStar_All.pipe_right kopt FStar_Util.must  in
                          FStar_Syntax_Syntax.mk_Total uu____17583  in
                        FStar_Syntax_Util.arrow typars uu____17580
                      else FStar_Syntax_Syntax.tun  in
                    let uu____17587 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____17569;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____17575;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____17587;
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
          let tycon_id uu___248_17638 =
            match uu___248_17638 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____17640,uu____17641) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____17651,uu____17652,uu____17653) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____17663,uu____17664,uu____17665) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____17695,uu____17696,uu____17697) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____17741) ->
                let uu____17742 =
                  let uu____17743 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____17743  in
                FStar_Parser_AST.mk_term uu____17742 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____17745 =
                  let uu____17746 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____17746  in
                FStar_Parser_AST.mk_term uu____17745 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____17748) ->
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
              | uu____17779 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____17787 =
                     let uu____17788 =
                       let uu____17795 = binder_to_term b  in
                       (out, uu____17795, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____17788  in
                   FStar_Parser_AST.mk_term uu____17787
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___249_17807 =
            match uu___249_17807 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____17863  ->
                       match uu____17863 with
                       | (x,t,uu____17874) ->
                           let uu____17879 =
                             let uu____17880 =
                               let uu____17885 =
                                 FStar_Syntax_Util.mangle_field_name x  in
                               (uu____17885, t)  in
                             FStar_Parser_AST.Annotated uu____17880  in
                           FStar_Parser_AST.mk_binder uu____17879
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____17887 =
                    let uu____17888 =
                      let uu____17889 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____17889  in
                    FStar_Parser_AST.mk_term uu____17888
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____17887 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let uu____17893 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____17920  ->
                          match uu____17920 with
                          | (x,uu____17930,uu____17931) ->
                              FStar_Syntax_Util.unmangle_field_name x))
                   in
                ((FStar_Parser_AST.TyconVariant
                    (id1, parms, kopt,
                      [(constrName, (FStar_Pervasives_Native.Some constrTyp),
                         FStar_Pervasives_Native.None, false)])),
                  uu____17893)
            | uu____17984 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___250_18023 =
            match uu___250_18023 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____18047 = typars_of_binders _env binders  in
                (match uu____18047 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____18083 =
                         let uu____18084 =
                           let uu____18085 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____18085  in
                         FStar_Parser_AST.mk_term uu____18084
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____18083 binders  in
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
            | uu____18096 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____18138 =
              FStar_List.fold_left
                (fun uu____18172  ->
                   fun uu____18173  ->
                     match (uu____18172, uu____18173) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____18242 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____18242 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____18138 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____18333 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____18333
                | uu____18334 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____18342 = desugar_abstract_tc quals env [] tc  in
              (match uu____18342 with
               | (uu____18355,uu____18356,se,uu____18358) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____18361,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____18378 =
                                 let uu____18379 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____18379  in
                               if uu____18378
                               then
                                 let uu____18380 =
                                   let uu____18385 =
                                     let uu____18386 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____18386
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____18385)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____18380
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
                           | uu____18395 ->
                               let uu____18396 =
                                 let uu____18403 =
                                   let uu____18404 =
                                     let uu____18419 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____18419)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____18404
                                    in
                                 FStar_Syntax_Syntax.mk uu____18403  in
                               uu____18396 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___291_18435 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___291_18435.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___291_18435.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___291_18435.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____18436 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____18439 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____18439
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____18452 = typars_of_binders env binders  in
              (match uu____18452 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____18486 =
                           FStar_Util.for_some
                             (fun uu___251_18488  ->
                                match uu___251_18488 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____18489 -> false) quals
                            in
                         if uu____18486
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____18494 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____18494
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____18499 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___252_18503  ->
                               match uu___252_18503 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____18504 -> false))
                        in
                     if uu____18499
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____18513 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____18513
                     then
                       let uu____18516 =
                         let uu____18523 =
                           let uu____18524 = unparen t  in
                           uu____18524.FStar_Parser_AST.tm  in
                         match uu____18523 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____18545 =
                               match FStar_List.rev args with
                               | (last_arg,uu____18575)::args_rev ->
                                   let uu____18587 =
                                     let uu____18588 = unparen last_arg  in
                                     uu____18588.FStar_Parser_AST.tm  in
                                   (match uu____18587 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____18616 -> ([], args))
                               | uu____18625 -> ([], args)  in
                             (match uu____18545 with
                              | (cattributes,args1) ->
                                  let uu____18664 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____18664))
                         | uu____18675 -> (t, [])  in
                       match uu____18516 with
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
                                  (fun uu___253_18697  ->
                                     match uu___253_18697 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____18698 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____18705)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____18729 = tycon_record_as_variant trec  in
              (match uu____18729 with
               | (t,fs) ->
                   let uu____18746 =
                     let uu____18749 =
                       let uu____18750 =
                         let uu____18759 =
                           let uu____18762 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____18762  in
                         (uu____18759, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____18750  in
                     uu____18749 :: quals  in
                   desugar_tycon env d uu____18746 [t])
          | uu____18767::uu____18768 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____18935 = et  in
                match uu____18935 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____19160 ->
                         let trec = tc  in
                         let uu____19184 = tycon_record_as_variant trec  in
                         (match uu____19184 with
                          | (t,fs) ->
                              let uu____19243 =
                                let uu____19246 =
                                  let uu____19247 =
                                    let uu____19256 =
                                      let uu____19259 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____19259  in
                                    (uu____19256, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____19247
                                   in
                                uu____19246 :: quals1  in
                              collect_tcs uu____19243 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____19346 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____19346 with
                          | (env2,uu____19406,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____19555 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____19555 with
                          | (env2,uu____19615,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____19740 ->
                         failwith "Unrecognized mutual type definition")
                 in
              let uu____19787 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____19787 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___255_20292  ->
                             match uu___255_20292 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____20357,uu____20358);
                                    FStar_Syntax_Syntax.sigrng = uu____20359;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____20360;
                                    FStar_Syntax_Syntax.sigmeta = uu____20361;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____20362;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____20425 =
                                     typars_of_binders env1 binders  in
                                   match uu____20425 with
                                   | (env2,tpars1) ->
                                       let uu____20452 =
                                         push_tparams env2 tpars1  in
                                       (match uu____20452 with
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
                                 let uu____20481 =
                                   let uu____20500 =
                                     mk_typ_abbrev id1 uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____20500)
                                    in
                                 [uu____20481]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____20560);
                                    FStar_Syntax_Syntax.sigrng = uu____20561;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____20563;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____20564;_},constrs,tconstr,quals1)
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
                                 let uu____20662 = push_tparams env1 tpars
                                    in
                                 (match uu____20662 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____20729  ->
                                             match uu____20729 with
                                             | (x,uu____20741) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____20745 =
                                        let uu____20772 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____20880  ->
                                                  match uu____20880 with
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
                                                        let uu____20934 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____20934
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
                                                                uu___254_20945
                                                                 ->
                                                                match uu___254_20945
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____20957
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____20965 =
                                                        let uu____20984 =
                                                          let uu____20985 =
                                                            let uu____20986 =
                                                              let uu____21001
                                                                =
                                                                let uu____21002
                                                                  =
                                                                  let uu____21005
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____21005
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____21002
                                                                 in
                                                              (name, univs1,
                                                                uu____21001,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____20986
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____20985;
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
                                                          uu____20984)
                                                         in
                                                      (name, uu____20965)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____20772
                                         in
                                      (match uu____20745 with
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
                             | uu____21220 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____21346  ->
                             match uu____21346 with
                             | (name_doc,uu____21372,uu____21373) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____21445  ->
                             match uu____21445 with
                             | (uu____21464,uu____21465,se) -> se))
                      in
                   let uu____21491 =
                     let uu____21498 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____21498 rng
                      in
                   (match uu____21491 with
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
                               (fun uu____21560  ->
                                  match uu____21560 with
                                  | (uu____21581,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____21628,tps,k,uu____21631,constrs)
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
                                  | uu____21650 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____21667  ->
                                 match uu____21667 with
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
      let uu____21710 =
        FStar_List.fold_left
          (fun uu____21745  ->
             fun b  ->
               match uu____21745 with
               | (env1,binders1) ->
                   let uu____21789 = desugar_binder env1 b  in
                   (match uu____21789 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____21812 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____21812 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____21865 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____21710 with
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
          let uu____21966 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___256_21971  ->
                    match uu___256_21971 with
                    | FStar_Syntax_Syntax.Reflectable uu____21972 -> true
                    | uu____21973 -> false))
             in
          if uu____21966
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____21976 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____21976
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
      let uu____22008 = FStar_Syntax_Util.head_and_args at1  in
      match uu____22008 with
      | (hd1,args) ->
          let uu____22059 =
            let uu____22074 =
              let uu____22075 = FStar_Syntax_Subst.compress hd1  in
              uu____22075.FStar_Syntax_Syntax.n  in
            (uu____22074, args)  in
          (match uu____22059 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(a1,uu____22098)::[]) when
               (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr)
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.fail_lax_attr)
               ->
               let uu____22133 =
                 let uu____22138 =
                   FStar_Syntax_Embeddings.e_list
                     FStar_Syntax_Embeddings.e_int
                    in
                 FStar_Syntax_Embeddings.unembed uu____22138 a1  in
               (match uu____22133 with
                | FStar_Pervasives_Native.Some es when
                    (FStar_List.length es) > (Prims.parse_int "0") ->
                    let b =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.fail_lax_attr
                       in
                    let uu____22159 =
                      let uu____22166 =
                        FStar_List.map FStar_BigInt.to_int_fs es  in
                      (uu____22166, b)  in
                    FStar_Pervasives_Native.Some uu____22159
                | uu____22177 ->
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
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____22219) when
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
           | uu____22248 -> FStar_Pervasives_Native.None)
  
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
                  let uu____22417 = desugar_binders monad_env eff_binders  in
                  match uu____22417 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let for_free =
                        let uu____22456 =
                          let uu____22457 =
                            let uu____22466 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____22466  in
                          FStar_List.length uu____22457  in
                        uu____22456 = (Prims.parse_int "1")  in
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
                            (uu____22512,(FStar_Parser_AST.TyconAbbrev
                                          (name,uu____22514,uu____22515,uu____22516),uu____22517)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____22550 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____22551 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____22563 = name_of_eff_decl decl  in
                             FStar_List.mem uu____22563 mandatory_members)
                          eff_decls
                         in
                      (match uu____22551 with
                       | (mandatory_members_decls,actions) ->
                           let uu____22580 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____22609  ->
                                     fun decl  ->
                                       match uu____22609 with
                                       | (env2,out) ->
                                           let uu____22629 =
                                             desugar_decl env2 decl  in
                                           (match uu____22629 with
                                            | (env3,ses) ->
                                                let uu____22642 =
                                                  let uu____22645 =
                                                    FStar_List.hd ses  in
                                                  uu____22645 :: out  in
                                                (env3, uu____22642)))
                                  (env1, []))
                              in
                           (match uu____22580 with
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
                                              (uu____22713,(FStar_Parser_AST.TyconAbbrev
                                                            (name,action_params,uu____22716,
                                                             {
                                                               FStar_Parser_AST.tm
                                                                 =
                                                                 FStar_Parser_AST.Construct
                                                                 (uu____22717,
                                                                  (def,uu____22719)::
                                                                  (cps_type,uu____22721)::[]);
                                                               FStar_Parser_AST.range
                                                                 =
                                                                 uu____22722;
                                                               FStar_Parser_AST.level
                                                                 =
                                                                 uu____22723;_}),doc1)::[])
                                              when Prims.op_Negation for_free
                                              ->
                                              let uu____22775 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____22775 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____22813 =
                                                     let uu____22814 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____22815 =
                                                       let uu____22816 =
                                                         desugar_term env3
                                                           def
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____22816
                                                        in
                                                     let uu____22823 =
                                                       let uu____22824 =
                                                         desugar_typ env3
                                                           cps_type
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____22824
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____22814;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____22815;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____22823
                                                     }  in
                                                   (uu____22813, doc1))
                                          | FStar_Parser_AST.Tycon
                                              (uu____22833,(FStar_Parser_AST.TyconAbbrev
                                                            (name,action_params,uu____22836,defn),doc1)::[])
                                              when for_free ->
                                              let uu____22871 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____22871 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____22909 =
                                                     let uu____22910 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____22911 =
                                                       let uu____22912 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____22912
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____22910;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____22911;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____22909, doc1))
                                          | uu____22921 ->
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
                                    let uu____22953 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____22953
                                     in
                                  let uu____22954 =
                                    let uu____22955 =
                                      FStar_Syntax_DsEnv.fail_or env2
                                        (FStar_Syntax_DsEnv.try_lookup_definition
                                           env2) l
                                       in
                                    FStar_All.pipe_left
                                      (FStar_Syntax_Subst.close binders1)
                                      uu____22955
                                     in
                                  ([], uu____22954)  in
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
                                      let uu____22972 =
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      ([], uu____22972)  in
                                    let uu____22979 =
                                      let uu____22980 =
                                        let uu____22981 =
                                          let uu____22982 = lookup1 "repr"
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____22982
                                           in
                                        let uu____22991 = lookup1 "return"
                                           in
                                        let uu____22992 = lookup1 "bind"  in
                                        let uu____22993 =
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
                                            uu____22981;
                                          FStar_Syntax_Syntax.return_repr =
                                            uu____22991;
                                          FStar_Syntax_Syntax.bind_repr =
                                            uu____22992;
                                          FStar_Syntax_Syntax.actions =
                                            actions1;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            uu____22993
                                        }  in
                                      FStar_Syntax_Syntax.Sig_new_effect_for_free
                                        uu____22980
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____22979;
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
                                         (fun uu___257_22999  ->
                                            match uu___257_22999 with
                                            | FStar_Syntax_Syntax.Reifiable 
                                                -> true
                                            | FStar_Syntax_Syntax.Reflectable
                                                uu____23000 -> true
                                            | uu____23001 -> false)
                                         qualifiers
                                        in
                                     let un_ts =
                                       ([], FStar_Syntax_Syntax.tun)  in
                                     let uu____23015 =
                                       let uu____23016 =
                                         let uu____23017 =
                                           lookup1 "return_wp"  in
                                         let uu____23018 = lookup1 "bind_wp"
                                            in
                                         let uu____23019 =
                                           lookup1 "if_then_else"  in
                                         let uu____23020 = lookup1 "ite_wp"
                                            in
                                         let uu____23021 = lookup1 "stronger"
                                            in
                                         let uu____23022 = lookup1 "close_wp"
                                            in
                                         let uu____23023 = lookup1 "assert_p"
                                            in
                                         let uu____23024 = lookup1 "assume_p"
                                            in
                                         let uu____23025 = lookup1 "null_wp"
                                            in
                                         let uu____23026 = lookup1 "trivial"
                                            in
                                         let uu____23027 =
                                           if rr
                                           then
                                             let uu____23028 = lookup1 "repr"
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.snd
                                               uu____23028
                                           else FStar_Syntax_Syntax.tun  in
                                         let uu____23044 =
                                           if rr
                                           then lookup1 "return"
                                           else un_ts  in
                                         let uu____23046 =
                                           if rr
                                           then lookup1 "bind"
                                           else un_ts  in
                                         let uu____23048 =
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
                                             uu____23017;
                                           FStar_Syntax_Syntax.bind_wp =
                                             uu____23018;
                                           FStar_Syntax_Syntax.if_then_else =
                                             uu____23019;
                                           FStar_Syntax_Syntax.ite_wp =
                                             uu____23020;
                                           FStar_Syntax_Syntax.stronger =
                                             uu____23021;
                                           FStar_Syntax_Syntax.close_wp =
                                             uu____23022;
                                           FStar_Syntax_Syntax.assert_p =
                                             uu____23023;
                                           FStar_Syntax_Syntax.assume_p =
                                             uu____23024;
                                           FStar_Syntax_Syntax.null_wp =
                                             uu____23025;
                                           FStar_Syntax_Syntax.trivial =
                                             uu____23026;
                                           FStar_Syntax_Syntax.repr =
                                             uu____23027;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____23044;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____23046;
                                           FStar_Syntax_Syntax.actions =
                                             actions1;
                                           FStar_Syntax_Syntax.eff_attrs =
                                             uu____23048
                                         }  in
                                       FStar_Syntax_Syntax.Sig_new_effect
                                         uu____23016
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         uu____23015;
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
                                          fun uu____23074  ->
                                            match uu____23074 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____23088 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____23088
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
                let uu____23112 = desugar_binders env1 eff_binders  in
                match uu____23112 with
                | (env2,binders) ->
                    let uu____23149 =
                      let uu____23160 = head_and_args defn  in
                      match uu____23160 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____23197 ->
                                let uu____23198 =
                                  let uu____23203 =
                                    let uu____23204 =
                                      let uu____23205 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.strcat uu____23205 " not found"
                                       in
                                    Prims.strcat "Effect " uu____23204  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____23203)
                                   in
                                FStar_Errors.raise_error uu____23198
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____23207 =
                            match FStar_List.rev args with
                            | (last_arg,uu____23237)::args_rev ->
                                let uu____23249 =
                                  let uu____23250 = unparen last_arg  in
                                  uu____23250.FStar_Parser_AST.tm  in
                                (match uu____23249 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____23278 -> ([], args))
                            | uu____23287 -> ([], args)  in
                          (match uu____23207 with
                           | (cattributes,args1) ->
                               let uu____23330 = desugar_args env2 args1  in
                               let uu____23331 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____23330, uu____23331))
                       in
                    (match uu____23149 with
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
                          (let uu____23367 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____23367 with
                           | (ed_binders,uu____23381,ed_binders_opening) ->
                               let sub1 uu____23394 =
                                 match uu____23394 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____23408 =
                                         FStar_Syntax_Subst.shift_subst
                                           (FStar_List.length us)
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____23408 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____23412 =
                                       let uu____23413 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____23413)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____23412
                                  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____23422 =
                                   let uu____23423 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____23423
                                    in
                                 let uu____23438 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____23439 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____23440 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____23441 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____23442 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____23443 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____23444 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____23445 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____23446 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____23447 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____23448 =
                                   let uu____23449 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____23449
                                    in
                                 let uu____23464 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____23465 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____23466 =
                                   FStar_List.map
                                     (fun action  ->
                                        let uu____23474 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____23475 =
                                          let uu____23476 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____23476
                                           in
                                        let uu____23491 =
                                          let uu____23492 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____23492
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____23474;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____23475;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____23491
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
                                     uu____23422;
                                   FStar_Syntax_Syntax.ret_wp = uu____23438;
                                   FStar_Syntax_Syntax.bind_wp = uu____23439;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____23440;
                                   FStar_Syntax_Syntax.ite_wp = uu____23441;
                                   FStar_Syntax_Syntax.stronger = uu____23442;
                                   FStar_Syntax_Syntax.close_wp = uu____23443;
                                   FStar_Syntax_Syntax.assert_p = uu____23444;
                                   FStar_Syntax_Syntax.assume_p = uu____23445;
                                   FStar_Syntax_Syntax.null_wp = uu____23446;
                                   FStar_Syntax_Syntax.trivial = uu____23447;
                                   FStar_Syntax_Syntax.repr = uu____23448;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____23464;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____23465;
                                   FStar_Syntax_Syntax.actions = uu____23466;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____23509 =
                                     let uu____23510 =
                                       let uu____23519 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____23519
                                        in
                                     FStar_List.length uu____23510  in
                                   uu____23509 = (Prims.parse_int "1")  in
                                 let uu____23550 =
                                   let uu____23553 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____23553 quals  in
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
                                   FStar_Syntax_Syntax.sigquals = uu____23550;
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
                                             let uu____23575 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____23575
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____23577 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____23577
                                 then
                                   let reflect_lid =
                                     let uu____23581 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____23581
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
    let uu____23591 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____23591 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.strcat "  " (Prims.strcat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____23642 ->
              let uu____23643 =
                let uu____23644 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____23644
                 in
              Prims.strcat "\n  " uu____23643
          | uu____23645 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____23658  ->
               match uu____23658 with
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
          let uu____23676 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____23676
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____23678 =
          let uu____23689 = FStar_Syntax_Syntax.as_arg arg  in [uu____23689]
           in
        FStar_Syntax_Util.mk_app fv uu____23678

and (desugar_decl_aux :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      let uu____23720 = desugar_decl_noattrs env d  in
      match uu____23720 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____23738 = mk_comment_attr d  in uu____23738 :: attrs1  in
          let uu____23739 =
            FStar_List.mapi
              (fun i  ->
                 fun sigelt  ->
                   if i = (Prims.parse_int "0")
                   then
                     let uu___292_23745 = sigelt  in
                     {
                       FStar_Syntax_Syntax.sigel =
                         (uu___292_23745.FStar_Syntax_Syntax.sigel);
                       FStar_Syntax_Syntax.sigrng =
                         (uu___292_23745.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___292_23745.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___292_23745.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs = attrs2
                     }
                   else
                     (let uu___293_23747 = sigelt  in
                      let uu____23748 =
                        FStar_List.filter
                          (fun at1  ->
                             let uu____23754 = get_fail_attr false at1  in
                             FStar_Option.isNone uu____23754) attrs2
                         in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___293_23747.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___293_23747.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___293_23747.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___293_23747.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs = uu____23748
                      })) sigelts
             in
          (env1, uu____23739)

and (desugar_decl :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      let uu____23775 = desugar_decl_aux env d  in
      match uu____23775 with
      | (env1,ses) ->
          let uu____23786 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____23786)

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
      | FStar_Parser_AST.Fsdoc uu____23814 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____23822 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____23822, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals  in
          let tcs1 =
            FStar_List.map
              (fun uu____23859  ->
                 match uu____23859 with | (x,uu____23867) -> x) tcs
             in
          let uu____23872 =
            FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals
             in
          desugar_tycon env d uu____23872 tcs1
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals  in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____23894;
                    FStar_Parser_AST.prange = uu____23895;_},uu____23896)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____23905;
                    FStar_Parser_AST.prange = uu____23906;_},uu____23907)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____23922;
                         FStar_Parser_AST.prange = uu____23923;_},uu____23924);
                    FStar_Parser_AST.prange = uu____23925;_},uu____23926)::[]
                   -> false
               | (p,uu____23954)::[] ->
                   let uu____23963 = is_app_pattern p  in
                   Prims.op_Negation uu____23963
               | uu____23964 -> false)
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
            let uu____24037 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____24037 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____24049 =
                     let uu____24050 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____24050.FStar_Syntax_Syntax.n  in
                   match uu____24049 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____24060) ->
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
                         | uu____24093::uu____24094 ->
                             FStar_List.map
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____24097 ->
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.collect
                                  (fun uu___258_24112  ->
                                     match uu___258_24112 with
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inl uu____24115;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____24116;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____24117;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____24118;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____24119;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____24120;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____24121;_}
                                         -> []
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____24133;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____24134;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____24135;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____24136;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____24137;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____24138;_}
                                         ->
                                         FStar_Syntax_DsEnv.lookup_letbinding_quals
                                           env
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                          in
                       let quals2 =
                         let uu____24152 =
                           FStar_All.pipe_right lets1
                             (FStar_Util.for_some
                                (fun uu____24183  ->
                                   match uu____24183 with
                                   | (uu____24196,(uu____24197,t)) ->
                                       t.FStar_Parser_AST.level =
                                         FStar_Parser_AST.Formula))
                            in
                         if uu____24152
                         then FStar_Syntax_Syntax.Logic :: quals1
                         else quals1  in
                       let lbs1 =
                         let uu____24215 =
                           FStar_All.pipe_right quals2
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract)
                            in
                         if uu____24215
                         then
                           let uu____24218 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu___294_24232 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___295_24234 = fv  in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___295_24234.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___295_24234.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___294_24232.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___294_24232.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___294_24232.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___294_24232.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___294_24232.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___294_24232.FStar_Syntax_Syntax.lbpos)
                                     }))
                              in
                           ((FStar_Pervasives_Native.fst lbs), uu____24218)
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
                   | uu____24261 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____24267 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____24286 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____24267 with
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
                       let uu___296_24322 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___296_24322.FStar_Parser_AST.prange)
                       }
                   | uu____24329 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___297_24336 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___297_24336.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___297_24336.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___297_24336.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____24372 id1 =
                   match uu____24372 with
                   | (env1,ses) ->
                       let main =
                         let uu____24393 =
                           let uu____24394 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____24394  in
                         FStar_Parser_AST.mk_term uu____24393
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
                       let uu____24444 = desugar_decl env1 id_decl  in
                       (match uu____24444 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____24462 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____24462 FStar_Util.set_elements
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
            let uu____24485 = close_fun env t  in
            desugar_term env uu____24485  in
          let quals1 =
            let uu____24489 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____24489
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let se =
            let uu____24495 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____24495;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in
          let env2 =
            FStar_Syntax_DsEnv.push_doc env1 lid d.FStar_Parser_AST.doc  in
          (env2, [se])
      | FStar_Parser_AST.Exception (id1,FStar_Pervasives_Native.None ) ->
          let uu____24503 =
            FStar_Syntax_DsEnv.fail_or env
              (FStar_Syntax_DsEnv.try_lookup_lid env)
              FStar_Parser_Const.exn_lid
             in
          (match uu____24503 with
           | (t,uu____24517) ->
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
            let uu____24547 =
              let uu____24556 = FStar_Syntax_Syntax.null_binder t  in
              [uu____24556]  in
            let uu____24575 =
              let uu____24578 =
                let uu____24579 =
                  FStar_Syntax_DsEnv.fail_or env
                    (FStar_Syntax_DsEnv.try_lookup_lid env)
                    FStar_Parser_Const.exn_lid
                   in
                FStar_Pervasives_Native.fst uu____24579  in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____24578
               in
            FStar_Syntax_Util.arrow uu____24547 uu____24575  in
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
            let uu____24640 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____24640 with
            | FStar_Pervasives_Native.None  ->
                let uu____24643 =
                  let uu____24648 =
                    let uu____24649 =
                      let uu____24650 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.strcat uu____24650 " not found"  in
                    Prims.strcat "Effect name " uu____24649  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____24648)  in
                FStar_Errors.raise_error uu____24643
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____24654 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____24672 =
                  let uu____24675 =
                    let uu____24676 = desugar_term env t  in
                    ([], uu____24676)  in
                  FStar_Pervasives_Native.Some uu____24675  in
                (uu____24672, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____24689 =
                  let uu____24692 =
                    let uu____24693 = desugar_term env wp  in
                    ([], uu____24693)  in
                  FStar_Pervasives_Native.Some uu____24692  in
                let uu____24700 =
                  let uu____24703 =
                    let uu____24704 = desugar_term env t  in
                    ([], uu____24704)  in
                  FStar_Pervasives_Native.Some uu____24703  in
                (uu____24689, uu____24700)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____24716 =
                  let uu____24719 =
                    let uu____24720 = desugar_term env t  in
                    ([], uu____24720)  in
                  FStar_Pervasives_Native.Some uu____24719  in
                (FStar_Pervasives_Native.None, uu____24716)
             in
          (match uu____24654 with
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
            let uu____24754 =
              let uu____24755 =
                let uu____24762 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____24762, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____24755  in
            {
              FStar_Syntax_Syntax.sigel = uu____24754;
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
      let uu____24788 =
        FStar_List.fold_left
          (fun uu____24808  ->
             fun d  ->
               match uu____24808 with
               | (env1,sigelts) ->
                   let uu____24828 = desugar_decl env1 d  in
                   (match uu____24828 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____24788 with
      | (env1,sigelts) ->
          let rec forward acc uu___260_24873 =
            match uu___260_24873 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____24887,FStar_Syntax_Syntax.Sig_let uu____24888) ->
                     let uu____24901 =
                       let uu____24904 =
                         let uu___298_24905 = se2  in
                         let uu____24906 =
                           let uu____24909 =
                             FStar_List.filter
                               (fun uu___259_24923  ->
                                  match uu___259_24923 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____24927;
                                           FStar_Syntax_Syntax.vars =
                                             uu____24928;_},uu____24929);
                                      FStar_Syntax_Syntax.pos = uu____24930;
                                      FStar_Syntax_Syntax.vars = uu____24931;_}
                                      when
                                      let uu____24958 =
                                        let uu____24959 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____24959
                                         in
                                      uu____24958 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____24960 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____24909
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___298_24905.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___298_24905.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___298_24905.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___298_24905.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____24906
                         }  in
                       uu____24904 :: se1 :: acc  in
                     forward uu____24901 sigelts1
                 | uu____24965 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____24973 = forward [] sigelts  in (env1, uu____24973)
  
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
          | (FStar_Pervasives_Native.None ,uu____25034) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____25038;
               FStar_Syntax_Syntax.exports = uu____25039;
               FStar_Syntax_Syntax.is_interface = uu____25040;_},FStar_Parser_AST.Module
             (current_lid,uu____25042)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____25050) ->
              let uu____25053 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____25053
           in
        let uu____25058 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____25094 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____25094, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____25111 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____25111, mname, decls, false)
           in
        match uu____25058 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____25141 = desugar_decls env2 decls  in
            (match uu____25141 with
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
          let uu____25203 =
            (FStar_Options.interactive ()) &&
              (let uu____25205 =
                 let uu____25206 =
                   let uu____25207 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____25207  in
                 FStar_Util.get_file_extension uu____25206  in
               FStar_List.mem uu____25205 ["fsti"; "fsi"])
             in
          if uu____25203 then as_interface m else m  in
        let uu____25211 = desugar_modul_common curmod env m1  in
        match uu____25211 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____25229 = FStar_Syntax_DsEnv.pop ()  in
              (uu____25229, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul ->
      (env_t,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun m  ->
      let uu____25249 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____25249 with
      | (env1,modul,pop_when_done) ->
          let uu____25263 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____25263 with
           | (env2,modul1) ->
               ((let uu____25275 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____25275
                 then
                   let uu____25276 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____25276
                 else ());
                (let uu____25278 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____25278, modul1))))
  
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
        (fun uu____25325  ->
           let uu____25326 = desugar_modul env modul  in
           match uu____25326 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____25367  ->
           let uu____25368 = desugar_decls env decls  in
           match uu____25368 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____25422  ->
             let uu____25423 = desugar_partial_modul modul env a_modul  in
             match uu____25423 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____25521 ->
                  let t =
                    let uu____25531 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____25531  in
                  let uu____25544 =
                    let uu____25545 = FStar_Syntax_Subst.compress t  in
                    uu____25545.FStar_Syntax_Syntax.n  in
                  (match uu____25544 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____25557,uu____25558)
                       -> bs1
                   | uu____25583 -> failwith "Impossible")
               in
            let uu____25592 =
              let uu____25599 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____25599
                FStar_Syntax_Syntax.t_unit
               in
            match uu____25592 with
            | (binders,uu____25601,binders_opening) ->
                let erase_term t =
                  let uu____25609 =
                    let uu____25610 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____25610  in
                  FStar_Syntax_Subst.close binders uu____25609  in
                let erase_tscheme uu____25628 =
                  match uu____25628 with
                  | (us,t) ->
                      let t1 =
                        let uu____25648 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____25648 t  in
                      let uu____25651 =
                        let uu____25652 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____25652  in
                      ([], uu____25651)
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
                    | uu____25675 ->
                        let bs =
                          let uu____25685 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____25685  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____25725 =
                          let uu____25726 =
                            let uu____25729 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____25729  in
                          uu____25726.FStar_Syntax_Syntax.n  in
                        (match uu____25725 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____25731,uu____25732) -> bs1
                         | uu____25757 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____25764 =
                      let uu____25765 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____25765  in
                    FStar_Syntax_Subst.close binders uu____25764  in
                  let uu___299_25766 = action  in
                  let uu____25767 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____25768 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___299_25766.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___299_25766.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____25767;
                    FStar_Syntax_Syntax.action_typ = uu____25768
                  }  in
                let uu___300_25769 = ed  in
                let uu____25770 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____25771 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____25772 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____25773 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____25774 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____25775 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____25776 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____25777 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____25778 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____25779 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____25780 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____25781 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____25782 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____25783 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____25784 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____25785 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___300_25769.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___300_25769.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____25770;
                  FStar_Syntax_Syntax.signature = uu____25771;
                  FStar_Syntax_Syntax.ret_wp = uu____25772;
                  FStar_Syntax_Syntax.bind_wp = uu____25773;
                  FStar_Syntax_Syntax.if_then_else = uu____25774;
                  FStar_Syntax_Syntax.ite_wp = uu____25775;
                  FStar_Syntax_Syntax.stronger = uu____25776;
                  FStar_Syntax_Syntax.close_wp = uu____25777;
                  FStar_Syntax_Syntax.assert_p = uu____25778;
                  FStar_Syntax_Syntax.assume_p = uu____25779;
                  FStar_Syntax_Syntax.null_wp = uu____25780;
                  FStar_Syntax_Syntax.trivial = uu____25781;
                  FStar_Syntax_Syntax.repr = uu____25782;
                  FStar_Syntax_Syntax.return_repr = uu____25783;
                  FStar_Syntax_Syntax.bind_repr = uu____25784;
                  FStar_Syntax_Syntax.actions = uu____25785;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___300_25769.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___301_25801 = se  in
                  let uu____25802 =
                    let uu____25803 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____25803  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____25802;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___301_25801.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___301_25801.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___301_25801.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___301_25801.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___302_25807 = se  in
                  let uu____25808 =
                    let uu____25809 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____25809
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____25808;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___302_25807.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___302_25807.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___302_25807.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___302_25807.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____25811 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____25812 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____25812 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____25824 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____25824
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____25826 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____25826)
  