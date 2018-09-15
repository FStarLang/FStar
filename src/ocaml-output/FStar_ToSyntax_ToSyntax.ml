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
      fun uu___239_237  ->
        match uu___239_237 with
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
  fun uu___240_246  ->
    match uu___240_246 with
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
  fun uu___241_260  ->
    match uu___241_260 with
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
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____753 =
            FStar_List.fold_left
              (fun uu____773  ->
                 fun binder  ->
                   match uu____773 with
                   | (env1,free) ->
                       let uu____793 = free_type_vars_b env1 binder  in
                       (match uu____793 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____753 with
           | (env1,free) ->
               let uu____824 = free_type_vars env1 body  in
               FStar_List.append free uu____824)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____833 =
            FStar_List.fold_left
              (fun uu____853  ->
                 fun binder  ->
                   match uu____853 with
                   | (env1,free) ->
                       let uu____873 = free_type_vars_b env1 binder  in
                       (match uu____873 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____833 with
           | (env1,free) ->
               let uu____904 = free_type_vars env1 body  in
               FStar_List.append free uu____904)
      | FStar_Parser_AST.Project (t1,uu____908) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.Abs uu____912 -> []
      | FStar_Parser_AST.Let uu____919 -> []
      | FStar_Parser_AST.LetOpen uu____940 -> []
      | FStar_Parser_AST.If uu____945 -> []
      | FStar_Parser_AST.QForall uu____952 -> []
      | FStar_Parser_AST.QExists uu____965 -> []
      | FStar_Parser_AST.Record uu____978 -> []
      | FStar_Parser_AST.Match uu____991 -> []
      | FStar_Parser_AST.TryWith uu____1006 -> []
      | FStar_Parser_AST.Bind uu____1021 -> []
      | FStar_Parser_AST.Quote uu____1028 -> []
      | FStar_Parser_AST.VQuote uu____1033 -> []
      | FStar_Parser_AST.Antiquote uu____1034 -> []
      | FStar_Parser_AST.Seq uu____1035 -> []

let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term,(FStar_Parser_AST.term,FStar_Parser_AST.imp)
                             FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let rec aux args t1 =
      let uu____1088 =
        let uu____1089 = unparen t1  in uu____1089.FStar_Parser_AST.tm  in
      match uu____1088 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____1131 -> (t1, args)  in
    aux [] t
  
let (close :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____1155 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1155  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1173 =
                     let uu____1174 =
                       let uu____1179 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____1179)  in
                     FStar_Parser_AST.TAnnotated uu____1174  in
                   FStar_Parser_AST.mk_binder uu____1173
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
        let uu____1196 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1196  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1214 =
                     let uu____1215 =
                       let uu____1220 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____1220)  in
                     FStar_Parser_AST.TAnnotated uu____1215  in
                   FStar_Parser_AST.mk_binder uu____1214
                     x.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____1222 =
             let uu____1223 = unparen t  in uu____1223.FStar_Parser_AST.tm
              in
           match uu____1222 with
           | FStar_Parser_AST.Product uu____1224 -> t
           | uu____1231 ->
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
      | uu____1267 -> (bs, t)
  
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild uu____1275 -> true
    | FStar_Parser_AST.PatTvar (uu____1278,uu____1279) -> true
    | FStar_Parser_AST.PatVar (uu____1284,uu____1285) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____1291) -> is_var_pattern p1
    | uu____1304 -> false
  
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____1311) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____1324;
           FStar_Parser_AST.prange = uu____1325;_},uu____1326)
        -> true
    | uu____1337 -> false
  
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
    | uu____1351 -> p
  
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
            let uu____1421 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____1421 with
             | (name,args,uu____1464) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1514);
               FStar_Parser_AST.prange = uu____1515;_},args)
            when is_top_level1 ->
            let uu____1525 =
              let uu____1530 = FStar_Syntax_DsEnv.qualify env id1  in
              FStar_Util.Inr uu____1530  in
            (uu____1525, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1552);
               FStar_Parser_AST.prange = uu____1553;_},args)
            -> ((FStar_Util.Inl id1), args, FStar_Pervasives_Native.None)
        | uu____1583 -> failwith "Not an app pattern"
  
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
        | FStar_Parser_AST.PatWild uu____1638 -> acc
        | FStar_Parser_AST.PatName uu____1641 -> acc
        | FStar_Parser_AST.PatOp uu____1642 -> acc
        | FStar_Parser_AST.PatConst uu____1643 ->
            if fail_on_patconst
            then
              FStar_Errors.raise_error
                (FStar_Errors.Error_CannotRedefineConst,
                  "Constants cannot be redefined") p.FStar_Parser_AST.prange
            else acc
        | FStar_Parser_AST.PatApp (phead,pats) ->
            gather_pattern_bound_vars_from_list (phead :: pats)
        | FStar_Parser_AST.PatTvar (x,uu____1656) -> FStar_Util.set_add x acc
        | FStar_Parser_AST.PatVar (x,uu____1662) -> FStar_Util.set_add x acc
        | FStar_Parser_AST.PatList pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatTuple (pats,uu____1671) ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatOr pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatRecord guarded_pats ->
            let uu____1686 =
              FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
            gather_pattern_bound_vars_from_list uu____1686
        | FStar_Parser_AST.PatAscribed (pat,uu____1694) ->
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
    match projectee with | LocalBinder _0 -> true | uu____1763 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____1799 -> false
  
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
  fun uu___242_1845  ->
    match uu___242_1845 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____1852 -> failwith "Impossible"
  
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
  fun uu____1885  ->
    match uu____1885 with
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
      let uu____1965 =
        let uu____1982 =
          let uu____1985 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____1985  in
        let uu____1986 =
          let uu____1997 =
            let uu____2006 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2006)  in
          [uu____1997]  in
        (uu____1982, uu____1986)  in
      FStar_Syntax_Syntax.Tm_app uu____1965  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____2053 =
        let uu____2070 =
          let uu____2073 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____2073  in
        let uu____2074 =
          let uu____2085 =
            let uu____2094 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2094)  in
          [uu____2085]  in
        (uu____2070, uu____2074)  in
      FStar_Syntax_Syntax.Tm_app uu____2053  in
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
          let uu____2155 =
            let uu____2172 =
              let uu____2175 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____2175  in
            let uu____2176 =
              let uu____2187 =
                let uu____2196 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____2196)  in
              let uu____2203 =
                let uu____2214 =
                  let uu____2223 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____2223)  in
                [uu____2214]  in
              uu____2187 :: uu____2203  in
            (uu____2172, uu____2176)  in
          FStar_Syntax_Syntax.Tm_app uu____2155  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let (generalize_annotated_univs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun s  ->
    let bs_univnames bs =
      let uu____2281 =
        let uu____2296 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____2315  ->
               match uu____2315 with
               | ({ FStar_Syntax_Syntax.ppname = uu____2326;
                    FStar_Syntax_Syntax.index = uu____2327;
                    FStar_Syntax_Syntax.sort = t;_},uu____2329)
                   ->
                   let uu____2336 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____2336) uu____2296
         in
      FStar_All.pipe_right bs uu____2281  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____2352 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____2369 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____2395 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____2416,uu____2417,bs,t,uu____2420,uu____2421)
                            ->
                            let uu____2430 = bs_univnames bs  in
                            let uu____2433 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____2430 uu____2433
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____2436,uu____2437,t,uu____2439,uu____2440,uu____2441)
                            -> FStar_Syntax_Free.univnames t
                        | uu____2446 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____2395 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___268_2454 = s  in
        let uu____2455 =
          let uu____2456 =
            let uu____2465 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____2483,bs,t,lids1,lids2) ->
                          let uu___269_2496 = se  in
                          let uu____2497 =
                            let uu____2498 =
                              let uu____2515 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____2516 =
                                let uu____2517 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____2517 t  in
                              (lid, uvs, uu____2515, uu____2516, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____2498
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____2497;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___269_2496.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___269_2496.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___269_2496.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___269_2496.FStar_Syntax_Syntax.sigattrs)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____2531,t,tlid,n1,lids1) ->
                          let uu___270_2540 = se  in
                          let uu____2541 =
                            let uu____2542 =
                              let uu____2557 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____2557, tlid, n1, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____2542  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____2541;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___270_2540.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___270_2540.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___270_2540.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___270_2540.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____2560 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____2465, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____2456  in
        {
          FStar_Syntax_Syntax.sigel = uu____2455;
          FStar_Syntax_Syntax.sigrng =
            (uu___268_2454.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___268_2454.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___268_2454.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___268_2454.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2566,t) ->
        let uvs =
          let uu____2569 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____2569 FStar_Util.set_elements  in
        let uu___271_2574 = s  in
        let uu____2575 =
          let uu____2576 =
            let uu____2583 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____2583)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____2576  in
        {
          FStar_Syntax_Syntax.sigel = uu____2575;
          FStar_Syntax_Syntax.sigrng =
            (uu___271_2574.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___271_2574.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___271_2574.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___271_2574.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____2605 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____2608 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____2615) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____2648,(FStar_Util.Inl t,uu____2650),uu____2651)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____2698,(FStar_Util.Inr c,uu____2700),uu____2701)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____2748 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____2749,(FStar_Util.Inl t,uu____2751),uu____2752) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____2799,(FStar_Util.Inr c,uu____2801),uu____2802) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____2849 -> empty_set  in
          FStar_Util.set_union uu____2605 uu____2608  in
        let all_lb_univs =
          let uu____2853 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____2869 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____2869) empty_set)
             in
          FStar_All.pipe_right uu____2853 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___272_2879 = s  in
        let uu____2880 =
          let uu____2881 =
            let uu____2888 =
              let uu____2889 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___273_2901 = lb  in
                        let uu____2902 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____2905 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___273_2901.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____2902;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___273_2901.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____2905;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___273_2901.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___273_2901.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____2889)  in
            (uu____2888, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____2881  in
        {
          FStar_Syntax_Syntax.sigel = uu____2880;
          FStar_Syntax_Syntax.sigrng =
            (uu___272_2879.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___272_2879.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___272_2879.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___272_2879.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____2913,fml) ->
        let uvs =
          let uu____2916 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____2916 FStar_Util.set_elements  in
        let uu___274_2921 = s  in
        let uu____2922 =
          let uu____2923 =
            let uu____2930 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____2930)  in
          FStar_Syntax_Syntax.Sig_assume uu____2923  in
        {
          FStar_Syntax_Syntax.sigel = uu____2922;
          FStar_Syntax_Syntax.sigrng =
            (uu___274_2921.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___274_2921.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___274_2921.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___274_2921.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____2932,bs,c,flags1) ->
        let uvs =
          let uu____2941 =
            let uu____2944 = bs_univnames bs  in
            let uu____2947 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____2944 uu____2947  in
          FStar_All.pipe_right uu____2941 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___275_2955 = s  in
        let uu____2956 =
          let uu____2957 =
            let uu____2970 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____2971 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____2970, uu____2971, flags1)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____2957  in
        {
          FStar_Syntax_Syntax.sigel = uu____2956;
          FStar_Syntax_Syntax.sigrng =
            (uu___275_2955.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___275_2955.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___275_2955.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___275_2955.FStar_Syntax_Syntax.sigattrs)
        }
    | uu____2974 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___243_2979  ->
    match uu___243_2979 with
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
    | uu____2980 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____2992 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____2992)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____3011 =
      let uu____3012 = unparen t  in uu____3012.FStar_Parser_AST.tm  in
    match uu____3011 with
    | FStar_Parser_AST.Wild  ->
        let uu____3017 =
          let uu____3018 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____3018  in
        FStar_Util.Inr uu____3017
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____3029)) ->
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
             let uu____3094 = sum_to_universe u n1  in
             FStar_Util.Inr uu____3094
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____3105 = sum_to_universe u n1  in
             FStar_Util.Inr uu____3105
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____3116 =
               let uu____3121 =
                 let uu____3122 = FStar_Parser_AST.term_to_string t  in
                 Prims.strcat
                   "This universe might contain a sum of two universe variables "
                   uu____3122
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____3121)
                in
             FStar_Errors.raise_error uu____3116 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____3127 ->
        let rec aux t1 univargs =
          let uu____3161 =
            let uu____3162 = unparen t1  in uu____3162.FStar_Parser_AST.tm
             in
          match uu____3161 with
          | FStar_Parser_AST.App (t2,targ,uu____3169) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___244_3192  ->
                     match uu___244_3192 with
                     | FStar_Util.Inr uu____3197 -> true
                     | uu____3198 -> false) univargs
              then
                let uu____3203 =
                  let uu____3204 =
                    FStar_List.map
                      (fun uu___245_3213  ->
                         match uu___245_3213 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____3204  in
                FStar_Util.Inr uu____3203
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___246_3230  ->
                        match uu___246_3230 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____3236 -> failwith "impossible")
                     univargs
                    in
                 let uu____3237 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____3237)
          | uu____3243 ->
              let uu____3244 =
                let uu____3249 =
                  let uu____3250 =
                    let uu____3251 = FStar_Parser_AST.term_to_string t1  in
                    Prims.strcat uu____3251 " in universe context"  in
                  Prims.strcat "Unexpected term " uu____3250  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3249)  in
              FStar_Errors.raise_error uu____3244 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____3260 ->
        let uu____3261 =
          let uu____3266 =
            let uu____3267 =
              let uu____3268 = FStar_Parser_AST.term_to_string t  in
              Prims.strcat uu____3268 " in universe context"  in
            Prims.strcat "Unexpected term " uu____3267  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3266)  in
        FStar_Errors.raise_error uu____3261 t.FStar_Parser_AST.range
  
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
                   FStar_Syntax_Syntax.antiquotes = uu____3298;_});
            FStar_Syntax_Syntax.pos = uu____3299;
            FStar_Syntax_Syntax.vars = uu____3300;_})::uu____3301
        ->
        let uu____3332 =
          let uu____3337 =
            let uu____3338 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____3338
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____3337)  in
        FStar_Errors.raise_error uu____3332 e.FStar_Syntax_Syntax.pos
    | (bv,e)::uu____3341 ->
        let uu____3360 =
          let uu____3365 =
            let uu____3366 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____3366
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____3365)  in
        FStar_Errors.raise_error uu____3360 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'Auu____3375 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident,'Auu____3375) FStar_Pervasives_Native.tuple2
        Prims.list -> FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____3403 = FStar_List.hd fields  in
        match uu____3403 with
        | (f,uu____3413) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____3425 =
                match uu____3425 with
                | (f',uu____3431) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____3433 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____3433
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
              (let uu____3437 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____3437);
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
          | FStar_Syntax_Syntax.Pat_dot_term uu____3817 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_wild uu____3824 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_constant uu____3825 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_var x ->
              FStar_Util.set_add x FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_cons (uu____3827,pats1) ->
              let aux out uu____3865 =
                match uu____3865 with
                | (p2,uu____3877) ->
                    let intersection =
                      let uu____3885 = pat_vars p2  in
                      FStar_Util.set_intersect uu____3885 out  in
                    let uu____3888 = FStar_Util.set_is_empty intersection  in
                    if uu____3888
                    then
                      let uu____3891 = pat_vars p2  in
                      FStar_Util.set_union out uu____3891
                    else
                      (let duplicate_bv =
                         let uu____3896 =
                           FStar_Util.set_elements intersection  in
                         FStar_List.hd uu____3896  in
                       let uu____3899 =
                         let uu____3904 =
                           FStar_Util.format1
                             "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                             (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                            in
                         (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                           uu____3904)
                          in
                       FStar_Errors.raise_error uu____3899 r)
                 in
              FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
           in
        match pats with
        | [] -> ()
        | p1::[] ->
            let uu____3924 = pat_vars p1  in
            FStar_All.pipe_right uu____3924 (fun a1  -> ())
        | p1::ps ->
            let pvars = pat_vars p1  in
            let aux p2 =
              let uu____3952 =
                let uu____3953 = pat_vars p2  in
                FStar_Util.set_eq pvars uu____3953  in
              if uu____3952
              then ()
              else
                (let nonlinear_vars =
                   let uu____3960 = pat_vars p2  in
                   FStar_Util.set_symmetric_difference pvars uu____3960  in
                 let first_nonlinear_var =
                   let uu____3964 = FStar_Util.set_elements nonlinear_vars
                      in
                   FStar_List.hd uu____3964  in
                 let uu____3967 =
                   let uu____3972 =
                     FStar_Util.format1
                       "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                       (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                      in
                   (FStar_Errors.Fatal_IncoherentPatterns, uu____3972)  in
                 FStar_Errors.raise_error uu____3967 r)
               in
            FStar_List.iter aux ps
         in
      let resolvex l e x =
        let uu____3997 =
          FStar_All.pipe_right l
            (FStar_Util.find_opt
               (fun y  ->
                  (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                    x.FStar_Ident.idText))
           in
        match uu____3997 with
        | FStar_Pervasives_Native.Some y -> (l, e, y)
        | uu____4013 ->
            let uu____4016 = FStar_Syntax_DsEnv.push_bv e x  in
            (match uu____4016 with | (e1,x1) -> ((x1 :: l), e1, x1))
         in
      let rec aux' top loc env1 p1 =
        let pos q = FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange
           in
        let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
        let orig = p1  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr uu____4161 -> failwith "impossible"
        | FStar_Parser_AST.PatOp op ->
            let uu____4183 =
              let uu____4184 =
                let uu____4185 =
                  let uu____4192 =
                    let uu____4193 =
                      let uu____4198 =
                        FStar_Parser_AST.compile_op (Prims.parse_int "0")
                          op.FStar_Ident.idText op.FStar_Ident.idRange
                         in
                      (uu____4198, (op.FStar_Ident.idRange))  in
                    FStar_Ident.mk_ident uu____4193  in
                  (uu____4192, FStar_Pervasives_Native.None)  in
                FStar_Parser_AST.PatVar uu____4185  in
              {
                FStar_Parser_AST.pat = uu____4184;
                FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
              }  in
            aux loc env1 uu____4183
        | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
            ((match tacopt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some uu____4215 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                      "Type ascriptions within patterns cannot be associated with a tactic")
                    orig.FStar_Parser_AST.prange);
             (let uu____4216 = aux loc env1 p2  in
              match uu____4216 with
              | (loc1,env',binder,p3,annots,imp) ->
                  let annot_pat_var p4 t1 =
                    match p4.FStar_Syntax_Syntax.v with
                    | FStar_Syntax_Syntax.Pat_var x ->
                        let uu___276_4301 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_var
                               (let uu___277_4306 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___277_4306.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___277_4306.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___276_4301.FStar_Syntax_Syntax.p)
                        }
                    | FStar_Syntax_Syntax.Pat_wild x ->
                        let uu___278_4308 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_wild
                               (let uu___279_4313 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___279_4313.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___279_4313.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___278_4308.FStar_Syntax_Syntax.p)
                        }
                    | uu____4314 when top -> p4
                    | uu____4315 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                            "Type ascriptions within patterns are only allowed on variables")
                          orig.FStar_Parser_AST.prange
                     in
                  let uu____4318 =
                    match binder with
                    | LetBinder uu____4339 -> failwith "impossible"
                    | LocalBinder (x,aq) ->
                        let t1 =
                          let uu____4363 = close_fun env1 t  in
                          desugar_term env1 uu____4363  in
                        let x1 =
                          let uu___280_4365 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___280_4365.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___280_4365.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t1
                          }  in
                        ([(x1, t1)], (LocalBinder (x1, aq)))
                     in
                  (match uu____4318 with
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
            let uu____4430 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
            (loc, env1, (LocalBinder (x, aq1)), uu____4430, [], imp)
        | FStar_Parser_AST.PatConst c ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                FStar_Syntax_Syntax.tun
               in
            let uu____4443 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____4443, [], false)
        | FStar_Parser_AST.PatTvar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____4464 = resolvex loc env1 x  in
            (match uu____4464 with
             | (loc1,env2,xbv) ->
                 let uu____4492 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____4492, [], imp))
        | FStar_Parser_AST.PatVar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____4513 = resolvex loc env1 x  in
            (match uu____4513 with
             | (loc1,env2,xbv) ->
                 let uu____4541 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____4541, [], imp))
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
            let uu____4555 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (l1, []))
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____4555, [], false)
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
               FStar_Parser_AST.prange = uu____4581;_},args)
            ->
            let uu____4587 =
              FStar_List.fold_right
                (fun arg  ->
                   fun uu____4646  ->
                     match uu____4646 with
                     | (loc1,env2,annots,args1) ->
                         let uu____4723 = aux loc1 env2 arg  in
                         (match uu____4723 with
                          | (loc2,env3,uu____4768,arg1,ans,imp) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((arg1, imp) :: args1)))) args
                (loc, env1, [], [])
               in
            (match uu____4587 with
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
                 let uu____4890 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____4890, annots, false))
        | FStar_Parser_AST.PatApp uu____4905 ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
              p1.FStar_Parser_AST.prange
        | FStar_Parser_AST.PatList pats ->
            let uu____4933 =
              FStar_List.fold_right
                (fun pat  ->
                   fun uu____4984  ->
                     match uu____4984 with
                     | (loc1,env2,annots,pats1) ->
                         let uu____5045 = aux loc1 env2 pat  in
                         (match uu____5045 with
                          | (loc2,env3,uu____5086,pat1,ans,uu____5089) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                (pat1 :: pats1)))) pats (loc, env1, [], [])
               in
            (match uu____4933 with
             | (loc1,env2,annots,pats1) ->
                 let pat =
                   let uu____5183 =
                     let uu____5186 =
                       let uu____5193 =
                         FStar_Range.end_range p1.FStar_Parser_AST.prange  in
                       pos_r uu____5193  in
                     let uu____5194 =
                       let uu____5195 =
                         let uu____5208 =
                           FStar_Syntax_Syntax.lid_as_fv
                             FStar_Parser_Const.nil_lid
                             FStar_Syntax_Syntax.delta_constant
                             (FStar_Pervasives_Native.Some
                                FStar_Syntax_Syntax.Data_ctor)
                            in
                         (uu____5208, [])  in
                       FStar_Syntax_Syntax.Pat_cons uu____5195  in
                     FStar_All.pipe_left uu____5186 uu____5194  in
                   FStar_List.fold_right
                     (fun hd1  ->
                        fun tl1  ->
                          let r =
                            FStar_Range.union_ranges
                              hd1.FStar_Syntax_Syntax.p
                              tl1.FStar_Syntax_Syntax.p
                             in
                          let uu____5240 =
                            let uu____5241 =
                              let uu____5254 =
                                FStar_Syntax_Syntax.lid_as_fv
                                  FStar_Parser_Const.cons_lid
                                  FStar_Syntax_Syntax.delta_constant
                                  (FStar_Pervasives_Native.Some
                                     FStar_Syntax_Syntax.Data_ctor)
                                 in
                              (uu____5254, [(hd1, false); (tl1, false)])  in
                            FStar_Syntax_Syntax.Pat_cons uu____5241  in
                          FStar_All.pipe_left (pos_r r) uu____5240) pats1
                     uu____5183
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
            let uu____5300 =
              FStar_List.fold_left
                (fun uu____5358  ->
                   fun p2  ->
                     match uu____5358 with
                     | (loc1,env2,annots,pats) ->
                         let uu____5436 = aux loc1 env2 p2  in
                         (match uu____5436 with
                          | (loc2,env3,uu____5481,pat,ans,uu____5484) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((pat, false) :: pats)))) (loc, env1, [], [])
                args
               in
            (match uu____5300 with
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
                   | uu____5633 -> failwith "impossible"  in
                 let x =
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some
                        (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun
                    in
                 let uu____5635 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____5635, annots, false))
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
                   (fun uu____5710  ->
                      match uu____5710 with
                      | (f,p2) -> ((f.FStar_Ident.ident), p2)))
               in
            let args =
              FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                (FStar_List.map
                   (fun uu____5740  ->
                      match uu____5740 with
                      | (f,uu____5746) ->
                          let uu____5747 =
                            FStar_All.pipe_right fields1
                              (FStar_List.tryFind
                                 (fun uu____5773  ->
                                    match uu____5773 with
                                    | (g,uu____5779) ->
                                        f.FStar_Ident.idText =
                                          g.FStar_Ident.idText))
                             in
                          (match uu____5747 with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatWild
                                    FStar_Pervasives_Native.None)
                                 p1.FStar_Parser_AST.prange
                           | FStar_Pervasives_Native.Some (uu____5784,p2) ->
                               p2)))
               in
            let app =
              let uu____5791 =
                let uu____5792 =
                  let uu____5799 =
                    let uu____5800 =
                      let uu____5801 =
                        FStar_Ident.lid_of_ids
                          (FStar_List.append
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                             [record.FStar_Syntax_DsEnv.constrname])
                         in
                      FStar_Parser_AST.PatName uu____5801  in
                    FStar_Parser_AST.mk_pattern uu____5800
                      p1.FStar_Parser_AST.prange
                     in
                  (uu____5799, args)  in
                FStar_Parser_AST.PatApp uu____5792  in
              FStar_Parser_AST.mk_pattern uu____5791
                p1.FStar_Parser_AST.prange
               in
            let uu____5804 = aux loc env1 app  in
            (match uu____5804 with
             | (env2,e,b,p2,annots,uu____5848) ->
                 let p3 =
                   match p2.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                       let uu____5884 =
                         let uu____5885 =
                           let uu____5898 =
                             let uu___281_5899 = fv  in
                             let uu____5900 =
                               let uu____5903 =
                                 let uu____5904 =
                                   let uu____5911 =
                                     FStar_All.pipe_right
                                       record.FStar_Syntax_DsEnv.fields
                                       (FStar_List.map
                                          FStar_Pervasives_Native.fst)
                                      in
                                   ((record.FStar_Syntax_DsEnv.typename),
                                     uu____5911)
                                    in
                                 FStar_Syntax_Syntax.Record_ctor uu____5904
                                  in
                               FStar_Pervasives_Native.Some uu____5903  in
                             {
                               FStar_Syntax_Syntax.fv_name =
                                 (uu___281_5899.FStar_Syntax_Syntax.fv_name);
                               FStar_Syntax_Syntax.fv_delta =
                                 (uu___281_5899.FStar_Syntax_Syntax.fv_delta);
                               FStar_Syntax_Syntax.fv_qual = uu____5900
                             }  in
                           (uu____5898, args1)  in
                         FStar_Syntax_Syntax.Pat_cons uu____5885  in
                       FStar_All.pipe_left pos uu____5884
                   | uu____5936 -> p2  in
                 (env2, e, b, p3, annots, false))
      
      and aux loc env1 p1 = aux' false loc env1 p1
       in
      let aux_maybe_or env1 p1 =
        let loc = []  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr [] -> failwith "impossible"
        | FStar_Parser_AST.PatOr (p2::ps) ->
            let uu____6018 = aux' true loc env1 p2  in
            (match uu____6018 with
             | (loc1,env2,var,p3,ans,uu____6060) ->
                 let uu____6073 =
                   FStar_List.fold_left
                     (fun uu____6122  ->
                        fun p4  ->
                          match uu____6122 with
                          | (loc2,env3,ps1) ->
                              let uu____6187 = aux' true loc2 env3 p4  in
                              (match uu____6187 with
                               | (loc3,env4,uu____6226,p5,ans1,uu____6229) ->
                                   (loc3, env4, ((p5, ans1) :: ps1))))
                     (loc1, env2, []) ps
                    in
                 (match uu____6073 with
                  | (loc2,env3,ps1) ->
                      let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                      (env3, var, pats)))
        | uu____6388 ->
            let uu____6389 = aux' true loc env1 p1  in
            (match uu____6389 with
             | (loc1,env2,vars,pat,ans,b) -> (env2, vars, [(pat, ans)]))
         in
      let uu____6482 = aux_maybe_or env p  in
      match uu____6482 with
      | (env1,b,pats) ->
          ((let uu____6537 = FStar_List.map FStar_Pervasives_Native.fst pats
               in
            check_linear_pattern_variables uu____6537
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
          let uu____6609 =
            let uu____6610 =
              let uu____6621 = FStar_Syntax_DsEnv.qualify env x  in
              (uu____6621, (ty, tacopt))  in
            LetBinder uu____6610  in
          (env, uu____6609, [])  in
        let op_to_ident x =
          let uu____6638 =
            let uu____6643 =
              FStar_Parser_AST.compile_op (Prims.parse_int "0")
                x.FStar_Ident.idText x.FStar_Ident.idRange
               in
            (uu____6643, (x.FStar_Ident.idRange))  in
          FStar_Ident.mk_ident uu____6638  in
        if top
        then
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu____6661 = op_to_ident x  in
              mklet uu____6661 FStar_Syntax_Syntax.tun
                FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x,uu____6663) ->
              mklet x FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu____6669;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____6685 = op_to_ident x  in
              let uu____6686 = desugar_term env t  in
              mklet uu____6685 uu____6686 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____6688);
                 FStar_Parser_AST.prange = uu____6689;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____6709 = desugar_term env t  in
              mklet x uu____6709 tacopt1
          | uu____6710 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu____6720 = desugar_data_pat env p  in
           match uu____6720 with
           | (env1,binder,p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu____6749;
                      FStar_Syntax_Syntax.p = uu____6750;_},uu____6751)::[]
                     -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu____6764;
                      FStar_Syntax_Syntax.p = uu____6765;_},uu____6766)::[]
                     -> []
                 | uu____6779 -> p1  in
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
  fun uu____6786  ->
    fun env  ->
      fun pat  ->
        let uu____6789 = desugar_data_pat env pat  in
        match uu____6789 with | (env1,uu____6805,pat1) -> (env1, pat1)

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
      let uu____6824 = desugar_term_aq env e  in
      match uu____6824 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____6841 = desugar_typ_aq env e  in
      match uu____6841 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness,FStar_Const.width)
        FStar_Pervasives_Native.tuple2 ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____6851  ->
        fun range  ->
          match uu____6851 with
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
              ((let uu____6861 =
                  let uu____6862 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____6862  in
                if uu____6861
                then
                  let uu____6863 =
                    let uu____6868 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____6868)  in
                  FStar_Errors.log_issue range uu____6863
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
                  let uu____6873 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____6873 range  in
                let lid1 =
                  let uu____6877 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____6877 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____6887 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____6887 range  in
                           let private_fv =
                             let uu____6889 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____6889 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___282_6890 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___282_6890.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___282_6890.FStar_Syntax_Syntax.vars)
                           }
                       | uu____6891 ->
                           failwith
                             (Prims.strcat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____6894 =
                        let uu____6899 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____6899)
                         in
                      FStar_Errors.raise_error uu____6894 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____6915 =
                  let uu____6922 =
                    let uu____6923 =
                      let uu____6940 =
                        let uu____6951 =
                          let uu____6960 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____6960)  in
                        [uu____6951]  in
                      (lid1, uu____6940)  in
                    FStar_Syntax_Syntax.Tm_app uu____6923  in
                  FStar_Syntax_Syntax.mk uu____6922  in
                uu____6915 FStar_Pervasives_Native.None range))

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
            let uu____7009 =
              let uu____7016 =
                (if resolve
                 then FStar_Syntax_DsEnv.try_lookup_lid_with_attributes
                 else
                   FStar_Syntax_DsEnv.try_lookup_lid_with_attributes_no_resolve)
                  env
                 in
              FStar_Syntax_DsEnv.fail_or env uu____7016 l  in
            match uu____7009 with
            | (tm,attrs) ->
                let warn_if_deprecated attrs1 =
                  FStar_List.iter
                    (fun a  ->
                       match a.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_app
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____7066;
                              FStar_Syntax_Syntax.vars = uu____7067;_},args)
                           when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____7094 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____7094 " is deprecated"  in
                           let msg1 =
                             if
                               (FStar_List.length args) >
                                 (Prims.parse_int "0")
                             then
                               let uu____7104 =
                                 let uu____7105 =
                                   let uu____7108 = FStar_List.hd args  in
                                   FStar_Pervasives_Native.fst uu____7108  in
                                 uu____7105.FStar_Syntax_Syntax.n  in
                               match uu____7104 with
                               | FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_string (s,uu____7130))
                                   when
                                   Prims.op_Negation
                                     ((FStar_Util.trim_string s) = "")
                                   ->
                                   Prims.strcat msg
                                     (Prims.strcat ", use "
                                        (Prims.strcat s " instead"))
                               | uu____7131 -> msg
                             else msg  in
                           let uu____7133 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____7133
                             (FStar_Errors.Warning_DeprecatedDefinition,
                               msg1)
                       | FStar_Syntax_Syntax.Tm_fvar fv when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____7136 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____7136 " is deprecated"  in
                           let uu____7137 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____7137
                             (FStar_Errors.Warning_DeprecatedDefinition, msg)
                       | uu____7138 -> ()) attrs1
                   in
                (warn_if_deprecated attrs; (let tm1 = setpos tm  in tm1))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____7153 =
          let uu____7154 = unparen t  in uu____7154.FStar_Parser_AST.tm  in
        match uu____7153 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____7155; FStar_Ident.ident = uu____7156;
              FStar_Ident.nsstr = uu____7157; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____7160 ->
            let uu____7161 =
              let uu____7166 =
                let uu____7167 = FStar_Parser_AST.term_to_string t  in
                Prims.strcat "Unknown attribute " uu____7167  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____7166)  in
            FStar_Errors.raise_error uu____7161 t.FStar_Parser_AST.range
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
          let uu___283_7250 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___283_7250.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___283_7250.FStar_Syntax_Syntax.vars)
          }  in
        let uu____7253 =
          let uu____7254 = unparen top  in uu____7254.FStar_Parser_AST.tm  in
        match uu____7253 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____7259 ->
            let uu____7266 = desugar_formula env top  in (uu____7266, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____7273 = desugar_formula env t  in (uu____7273, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____7280 = desugar_formula env t  in (uu____7280, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____7304 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____7304, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____7306 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____7306, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____7314 =
                let uu____7315 =
                  let uu____7322 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____7322, args)  in
                FStar_Parser_AST.Op uu____7315  in
              FStar_Parser_AST.mk_term uu____7314 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____7325 =
              let uu____7326 =
                let uu____7327 =
                  let uu____7334 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____7334, [e])  in
                FStar_Parser_AST.Op uu____7327  in
              FStar_Parser_AST.mk_term uu____7326 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____7325
        | FStar_Parser_AST.Op (op_star,uu____7338::uu____7339::[]) when
            (let uu____7344 = FStar_Ident.text_of_id op_star  in
             uu____7344 = "*") &&
              (let uu____7346 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____7346 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____7361;_},t1::t2::[])
                  ->
                  let uu____7366 = flatten1 t1  in
                  FStar_List.append uu____7366 [t2]
              | uu____7369 -> [t]  in
            let uu____7370 =
              let uu____7395 =
                let uu____7418 =
                  let uu____7421 = unparen top  in flatten1 uu____7421  in
                FStar_All.pipe_right uu____7418
                  (FStar_List.map
                     (fun t  ->
                        let uu____7456 = desugar_typ_aq env t  in
                        match uu____7456 with
                        | (t',aq) ->
                            let uu____7467 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____7467, aq)))
                 in
              FStar_All.pipe_right uu____7395 FStar_List.unzip  in
            (match uu____7370 with
             | (targs,aqs) ->
                 let tup =
                   let uu____7577 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____7577
                    in
                 let uu____7586 =
                   mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                 (uu____7586, (join_aqs aqs)))
        | FStar_Parser_AST.Tvar a ->
            let uu____7600 =
              let uu____7601 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_All.pipe_left setpos uu____7601  in
            (uu____7600, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____7607 =
              let uu____7612 =
                let uu____7613 =
                  let uu____7614 = FStar_Ident.text_of_id u  in
                  Prims.strcat uu____7614 " in non-universe context"  in
                Prims.strcat "Unexpected universe variable " uu____7613  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____7612)  in
            FStar_Errors.raise_error uu____7607 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____7625 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____7625 with
             | FStar_Pervasives_Native.None  ->
                 let uu____7632 =
                   let uu____7637 =
                     let uu____7638 = FStar_Ident.text_of_id s  in
                     Prims.strcat "Unexpected or unbound operator: "
                       uu____7638
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____7637)
                    in
                 FStar_Errors.raise_error uu____7632
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let uu____7648 =
                     let uu____7673 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____7735 = desugar_term_aq env t  in
                               match uu____7735 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____7673 FStar_List.unzip  in
                   (match uu____7648 with
                    | (args1,aqs) ->
                        let uu____7868 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____7868, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____7884)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____7899 =
              let uu___284_7900 = top  in
              let uu____7901 =
                let uu____7902 =
                  let uu____7909 =
                    let uu___285_7910 = top  in
                    let uu____7911 =
                      let uu____7912 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____7912  in
                    {
                      FStar_Parser_AST.tm = uu____7911;
                      FStar_Parser_AST.range =
                        (uu___285_7910.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___285_7910.FStar_Parser_AST.level)
                    }  in
                  (uu____7909, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____7902  in
              {
                FStar_Parser_AST.tm = uu____7901;
                FStar_Parser_AST.range =
                  (uu___284_7900.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___284_7900.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____7899
        | FStar_Parser_AST.Construct (n1,(a,uu____7915)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____7931 =
                let uu___286_7932 = top  in
                let uu____7933 =
                  let uu____7934 =
                    let uu____7941 =
                      let uu___287_7942 = top  in
                      let uu____7943 =
                        let uu____7944 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____7944  in
                      {
                        FStar_Parser_AST.tm = uu____7943;
                        FStar_Parser_AST.range =
                          (uu___287_7942.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___287_7942.FStar_Parser_AST.level)
                      }  in
                    (uu____7941, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____7934  in
                {
                  FStar_Parser_AST.tm = uu____7933;
                  FStar_Parser_AST.range =
                    (uu___286_7932.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___286_7932.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____7931))
        | FStar_Parser_AST.Construct (n1,(a,uu____7947)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____7962 =
              let uu___288_7963 = top  in
              let uu____7964 =
                let uu____7965 =
                  let uu____7972 =
                    let uu___289_7973 = top  in
                    let uu____7974 =
                      let uu____7975 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____7975  in
                    {
                      FStar_Parser_AST.tm = uu____7974;
                      FStar_Parser_AST.range =
                        (uu___289_7973.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___289_7973.FStar_Parser_AST.level)
                    }  in
                  (uu____7972, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____7965  in
              {
                FStar_Parser_AST.tm = uu____7964;
                FStar_Parser_AST.range =
                  (uu___288_7963.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___288_7963.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____7962
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____7976; FStar_Ident.ident = uu____7977;
              FStar_Ident.nsstr = uu____7978; FStar_Ident.str = "Type0";_}
            ->
            let uu____7981 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____7981, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____7982; FStar_Ident.ident = uu____7983;
              FStar_Ident.nsstr = uu____7984; FStar_Ident.str = "Type";_}
            ->
            let uu____7987 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____7987, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____7988; FStar_Ident.ident = uu____7989;
               FStar_Ident.nsstr = uu____7990; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____8008 =
              let uu____8009 =
                let uu____8010 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____8010  in
              mk1 uu____8009  in
            (uu____8008, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8011; FStar_Ident.ident = uu____8012;
              FStar_Ident.nsstr = uu____8013; FStar_Ident.str = "Effect";_}
            ->
            let uu____8016 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____8016, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8017; FStar_Ident.ident = uu____8018;
              FStar_Ident.nsstr = uu____8019; FStar_Ident.str = "True";_}
            ->
            let uu____8022 =
              let uu____8023 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8023
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8022, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8024; FStar_Ident.ident = uu____8025;
              FStar_Ident.nsstr = uu____8026; FStar_Ident.str = "False";_}
            ->
            let uu____8029 =
              let uu____8030 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8030
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8029, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____8033;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____8035 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____8035 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____8044 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_constant_at_level
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None
                     in
                  (uu____8044, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____8045 =
                    let uu____8046 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____8046 txt
                     in
                  failwith uu____8045))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8053 = desugar_name mk1 setpos env true l  in
              (uu____8053, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8056 = desugar_name mk1 setpos env true l  in
              (uu____8056, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____8067 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____8067 with
                | FStar_Pervasives_Native.Some uu____8076 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____8081 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____8081 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____8095 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____8112 =
                    let uu____8113 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____8113  in
                  (uu____8112, noaqs)
              | uu____8114 ->
                  let uu____8121 =
                    let uu____8126 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____8126)  in
                  FStar_Errors.raise_error uu____8121
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____8133 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____8133 with
              | FStar_Pervasives_Native.None  ->
                  let uu____8140 =
                    let uu____8145 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____8145)
                     in
                  FStar_Errors.raise_error uu____8140
                    top.FStar_Parser_AST.range
              | uu____8150 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____8154 = desugar_name mk1 setpos env true lid'  in
                  (uu____8154, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8170 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____8170 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____8189 ->
                       let uu____8196 =
                         FStar_Util.take
                           (fun uu____8220  ->
                              match uu____8220 with
                              | (uu____8225,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____8196 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____8270 =
                              let uu____8295 =
                                FStar_List.map
                                  (fun uu____8338  ->
                                     match uu____8338 with
                                     | (t,imp) ->
                                         let uu____8355 =
                                           desugar_term_aq env t  in
                                         (match uu____8355 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____8295
                                FStar_List.unzip
                               in
                            (match uu____8270 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____8496 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____8496, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____8514 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____8514 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.strcat "Constructor "
                             (Prims.strcat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____8521 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.strcat "Effect "
                             (Prims.strcat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____8532 =
              FStar_List.fold_left
                (fun uu____8577  ->
                   fun b  ->
                     match uu____8577 with
                     | (env1,tparams,typs) ->
                         let uu____8634 = desugar_binder env1 b  in
                         (match uu____8634 with
                          | (xopt,t1) ->
                              let uu____8663 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____8672 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____8672)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____8663 with
                               | (env2,x) ->
                                   let uu____8692 =
                                     let uu____8695 =
                                       let uu____8698 =
                                         let uu____8699 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____8699
                                          in
                                       [uu____8698]  in
                                     FStar_List.append typs uu____8695  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___290_8725 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___290_8725.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___290_8725.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____8692)))) (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      FStar_Pervasives_Native.None])
               in
            (match uu____8532 with
             | (env1,uu____8753,targs) ->
                 let tup =
                   let uu____8776 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____8776
                    in
                 let uu____8777 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_app (tup, targs))
                    in
                 (uu____8777, noaqs))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____8796 = uncurry binders t  in
            (match uu____8796 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___247_8840 =
                   match uu___247_8840 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1  in
                       let uu____8856 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____8856
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____8880 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____8880 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____8913 = aux env [] bs  in (uu____8913, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____8922 = desugar_binder env b  in
            (match uu____8922 with
             | (FStar_Pervasives_Native.None ,uu____8933) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____8947 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____8947 with
                  | ((x,uu____8963),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____8976 =
                        let uu____8977 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____8977  in
                      (uu____8976, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let bvss =
              FStar_List.map (gather_pattern_bound_vars false) binders  in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set1::sets2 ->
                    let i = FStar_Util.set_intersect acc set1  in
                    let uu____9055 = FStar_Util.set_is_empty i  in
                    if uu____9055
                    then
                      let uu____9058 = FStar_Util.set_union acc set1  in
                      aux uu____9058 sets2
                    else
                      (let uu____9062 =
                         let uu____9063 = FStar_Util.set_elements i  in
                         FStar_List.hd uu____9063  in
                       FStar_Pervasives_Native.Some uu____9062)
                 in
              let uu____9066 = FStar_Syntax_Syntax.new_id_set ()  in
              aux uu____9066 sets  in
            ((let uu____9070 = check_disjoint bvss  in
              match uu____9070 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some id1 ->
                  let uu____9074 =
                    let uu____9079 =
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        id1.FStar_Ident.idText
                       in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____9079)
                     in
                  let uu____9080 = FStar_Ident.range_of_id id1  in
                  FStar_Errors.raise_error uu____9074 uu____9080);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern)
                 in
              let uu____9088 =
                FStar_List.fold_left
                  (fun uu____9108  ->
                     fun pat  ->
                       match uu____9108 with
                       | (env1,ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____9134,(t,FStar_Pervasives_Native.None ))
                                ->
                                let uu____9144 =
                                  let uu____9147 = free_type_vars env1 t  in
                                  FStar_List.append uu____9147 ftvs  in
                                (env1, uu____9144)
                            | FStar_Parser_AST.PatAscribed
                                (uu____9152,(t,FStar_Pervasives_Native.Some
                                             tac))
                                ->
                                let uu____9163 =
                                  let uu____9166 = free_type_vars env1 t  in
                                  let uu____9169 =
                                    let uu____9172 = free_type_vars env1 tac
                                       in
                                    FStar_List.append uu____9172 ftvs  in
                                  FStar_List.append uu____9166 uu____9169  in
                                (env1, uu____9163)
                            | uu____9177 -> (env1, ftvs))) (env, []) binders1
                 in
              match uu____9088 with
              | (uu____9186,ftv) ->
                  let ftv1 = sort_ftv ftv  in
                  let binders2 =
                    let uu____9198 =
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
                    FStar_List.append uu____9198 binders1  in
                  let rec aux env1 bs sc_pat_opt uu___248_9255 =
                    match uu___248_9255 with
                    | [] ->
                        let uu____9282 = desugar_term_aq env1 body  in
                        (match uu____9282 with
                         | (body1,aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc,pat) ->
                                   let body2 =
                                     let uu____9319 =
                                       let uu____9320 =
                                         FStar_Syntax_Syntax.pat_bvs pat  in
                                       FStar_All.pipe_right uu____9320
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder)
                                        in
                                     FStar_Syntax_Subst.close uu____9319
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
                             let uu____9389 =
                               let uu____9392 =
                                 no_annot_abs (FStar_List.rev bs) body2  in
                               setpos uu____9392  in
                             (uu____9389, aq))
                    | p::rest ->
                        let uu____9407 = desugar_binding_pat env1 p  in
                        (match uu____9407 with
                         | (env2,b,pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1,uu____9441)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____9456 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange
                                in
                             let uu____9463 =
                               match b with
                               | LetBinder uu____9504 ->
                                   failwith "Impossible"
                               | LocalBinder (x,aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None
                                        ,uu____9572) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.None ) ->
                                         let uu____9626 =
                                           let uu____9635 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____9635, p1)  in
                                         FStar_Pervasives_Native.Some
                                           uu____9626
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.Some
                                        (sc,p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____9697,uu____9698) ->
                                              let tup2 =
                                                let uu____9700 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.parse_int "2")
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____9700
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____9704 =
                                                  let uu____9711 =
                                                    let uu____9712 =
                                                      let uu____9729 =
                                                        mk1
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let uu____9732 =
                                                        let uu____9743 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let uu____9752 =
                                                          let uu____9763 =
                                                            let uu____9772 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____9772
                                                             in
                                                          [uu____9763]  in
                                                        uu____9743 ::
                                                          uu____9752
                                                         in
                                                      (uu____9729,
                                                        uu____9732)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____9712
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____9711
                                                   in
                                                uu____9704
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range
                                                 in
                                              let p2 =
                                                let uu____9823 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____9823
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____9866,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____9868,pats)) ->
                                              let tupn =
                                                let uu____9911 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    ((Prims.parse_int "1") +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____9911
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____9923 =
                                                  let uu____9924 =
                                                    let uu____9941 =
                                                      mk1
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____9944 =
                                                      let uu____9955 =
                                                        let uu____9966 =
                                                          let uu____9975 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____9975
                                                           in
                                                        [uu____9966]  in
                                                      FStar_List.append args
                                                        uu____9955
                                                       in
                                                    (uu____9941, uu____9944)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____9924
                                                   in
                                                mk1 uu____9923  in
                                              let p2 =
                                                let uu____10023 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats [(p1, false)])))
                                                  uu____10023
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____10064 ->
                                              failwith "Impossible")
                                      in
                                   ((x, aq), sc_pat_opt1)
                                in
                             (match uu____9463 with
                              | (b1,sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest))
                     in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____10157,uu____10158,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____10180 =
                let uu____10181 = unparen e  in
                uu____10181.FStar_Parser_AST.tm  in
              match uu____10180 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____10191 ->
                  let uu____10192 = desugar_term_aq env e  in
                  (match uu____10192 with
                   | (head1,aq) ->
                       let uu____10205 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____10205, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____10212 ->
            let rec aux args aqs e =
              let uu____10289 =
                let uu____10290 = unparen e  in
                uu____10290.FStar_Parser_AST.tm  in
              match uu____10289 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____10308 = desugar_term_aq env t  in
                  (match uu____10308 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____10356 ->
                  let uu____10357 = desugar_term_aq env e  in
                  (match uu____10357 with
                   | (head1,aq) ->
                       let uu____10378 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____10378, (join_aqs (aq :: aqs))))
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
            let uu____10438 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____10438
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
            let uu____10490 = desugar_term_aq env t  in
            (match uu____10490 with
             | (tm,s) ->
                 let uu____10501 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____10501, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____10507 =
              let uu____10520 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____10520 then desugar_typ_aq else desugar_term_aq  in
            uu____10507 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____10575 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____10718  ->
                        match uu____10718 with
                        | (attr_opt,(p,def)) ->
                            let uu____10776 = is_app_pattern p  in
                            if uu____10776
                            then
                              let uu____10807 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____10807, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____10889 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____10889, def1)
                               | uu____10934 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____10972);
                                           FStar_Parser_AST.prange =
                                             uu____10973;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____11021 =
                                            let uu____11042 =
                                              let uu____11047 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____11047  in
                                            (uu____11042, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____11021, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____11138) ->
                                        if top_level
                                        then
                                          let uu____11173 =
                                            let uu____11194 =
                                              let uu____11199 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____11199  in
                                            (uu____11194, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____11173, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____11289 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____11320 =
                FStar_List.fold_left
                  (fun uu____11393  ->
                     fun uu____11394  ->
                       match (uu____11393, uu____11394) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____11502,uu____11503),uu____11504))
                           ->
                           let uu____11621 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____11647 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____11647 with
                                  | (env2,xx) ->
                                      let uu____11666 =
                                        let uu____11669 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____11669 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____11666))
                             | FStar_Util.Inr l ->
                                 let uu____11677 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (uu____11677, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____11621 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____11320 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____11825 =
                    match uu____11825 with
                    | (attrs_opt,(uu____11861,args,result_t),def) ->
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
                                let uu____11949 = is_comp_type env1 t  in
                                if uu____11949
                                then
                                  ((let uu____11951 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____11961 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____11961))
                                       in
                                    match uu____11951 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____11964 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____11966 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____11966))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____11964
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
                          | uu____11973 ->
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
                              let uu____11988 =
                                let uu____11989 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____11989
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____11988
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
                  let uu____12066 = desugar_term_aq env' body  in
                  (match uu____12066 with
                   | (body1,aq) ->
                       let uu____12079 =
                         let uu____12082 =
                           let uu____12083 =
                             let uu____12096 =
                               FStar_Syntax_Subst.close rec_bindings1 body1
                                in
                             ((is_rec, lbs1), uu____12096)  in
                           FStar_Syntax_Syntax.Tm_let uu____12083  in
                         FStar_All.pipe_left mk1 uu____12082  in
                       (uu____12079, aq))
               in
            let ds_non_rec attrs_opt pat t1 t2 =
              let attrs =
                match attrs_opt with
                | FStar_Pervasives_Native.None  -> []
                | FStar_Pervasives_Native.Some l ->
                    FStar_List.map (desugar_term env) l
                 in
              let t11 = desugar_term env t1  in
              let uu____12169 =
                desugar_binding_pat_maybe_top top_level env pat  in
              match uu____12169 with
              | (env1,binder,pat1) ->
                  let uu____12191 =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let uu____12217 = desugar_term_aq env1 t2  in
                        (match uu____12217 with
                         | (body1,aq) ->
                             let fv =
                               let uu____12231 =
                                 FStar_Syntax_Util.incr_delta_qualifier t11
                                  in
                               FStar_Syntax_Syntax.lid_as_fv l uu____12231
                                 FStar_Pervasives_Native.None
                                in
                             let uu____12232 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t11,
                                            (t11.FStar_Syntax_Syntax.pos))]),
                                      body1))
                                in
                             (uu____12232, aq))
                    | LocalBinder (x,uu____12262) ->
                        let uu____12263 = desugar_term_aq env1 t2  in
                        (match uu____12263 with
                         | (body1,aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | ({
                                    FStar_Syntax_Syntax.v =
                                      FStar_Syntax_Syntax.Pat_wild
                                      uu____12277;
                                    FStar_Syntax_Syntax.p = uu____12278;_},uu____12279)::[]
                                   -> body1
                               | uu____12292 ->
                                   let uu____12295 =
                                     let uu____12302 =
                                       let uu____12303 =
                                         let uu____12326 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         let uu____12329 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1
                                            in
                                         (uu____12326, uu____12329)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____12303
                                        in
                                     FStar_Syntax_Syntax.mk uu____12302  in
                                   uu____12295 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range
                                in
                             let uu____12369 =
                               let uu____12372 =
                                 let uu____12373 =
                                   let uu____12386 =
                                     let uu____12389 =
                                       let uu____12390 =
                                         FStar_Syntax_Syntax.mk_binder x  in
                                       [uu____12390]  in
                                     FStar_Syntax_Subst.close uu____12389
                                       body2
                                      in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t11,
                                           (t11.FStar_Syntax_Syntax.pos))]),
                                     uu____12386)
                                    in
                                 FStar_Syntax_Syntax.Tm_let uu____12373  in
                               FStar_All.pipe_left mk1 uu____12372  in
                             (uu____12369, aq))
                     in
                  (match uu____12191 with | (tm,aq) -> (tm, aq))
               in
            let uu____12449 = FStar_List.hd lbs  in
            (match uu____12449 with
             | (attrs,(head_pat,defn)) ->
                 let uu____12493 = is_rec || (is_app_pattern head_pat)  in
                 if uu____12493
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____12506 =
                let uu____12507 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____12507  in
              mk1 uu____12506  in
            let uu____12508 = desugar_term_aq env t1  in
            (match uu____12508 with
             | (t1',aq1) ->
                 let uu____12519 = desugar_term_aq env t2  in
                 (match uu____12519 with
                  | (t2',aq2) ->
                      let uu____12530 = desugar_term_aq env t3  in
                      (match uu____12530 with
                       | (t3',aq3) ->
                           let uu____12541 =
                             let uu____12542 =
                               let uu____12543 =
                                 let uu____12566 =
                                   let uu____12583 =
                                     let uu____12598 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t2.FStar_Parser_AST.range
                                        in
                                     (uu____12598,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____12611 =
                                     let uu____12628 =
                                       let uu____12643 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t3.FStar_Parser_AST.range
                                          in
                                       (uu____12643,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____12628]  in
                                   uu____12583 :: uu____12611  in
                                 (t1', uu____12566)  in
                               FStar_Syntax_Syntax.Tm_match uu____12543  in
                             mk1 uu____12542  in
                           (uu____12541, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____12836 =
              match uu____12836 with
              | (pat,wopt,b) ->
                  let uu____12858 = desugar_match_pat env pat  in
                  (match uu____12858 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____12889 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____12889
                          in
                       let uu____12894 = desugar_term_aq env1 b  in
                       (match uu____12894 with
                        | (b1,aq) ->
                            let uu____12907 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____12907, aq)))
               in
            let uu____12912 = desugar_term_aq env e  in
            (match uu____12912 with
             | (e1,aq) ->
                 let uu____12923 =
                   let uu____12954 =
                     let uu____12987 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____12987 FStar_List.unzip  in
                   FStar_All.pipe_right uu____12954
                     (fun uu____13117  ->
                        match uu____13117 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____12923 with
                  | (brs,aqs) ->
                      let uu____13336 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____13336, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____13370 =
              let uu____13391 = is_comp_type env t  in
              if uu____13391
              then
                let comp = desugar_comp t.FStar_Parser_AST.range env t  in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____13442 = desugar_term_aq env t  in
                 match uu____13442 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____13370 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____13534 = desugar_term_aq env e  in
                 (match uu____13534 with
                  | (e1,aq) ->
                      let uu____13545 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____13545, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____13584,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____13625 = FStar_List.hd fields  in
              match uu____13625 with | (f,uu____13637) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____13683  ->
                        match uu____13683 with
                        | (g,uu____13689) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____13695,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____13709 =
                         let uu____13714 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____13714)
                          in
                       FStar_Errors.raise_error uu____13709
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
                  let uu____13722 =
                    let uu____13733 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____13764  ->
                              match uu____13764 with
                              | (f,uu____13774) ->
                                  let uu____13775 =
                                    let uu____13776 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____13776
                                     in
                                  (uu____13775, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____13733)  in
                  FStar_Parser_AST.Construct uu____13722
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____13794 =
                      let uu____13795 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____13795  in
                    FStar_Parser_AST.mk_term uu____13794
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____13797 =
                      let uu____13810 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____13840  ->
                                match uu____13840 with
                                | (f,uu____13850) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____13810)  in
                    FStar_Parser_AST.Record uu____13797  in
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
            let uu____13910 = desugar_term_aq env recterm1  in
            (match uu____13910 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____13926;
                         FStar_Syntax_Syntax.vars = uu____13927;_},args)
                      ->
                      let uu____13953 =
                        let uu____13954 =
                          let uu____13955 =
                            let uu____13972 =
                              let uu____13975 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____13976 =
                                let uu____13979 =
                                  let uu____13980 =
                                    let uu____13987 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____13987)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____13980
                                   in
                                FStar_Pervasives_Native.Some uu____13979  in
                              FStar_Syntax_Syntax.fvar uu____13975
                                FStar_Syntax_Syntax.delta_constant
                                uu____13976
                               in
                            (uu____13972, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____13955  in
                        FStar_All.pipe_left mk1 uu____13954  in
                      (uu____13953, s)
                  | uu____14016 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____14020 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____14020 with
              | (constrname,is_rec) ->
                  let uu____14035 = desugar_term_aq env e  in
                  (match uu____14035 with
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
                       let uu____14053 =
                         let uu____14054 =
                           let uu____14055 =
                             let uu____14072 =
                               let uu____14075 =
                                 let uu____14076 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____14076
                                  in
                               FStar_Syntax_Syntax.fvar uu____14075
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1")) qual
                                in
                             let uu____14077 =
                               let uu____14088 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____14088]  in
                             (uu____14072, uu____14077)  in
                           FStar_Syntax_Syntax.Tm_app uu____14055  in
                         FStar_All.pipe_left mk1 uu____14054  in
                       (uu____14053, s))))
        | FStar_Parser_AST.NamedTyp (uu____14125,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____14134 =
              let uu____14135 = FStar_Syntax_Subst.compress tm  in
              uu____14135.FStar_Syntax_Syntax.n  in
            (match uu____14134 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____14143 =
                   let uu___291_14144 =
                     let uu____14145 =
                       let uu____14146 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____14146  in
                     FStar_Syntax_Util.exp_string uu____14145  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___291_14144.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___291_14144.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____14143, noaqs)
             | uu____14147 ->
                 let uu____14148 =
                   let uu____14153 =
                     let uu____14154 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.strcat "VQuote, expected an fvar, got: "
                       uu____14154
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____14153)  in
                 FStar_Errors.raise_error uu____14148
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____14160 = desugar_term_aq env e  in
            (match uu____14160 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____14172 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____14172, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____14177 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____14178 =
              let uu____14179 =
                let uu____14186 = desugar_term env e  in (bv, uu____14186)
                 in
              [uu____14179]  in
            (uu____14177, uu____14178)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____14211 =
              let uu____14212 =
                let uu____14213 =
                  let uu____14220 = desugar_term env e  in (uu____14220, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____14213  in
              FStar_All.pipe_left mk1 uu____14212  in
            (uu____14211, noaqs)
        | uu____14225 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____14226 = desugar_formula env top  in
            (uu____14226, noaqs)
        | uu____14227 ->
            let uu____14228 =
              let uu____14233 =
                let uu____14234 = FStar_Parser_AST.term_to_string top  in
                Prims.strcat "Unexpected term: " uu____14234  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____14233)  in
            FStar_Errors.raise_error uu____14228 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____14240 -> false
    | uu____14249 -> true

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
           (fun uu____14286  ->
              match uu____14286 with
              | (a,imp) ->
                  let uu____14299 = desugar_term env a  in
                  arg_withimp_e imp uu____14299))

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
        let is_requires uu____14331 =
          match uu____14331 with
          | (t1,uu____14337) ->
              let uu____14338 =
                let uu____14339 = unparen t1  in
                uu____14339.FStar_Parser_AST.tm  in
              (match uu____14338 with
               | FStar_Parser_AST.Requires uu____14340 -> true
               | uu____14347 -> false)
           in
        let is_ensures uu____14357 =
          match uu____14357 with
          | (t1,uu____14363) ->
              let uu____14364 =
                let uu____14365 = unparen t1  in
                uu____14365.FStar_Parser_AST.tm  in
              (match uu____14364 with
               | FStar_Parser_AST.Ensures uu____14366 -> true
               | uu____14373 -> false)
           in
        let is_app head1 uu____14388 =
          match uu____14388 with
          | (t1,uu____14394) ->
              let uu____14395 =
                let uu____14396 = unparen t1  in
                uu____14396.FStar_Parser_AST.tm  in
              (match uu____14395 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____14398;
                      FStar_Parser_AST.level = uu____14399;_},uu____14400,uu____14401)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____14402 -> false)
           in
        let is_smt_pat uu____14412 =
          match uu____14412 with
          | (t1,uu____14418) ->
              let uu____14419 =
                let uu____14420 = unparen t1  in
                uu____14420.FStar_Parser_AST.tm  in
              (match uu____14419 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____14423);
                             FStar_Parser_AST.range = uu____14424;
                             FStar_Parser_AST.level = uu____14425;_},uu____14426)::uu____14427::[])
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
                             FStar_Parser_AST.range = uu____14466;
                             FStar_Parser_AST.level = uu____14467;_},uu____14468)::uu____14469::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
               | uu____14494 -> false)
           in
        let is_decreases = is_app "decreases"  in
        let pre_process_comp_typ t1 =
          let uu____14526 = head_and_args t1  in
          match uu____14526 with
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
                   let thunk_ens uu____14624 =
                     match uu____14624 with
                     | (e,i) ->
                         let uu____14635 = thunk_ens_ e  in (uu____14635, i)
                      in
                   let fail_lemma uu____14647 =
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
                         let uu____14727 =
                           let uu____14734 =
                             let uu____14741 = thunk_ens ens  in
                             [uu____14741; nil_pat]  in
                           req_true :: uu____14734  in
                         unit_tm :: uu____14727
                     | req::ens::[] when
                         (is_requires req) && (is_ensures ens) ->
                         let uu____14788 =
                           let uu____14795 =
                             let uu____14802 = thunk_ens ens  in
                             [uu____14802; nil_pat]  in
                           req :: uu____14795  in
                         unit_tm :: uu____14788
                     | ens::smtpat::[] when
                         (((let uu____14851 = is_requires ens  in
                            Prims.op_Negation uu____14851) &&
                             (let uu____14853 = is_smt_pat ens  in
                              Prims.op_Negation uu____14853))
                            &&
                            (let uu____14855 = is_decreases ens  in
                             Prims.op_Negation uu____14855))
                           && (is_smt_pat smtpat)
                         ->
                         let uu____14856 =
                           let uu____14863 =
                             let uu____14870 = thunk_ens ens  in
                             [uu____14870; smtpat]  in
                           req_true :: uu____14863  in
                         unit_tm :: uu____14856
                     | ens::dec::[] when
                         (is_ensures ens) && (is_decreases dec) ->
                         let uu____14917 =
                           let uu____14924 =
                             let uu____14931 = thunk_ens ens  in
                             [uu____14931; nil_pat; dec]  in
                           req_true :: uu____14924  in
                         unit_tm :: uu____14917
                     | ens::dec::smtpat::[] when
                         ((is_ensures ens) && (is_decreases dec)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____14991 =
                           let uu____14998 =
                             let uu____15005 = thunk_ens ens  in
                             [uu____15005; smtpat; dec]  in
                           req_true :: uu____14998  in
                         unit_tm :: uu____14991
                     | req::ens::dec::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_decreases dec)
                         ->
                         let uu____15065 =
                           let uu____15072 =
                             let uu____15079 = thunk_ens ens  in
                             [uu____15079; nil_pat; dec]  in
                           req :: uu____15072  in
                         unit_tm :: uu____15065
                     | req::ens::smtpat::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____15139 =
                           let uu____15146 =
                             let uu____15153 = thunk_ens ens  in
                             [uu____15153; smtpat]  in
                           req :: uu____15146  in
                         unit_tm :: uu____15139
                     | req::ens::dec::smtpat::[] when
                         (((is_requires req) && (is_ensures ens)) &&
                            (is_smt_pat smtpat))
                           && (is_decreases dec)
                         ->
                         let uu____15218 =
                           let uu____15225 =
                             let uu____15232 = thunk_ens ens  in
                             [uu____15232; dec; smtpat]  in
                           req :: uu____15225  in
                         unit_tm :: uu____15218
                     | _other -> fail_lemma ()  in
                   let head_and_attributes =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) lemma
                      in
                   (head_and_attributes, args1)
               | FStar_Parser_AST.Name l when
                   FStar_Syntax_DsEnv.is_effect_name env l ->
                   let uu____15294 =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) l
                      in
                   (uu____15294, args)
               | FStar_Parser_AST.Name l when
                   (let uu____15322 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____15322
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   let uu____15323 =
                     let uu____15330 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_Tot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____15330, [])  in
                   (uu____15323, args)
               | FStar_Parser_AST.Name l when
                   (let uu____15348 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____15348
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                   ->
                   let uu____15349 =
                     let uu____15356 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_GTot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____15356, [])  in
                   (uu____15349, args)
               | FStar_Parser_AST.Name l when
                   (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                      ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                     || ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                   ->
                   let uu____15372 =
                     let uu____15379 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_Tot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____15379, [])  in
                   (uu____15372, [(t1, FStar_Parser_AST.Nothing)])
               | uu____15402 ->
                   let default_effect =
                     let uu____15404 = FStar_Options.ml_ish ()  in
                     if uu____15404
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____15407 =
                           FStar_Options.warn_default_effects ()  in
                         if uu____15407
                         then
                           FStar_Errors.log_issue
                             head1.FStar_Parser_AST.range
                             (FStar_Errors.Warning_UseDefaultEffect,
                               "Using default effect Tot")
                         else ());
                        FStar_Parser_Const.effect_Tot_lid)
                      in
                   let uu____15409 =
                     let uu____15416 =
                       FStar_Ident.set_lid_range default_effect
                         head1.FStar_Parser_AST.range
                        in
                     (uu____15416, [])  in
                   (uu____15409, [(t1, FStar_Parser_AST.Nothing)]))
           in
        let uu____15439 = pre_process_comp_typ t  in
        match uu____15439 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____15488 =
                  let uu____15493 =
                    let uu____15494 = FStar_Syntax_Print.lid_to_string eff
                       in
                    FStar_Util.format1 "Not enough args to effect %s"
                      uu____15494
                     in
                  (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____15493)  in
                fail1 uu____15488)
             else ();
             (let is_universe uu____15505 =
                match uu____15505 with
                | (uu____15510,imp) -> imp = FStar_Parser_AST.UnivApp  in
              let uu____15512 = FStar_Util.take is_universe args  in
              match uu____15512 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____15571  ->
                         match uu____15571 with
                         | (u,imp) -> desugar_universe u) universes
                     in
                  let uu____15578 =
                    let uu____15593 = FStar_List.hd args1  in
                    let uu____15602 = FStar_List.tl args1  in
                    (uu____15593, uu____15602)  in
                  (match uu____15578 with
                   | (result_arg,rest) ->
                       let result_typ =
                         desugar_typ env
                           (FStar_Pervasives_Native.fst result_arg)
                          in
                       let rest1 = desugar_args env rest  in
                       let uu____15657 =
                         let is_decrease uu____15695 =
                           match uu____15695 with
                           | (t1,uu____15705) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.pos = uu____15715;
                                       FStar_Syntax_Syntax.vars = uu____15716;_},uu____15717::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.decreases_lid
                                | uu____15756 -> false)
                            in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease)
                          in
                       (match uu____15657 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____15872  ->
                                      match uu____15872 with
                                      | (t1,uu____15882) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____15891,(arg,uu____15893)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____15932 -> failwith "impos")))
                               in
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
                                | uu____15949 -> false  in
                              (((is_empty decreases_clause) &&
                                  (is_empty rest2))
                                 && (is_empty cattributes))
                                && (is_empty universes1)
                               in
                            let uu____15960 =
                              no_additional_args &&
                                (FStar_Ident.lid_equals eff
                                   FStar_Parser_Const.effect_Tot_lid)
                               in
                            if uu____15960
                            then FStar_Syntax_Syntax.mk_Total result_typ
                            else
                              (let uu____15964 =
                                 no_additional_args &&
                                   (FStar_Ident.lid_equals eff
                                      FStar_Parser_Const.effect_GTot_lid)
                                  in
                               if uu____15964
                               then FStar_Syntax_Syntax.mk_GTotal result_typ
                               else
                                 (let flags1 =
                                    let uu____15971 =
                                      FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_Lemma_lid
                                       in
                                    if uu____15971
                                    then [FStar_Syntax_Syntax.LEMMA]
                                    else
                                      (let uu____15975 =
                                         FStar_Ident.lid_equals eff
                                           FStar_Parser_Const.effect_Tot_lid
                                          in
                                       if uu____15975
                                       then [FStar_Syntax_Syntax.TOTAL]
                                       else
                                         (let uu____15979 =
                                            FStar_Ident.lid_equals eff
                                              FStar_Parser_Const.effect_ML_lid
                                             in
                                          if uu____15979
                                          then [FStar_Syntax_Syntax.MLEFFECT]
                                          else
                                            (let uu____15983 =
                                               FStar_Ident.lid_equals eff
                                                 FStar_Parser_Const.effect_GTot_lid
                                                in
                                             if uu____15983
                                             then
                                               [FStar_Syntax_Syntax.SOMETRIVIAL]
                                             else [])))
                                     in
                                  let flags2 =
                                    FStar_List.append flags1 cattributes  in
                                  let rest3 =
                                    let uu____16001 =
                                      FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_Lemma_lid
                                       in
                                    if uu____16001
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
                                                  let uu____16090 =
                                                    FStar_Ident.set_lid_range
                                                      FStar_Parser_Const.pattern_lid
                                                      pat.FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_Syntax.fvar
                                                    uu____16090
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
                                            | uu____16111 -> pat  in
                                          let uu____16112 =
                                            let uu____16123 =
                                              let uu____16134 =
                                                let uu____16143 =
                                                  FStar_Syntax_Syntax.mk
                                                    (FStar_Syntax_Syntax.Tm_meta
                                                       (pat1,
                                                         (FStar_Syntax_Syntax.Meta_desugared
                                                            FStar_Syntax_Syntax.Meta_smt_pat)))
                                                    FStar_Pervasives_Native.None
                                                    pat1.FStar_Syntax_Syntax.pos
                                                   in
                                                (uu____16143, aq)  in
                                              [uu____16134]  in
                                            ens :: uu____16123  in
                                          req :: uu____16112
                                      | uu____16184 -> rest2
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
        | uu____16208 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___292_16229 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___292_16229.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___292_16229.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___293_16271 = b  in
             {
               FStar_Parser_AST.b = (uu___293_16271.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___293_16271.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___293_16271.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____16334 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____16334)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____16347 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____16347 with
             | (env1,a1) ->
                 let a2 =
                   let uu___294_16357 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___294_16357.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___294_16357.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____16383 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____16397 =
                     let uu____16400 =
                       let uu____16401 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____16401]  in
                     no_annot_abs uu____16400 body2  in
                   FStar_All.pipe_left setpos uu____16397  in
                 let uu____16422 =
                   let uu____16423 =
                     let uu____16440 =
                       let uu____16443 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____16443
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____16444 =
                       let uu____16455 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____16455]  in
                     (uu____16440, uu____16444)  in
                   FStar_Syntax_Syntax.Tm_app uu____16423  in
                 FStar_All.pipe_left mk1 uu____16422)
        | uu____16494 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____16574 = q (rest, pats, body)  in
              let uu____16581 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____16574 uu____16581
                FStar_Parser_AST.Formula
               in
            let uu____16582 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____16582 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____16591 -> failwith "impossible"  in
      let uu____16594 =
        let uu____16595 = unparen f  in uu____16595.FStar_Parser_AST.tm  in
      match uu____16594 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____16602,uu____16603) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____16614,uu____16615) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____16646 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____16646
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____16682 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____16682
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____16725 -> desugar_term env f

and (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                FStar_Pervasives_Native.tuple2 Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bs  ->
      let uu____16730 =
        FStar_List.fold_left
          (fun uu____16763  ->
             fun b  ->
               match uu____16763 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___295_16807 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___295_16807.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___295_16807.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___295_16807.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____16822 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____16822 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___296_16840 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___296_16840.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___296_16840.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____16841 =
                               let uu____16848 =
                                 let uu____16853 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____16853)  in
                               uu____16848 :: out  in
                             (env2, uu____16841))
                    | uu____16864 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____16730 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

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
          let uu____16935 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____16935)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____16940 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____16940)
      | FStar_Parser_AST.TVariable x ->
          let uu____16944 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____16944)
      | FStar_Parser_AST.NoName t ->
          let uu____16948 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____16948)
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
      fun uu___249_16956  ->
        match uu___249_16956 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____16978 = FStar_Syntax_Syntax.null_binder k  in
            (uu____16978, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____16995 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____16995 with
             | (env1,a1) ->
                 let uu____17012 =
                   let uu____17019 = trans_aqual env1 imp  in
                   ((let uu___297_17025 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___297_17025.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___297_17025.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____17019)
                    in
                 (uu____17012, env1))

and (trans_aqual :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___250_17033  ->
      match uu___250_17033 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____17037 =
            let uu____17038 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____17038  in
          FStar_Pervasives_Native.Some uu____17037
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
               (fun uu___251_17074  ->
                  match uu___251_17074 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____17075 -> false))
           in
        let quals2 q =
          let uu____17088 =
            (let uu____17091 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____17091) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____17088
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____17105 = FStar_Ident.range_of_lid disc_name  in
                let uu____17106 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____17105;
                  FStar_Syntax_Syntax.sigquals = uu____17106;
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
            let uu____17145 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____17183  ->
                        match uu____17183 with
                        | (x,uu____17193) ->
                            let uu____17198 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____17198 with
                             | (field_name,uu____17206) ->
                                 let only_decl =
                                   ((let uu____17210 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____17210)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____17212 =
                                        let uu____17213 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____17213.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____17212)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____17229 =
                                       FStar_List.filter
                                         (fun uu___252_17233  ->
                                            match uu___252_17233 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____17234 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____17229
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___253_17247  ->
                                             match uu___253_17247 with
                                             | FStar_Syntax_Syntax.NoExtract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____17248 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____17250 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____17250;
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____17255 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____17255
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          (FStar_Syntax_Syntax.Delta_equational_at_level
                                             (Prims.parse_int "1"))
                                      else
                                        FStar_Syntax_Syntax.Delta_equational_at_level
                                          (Prims.parse_int "1")
                                       in
                                    let lb =
                                      let uu____17260 =
                                        let uu____17265 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____17265  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____17260;
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
                                      let uu____17269 =
                                        let uu____17270 =
                                          let uu____17277 =
                                            let uu____17280 =
                                              let uu____17281 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____17281
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____17280]  in
                                          ((false, [lb]), uu____17277)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____17270
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____17269;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____17145 FStar_List.flatten
  
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
            (lid,uu____17325,t,uu____17327,n1,uu____17329) when
            let uu____17334 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____17334 ->
            let uu____17335 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____17335 with
             | (formals,uu____17353) ->
                 (match formals with
                  | [] -> []
                  | uu____17382 ->
                      let filter_records uu___254_17398 =
                        match uu___254_17398 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____17401,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____17413 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____17415 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____17415 with
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
                      let uu____17425 = FStar_Util.first_N n1 formals  in
                      (match uu____17425 with
                       | (uu____17454,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____17488 -> []
  
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
                    let uu____17566 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____17566
                    then
                      let uu____17569 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____17569
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____17572 =
                      let uu____17577 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____17577  in
                    let uu____17578 =
                      if FStar_Util.is_some kopt
                      then
                        let uu____17583 =
                          let uu____17586 =
                            FStar_All.pipe_right kopt FStar_Util.must  in
                          FStar_Syntax_Syntax.mk_Total uu____17586  in
                        FStar_Syntax_Util.arrow typars uu____17583
                      else FStar_Syntax_Syntax.tun  in
                    let uu____17590 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____17572;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____17578;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____17590;
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
          let tycon_id uu___255_17641 =
            match uu___255_17641 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____17643,uu____17644) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____17654,uu____17655,uu____17656) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____17666,uu____17667,uu____17668) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____17698,uu____17699,uu____17700) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____17744) ->
                let uu____17745 =
                  let uu____17746 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____17746  in
                FStar_Parser_AST.mk_term uu____17745 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____17748 =
                  let uu____17749 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____17749  in
                FStar_Parser_AST.mk_term uu____17748 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____17751) ->
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
              | uu____17782 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____17790 =
                     let uu____17791 =
                       let uu____17798 = binder_to_term b  in
                       (out, uu____17798, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____17791  in
                   FStar_Parser_AST.mk_term uu____17790
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___256_17810 =
            match uu___256_17810 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____17866  ->
                       match uu____17866 with
                       | (x,t,uu____17877) ->
                           let uu____17882 =
                             let uu____17883 =
                               let uu____17888 =
                                 FStar_Syntax_Util.mangle_field_name x  in
                               (uu____17888, t)  in
                             FStar_Parser_AST.Annotated uu____17883  in
                           FStar_Parser_AST.mk_binder uu____17882
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____17890 =
                    let uu____17891 =
                      let uu____17892 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____17892  in
                    FStar_Parser_AST.mk_term uu____17891
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____17890 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let uu____17896 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____17923  ->
                          match uu____17923 with
                          | (x,uu____17933,uu____17934) ->
                              FStar_Syntax_Util.unmangle_field_name x))
                   in
                ((FStar_Parser_AST.TyconVariant
                    (id1, parms, kopt,
                      [(constrName, (FStar_Pervasives_Native.Some constrTyp),
                         FStar_Pervasives_Native.None, false)])),
                  uu____17896)
            | uu____17987 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___257_18026 =
            match uu___257_18026 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____18050 = typars_of_binders _env binders  in
                (match uu____18050 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____18086 =
                         let uu____18087 =
                           let uu____18088 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____18088  in
                         FStar_Parser_AST.mk_term uu____18087
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____18086 binders  in
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
            | uu____18099 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____18141 =
              FStar_List.fold_left
                (fun uu____18175  ->
                   fun uu____18176  ->
                     match (uu____18175, uu____18176) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____18245 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____18245 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____18141 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____18336 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____18336
                | uu____18337 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____18345 = desugar_abstract_tc quals env [] tc  in
              (match uu____18345 with
               | (uu____18358,uu____18359,se,uu____18361) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____18364,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____18381 =
                                 let uu____18382 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____18382  in
                               if uu____18381
                               then
                                 let uu____18383 =
                                   let uu____18388 =
                                     let uu____18389 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____18389
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____18388)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____18383
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
                           | uu____18398 ->
                               let uu____18399 =
                                 let uu____18406 =
                                   let uu____18407 =
                                     let uu____18422 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____18422)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____18407
                                    in
                                 FStar_Syntax_Syntax.mk uu____18406  in
                               uu____18399 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___298_18438 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___298_18438.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___298_18438.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___298_18438.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____18439 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____18442 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____18442
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____18455 = typars_of_binders env binders  in
              (match uu____18455 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____18489 =
                           FStar_Util.for_some
                             (fun uu___258_18491  ->
                                match uu___258_18491 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____18492 -> false) quals
                            in
                         if uu____18489
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____18497 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____18497
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____18502 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___259_18506  ->
                               match uu___259_18506 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____18507 -> false))
                        in
                     if uu____18502
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____18516 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____18516
                     then
                       let uu____18519 =
                         let uu____18526 =
                           let uu____18527 = unparen t  in
                           uu____18527.FStar_Parser_AST.tm  in
                         match uu____18526 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____18548 =
                               match FStar_List.rev args with
                               | (last_arg,uu____18578)::args_rev ->
                                   let uu____18590 =
                                     let uu____18591 = unparen last_arg  in
                                     uu____18591.FStar_Parser_AST.tm  in
                                   (match uu____18590 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____18619 -> ([], args))
                               | uu____18628 -> ([], args)  in
                             (match uu____18548 with
                              | (cattributes,args1) ->
                                  let uu____18667 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____18667))
                         | uu____18678 -> (t, [])  in
                       match uu____18519 with
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
                                  (fun uu___260_18700  ->
                                     match uu___260_18700 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____18701 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____18708)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____18732 = tycon_record_as_variant trec  in
              (match uu____18732 with
               | (t,fs) ->
                   let uu____18749 =
                     let uu____18752 =
                       let uu____18753 =
                         let uu____18762 =
                           let uu____18765 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____18765  in
                         (uu____18762, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____18753  in
                     uu____18752 :: quals  in
                   desugar_tycon env d uu____18749 [t])
          | uu____18770::uu____18771 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____18938 = et  in
                match uu____18938 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____19163 ->
                         let trec = tc  in
                         let uu____19187 = tycon_record_as_variant trec  in
                         (match uu____19187 with
                          | (t,fs) ->
                              let uu____19246 =
                                let uu____19249 =
                                  let uu____19250 =
                                    let uu____19259 =
                                      let uu____19262 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____19262  in
                                    (uu____19259, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____19250
                                   in
                                uu____19249 :: quals1  in
                              collect_tcs uu____19246 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____19349 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____19349 with
                          | (env2,uu____19409,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____19558 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____19558 with
                          | (env2,uu____19618,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____19743 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____19790 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____19790 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___262_20295  ->
                             match uu___262_20295 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____20360,uu____20361);
                                    FStar_Syntax_Syntax.sigrng = uu____20362;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____20363;
                                    FStar_Syntax_Syntax.sigmeta = uu____20364;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____20365;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____20428 =
                                     typars_of_binders env1 binders  in
                                   match uu____20428 with
                                   | (env2,tpars1) ->
                                       let uu____20455 =
                                         push_tparams env2 tpars1  in
                                       (match uu____20455 with
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
                                 let uu____20484 =
                                   let uu____20503 =
                                     mk_typ_abbrev id1 uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____20503)
                                    in
                                 [uu____20484]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____20563);
                                    FStar_Syntax_Syntax.sigrng = uu____20564;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____20566;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____20567;_},constrs,tconstr,quals1)
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
                                 let uu____20665 = push_tparams env1 tpars
                                    in
                                 (match uu____20665 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____20732  ->
                                             match uu____20732 with
                                             | (x,uu____20744) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____20748 =
                                        let uu____20775 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____20883  ->
                                                  match uu____20883 with
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
                                                        let uu____20937 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____20937
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
                                                                uu___261_20948
                                                                 ->
                                                                match uu___261_20948
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____20960
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____20968 =
                                                        let uu____20987 =
                                                          let uu____20988 =
                                                            let uu____20989 =
                                                              let uu____21004
                                                                =
                                                                let uu____21005
                                                                  =
                                                                  let uu____21008
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____21008
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____21005
                                                                 in
                                                              (name, univs1,
                                                                uu____21004,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____20989
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____20988;
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
                                                          uu____20987)
                                                         in
                                                      (name, uu____20968)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____20775
                                         in
                                      (match uu____20748 with
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
                             | uu____21223 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____21349  ->
                             match uu____21349 with
                             | (name_doc,uu____21375,uu____21376) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____21448  ->
                             match uu____21448 with
                             | (uu____21467,uu____21468,se) -> se))
                      in
                   let uu____21494 =
                     let uu____21501 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____21501 rng
                      in
                   (match uu____21494 with
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
                               (fun uu____21563  ->
                                  match uu____21563 with
                                  | (uu____21584,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____21631,tps,k,uu____21634,constrs)
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
                                  | uu____21653 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____21670  ->
                                 match uu____21670 with
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
      let uu____21713 =
        FStar_List.fold_left
          (fun uu____21748  ->
             fun b  ->
               match uu____21748 with
               | (env1,binders1) ->
                   let uu____21792 = desugar_binder env1 b  in
                   (match uu____21792 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____21815 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____21815 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____21868 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____21713 with
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
          let uu____21969 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___263_21974  ->
                    match uu___263_21974 with
                    | FStar_Syntax_Syntax.Reflectable uu____21975 -> true
                    | uu____21976 -> false))
             in
          if uu____21969
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____21979 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____21979
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
      let uu____22011 = FStar_Syntax_Util.head_and_args at1  in
      match uu____22011 with
      | (hd1,args) ->
          let uu____22062 =
            let uu____22077 =
              let uu____22078 = FStar_Syntax_Subst.compress hd1  in
              uu____22078.FStar_Syntax_Syntax.n  in
            (uu____22077, args)  in
          (match uu____22062 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(a1,uu____22101)::[]) when
               (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr)
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.fail_lax_attr)
               ->
               let uu____22136 =
                 let uu____22141 =
                   let uu____22150 =
                     FStar_Syntax_Embeddings.e_list
                       FStar_Syntax_Embeddings.e_int
                      in
                   FStar_Syntax_Embeddings.unembed uu____22150 a1  in
                 uu____22141 true FStar_Syntax_Embeddings.id_norm_cb  in
               (match uu____22136 with
                | FStar_Pervasives_Native.Some es when
                    (FStar_List.length es) > (Prims.parse_int "0") ->
                    let b =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.fail_lax_attr
                       in
                    let uu____22175 =
                      let uu____22182 =
                        FStar_List.map FStar_BigInt.to_int_fs es  in
                      (uu____22182, b)  in
                    FStar_Pervasives_Native.Some uu____22175
                | uu____22193 ->
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
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____22235) when
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
           | uu____22264 -> FStar_Pervasives_Native.None)
  
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
                  let uu____22433 = desugar_binders monad_env eff_binders  in
                  match uu____22433 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let for_free =
                        let uu____22472 =
                          let uu____22473 =
                            let uu____22482 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____22482  in
                          FStar_List.length uu____22473  in
                        uu____22472 = (Prims.parse_int "1")  in
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
                            (uu____22528,uu____22529,(FStar_Parser_AST.TyconAbbrev
                                                      (name,uu____22531,uu____22532,uu____22533),uu____22534)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____22567 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____22568 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____22580 = name_of_eff_decl decl  in
                             FStar_List.mem uu____22580 mandatory_members)
                          eff_decls
                         in
                      (match uu____22568 with
                       | (mandatory_members_decls,actions) ->
                           let uu____22597 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____22626  ->
                                     fun decl  ->
                                       match uu____22626 with
                                       | (env2,out) ->
                                           let uu____22646 =
                                             desugar_decl env2 decl  in
                                           (match uu____22646 with
                                            | (env3,ses) ->
                                                let uu____22659 =
                                                  let uu____22662 =
                                                    FStar_List.hd ses  in
                                                  uu____22662 :: out  in
                                                (env3, uu____22659)))
                                  (env1, []))
                              in
                           (match uu____22597 with
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
                                              (uu____22731,uu____22732,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____22735,
                                                 {
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.Construct
                                                     (uu____22736,(def,uu____22738)::
                                                      (cps_type,uu____22740)::[]);
                                                   FStar_Parser_AST.range =
                                                     uu____22741;
                                                   FStar_Parser_AST.level =
                                                     uu____22742;_}),doc1)::[])
                                              when Prims.op_Negation for_free
                                              ->
                                              let uu____22794 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____22794 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____22832 =
                                                     let uu____22833 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____22834 =
                                                       let uu____22835 =
                                                         desugar_term env3
                                                           def
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____22835
                                                        in
                                                     let uu____22842 =
                                                       let uu____22843 =
                                                         desugar_typ env3
                                                           cps_type
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____22843
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____22833;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____22834;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____22842
                                                     }  in
                                                   (uu____22832, doc1))
                                          | FStar_Parser_AST.Tycon
                                              (uu____22852,uu____22853,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____22856,defn),doc1)::[])
                                              when for_free ->
                                              let uu____22891 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____22891 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____22929 =
                                                     let uu____22930 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____22931 =
                                                       let uu____22932 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____22932
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____22930;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____22931;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____22929, doc1))
                                          | uu____22941 ->
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
                                    let uu____22973 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____22973
                                     in
                                  let uu____22974 =
                                    let uu____22975 =
                                      FStar_Syntax_DsEnv.fail_or env2
                                        (FStar_Syntax_DsEnv.try_lookup_definition
                                           env2) l
                                       in
                                    FStar_All.pipe_left
                                      (FStar_Syntax_Subst.close binders1)
                                      uu____22975
                                     in
                                  ([], uu____22974)  in
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
                                      let uu____22992 =
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      ([], uu____22992)  in
                                    let uu____22999 =
                                      let uu____23000 =
                                        let uu____23001 =
                                          let uu____23002 = lookup1 "repr"
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____23002
                                           in
                                        let uu____23011 = lookup1 "return"
                                           in
                                        let uu____23012 = lookup1 "bind"  in
                                        let uu____23013 =
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
                                            uu____23001;
                                          FStar_Syntax_Syntax.return_repr =
                                            uu____23011;
                                          FStar_Syntax_Syntax.bind_repr =
                                            uu____23012;
                                          FStar_Syntax_Syntax.actions =
                                            actions1;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            uu____23013
                                        }  in
                                      FStar_Syntax_Syntax.Sig_new_effect_for_free
                                        uu____23000
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____22999;
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
                                         (fun uu___264_23019  ->
                                            match uu___264_23019 with
                                            | FStar_Syntax_Syntax.Reifiable 
                                                -> true
                                            | FStar_Syntax_Syntax.Reflectable
                                                uu____23020 -> true
                                            | uu____23021 -> false)
                                         qualifiers
                                        in
                                     let un_ts =
                                       ([], FStar_Syntax_Syntax.tun)  in
                                     let uu____23035 =
                                       let uu____23036 =
                                         let uu____23037 =
                                           lookup1 "return_wp"  in
                                         let uu____23038 = lookup1 "bind_wp"
                                            in
                                         let uu____23039 =
                                           lookup1 "if_then_else"  in
                                         let uu____23040 = lookup1 "ite_wp"
                                            in
                                         let uu____23041 = lookup1 "stronger"
                                            in
                                         let uu____23042 = lookup1 "close_wp"
                                            in
                                         let uu____23043 = lookup1 "assert_p"
                                            in
                                         let uu____23044 = lookup1 "assume_p"
                                            in
                                         let uu____23045 = lookup1 "null_wp"
                                            in
                                         let uu____23046 = lookup1 "trivial"
                                            in
                                         let uu____23047 =
                                           if rr
                                           then
                                             let uu____23048 = lookup1 "repr"
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.snd
                                               uu____23048
                                           else FStar_Syntax_Syntax.tun  in
                                         let uu____23064 =
                                           if rr
                                           then lookup1 "return"
                                           else un_ts  in
                                         let uu____23066 =
                                           if rr
                                           then lookup1 "bind"
                                           else un_ts  in
                                         let uu____23068 =
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
                                             uu____23037;
                                           FStar_Syntax_Syntax.bind_wp =
                                             uu____23038;
                                           FStar_Syntax_Syntax.if_then_else =
                                             uu____23039;
                                           FStar_Syntax_Syntax.ite_wp =
                                             uu____23040;
                                           FStar_Syntax_Syntax.stronger =
                                             uu____23041;
                                           FStar_Syntax_Syntax.close_wp =
                                             uu____23042;
                                           FStar_Syntax_Syntax.assert_p =
                                             uu____23043;
                                           FStar_Syntax_Syntax.assume_p =
                                             uu____23044;
                                           FStar_Syntax_Syntax.null_wp =
                                             uu____23045;
                                           FStar_Syntax_Syntax.trivial =
                                             uu____23046;
                                           FStar_Syntax_Syntax.repr =
                                             uu____23047;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____23064;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____23066;
                                           FStar_Syntax_Syntax.actions =
                                             actions1;
                                           FStar_Syntax_Syntax.eff_attrs =
                                             uu____23068
                                         }  in
                                       FStar_Syntax_Syntax.Sig_new_effect
                                         uu____23036
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         uu____23035;
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
                                          fun uu____23094  ->
                                            match uu____23094 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____23108 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____23108
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
                let uu____23132 = desugar_binders env1 eff_binders  in
                match uu____23132 with
                | (env2,binders) ->
                    let uu____23169 =
                      let uu____23180 = head_and_args defn  in
                      match uu____23180 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____23217 ->
                                let uu____23218 =
                                  let uu____23223 =
                                    let uu____23224 =
                                      let uu____23225 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.strcat uu____23225 " not found"
                                       in
                                    Prims.strcat "Effect " uu____23224  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____23223)
                                   in
                                FStar_Errors.raise_error uu____23218
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____23227 =
                            match FStar_List.rev args with
                            | (last_arg,uu____23257)::args_rev ->
                                let uu____23269 =
                                  let uu____23270 = unparen last_arg  in
                                  uu____23270.FStar_Parser_AST.tm  in
                                (match uu____23269 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____23298 -> ([], args))
                            | uu____23307 -> ([], args)  in
                          (match uu____23227 with
                           | (cattributes,args1) ->
                               let uu____23350 = desugar_args env2 args1  in
                               let uu____23351 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____23350, uu____23351))
                       in
                    (match uu____23169 with
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
                          (let uu____23387 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____23387 with
                           | (ed_binders,uu____23401,ed_binders_opening) ->
                               let sub1 uu____23414 =
                                 match uu____23414 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____23428 =
                                         FStar_Syntax_Subst.shift_subst
                                           (FStar_List.length us)
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____23428 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____23432 =
                                       let uu____23433 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____23433)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____23432
                                  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____23442 =
                                   let uu____23443 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____23443
                                    in
                                 let uu____23458 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____23459 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____23460 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____23461 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____23462 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____23463 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____23464 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____23465 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____23466 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____23467 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____23468 =
                                   let uu____23469 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____23469
                                    in
                                 let uu____23484 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____23485 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____23486 =
                                   FStar_List.map
                                     (fun action  ->
                                        let uu____23494 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____23495 =
                                          let uu____23496 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____23496
                                           in
                                        let uu____23511 =
                                          let uu____23512 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____23512
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____23494;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____23495;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____23511
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
                                     uu____23442;
                                   FStar_Syntax_Syntax.ret_wp = uu____23458;
                                   FStar_Syntax_Syntax.bind_wp = uu____23459;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____23460;
                                   FStar_Syntax_Syntax.ite_wp = uu____23461;
                                   FStar_Syntax_Syntax.stronger = uu____23462;
                                   FStar_Syntax_Syntax.close_wp = uu____23463;
                                   FStar_Syntax_Syntax.assert_p = uu____23464;
                                   FStar_Syntax_Syntax.assume_p = uu____23465;
                                   FStar_Syntax_Syntax.null_wp = uu____23466;
                                   FStar_Syntax_Syntax.trivial = uu____23467;
                                   FStar_Syntax_Syntax.repr = uu____23468;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____23484;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____23485;
                                   FStar_Syntax_Syntax.actions = uu____23486;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____23529 =
                                     let uu____23530 =
                                       let uu____23539 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____23539
                                        in
                                     FStar_List.length uu____23530  in
                                   uu____23529 = (Prims.parse_int "1")  in
                                 let uu____23570 =
                                   let uu____23573 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____23573 quals  in
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
                                   FStar_Syntax_Syntax.sigquals = uu____23570;
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
                                             let uu____23595 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____23595
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____23597 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____23597
                                 then
                                   let reflect_lid =
                                     let uu____23601 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____23601
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
    let uu____23611 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____23611 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.strcat "  " (Prims.strcat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____23662 ->
              let uu____23663 =
                let uu____23664 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____23664
                 in
              Prims.strcat "\n  " uu____23663
          | uu____23665 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____23678  ->
               match uu____23678 with
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
          let uu____23696 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____23696
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____23698 =
          let uu____23709 = FStar_Syntax_Syntax.as_arg arg  in [uu____23709]
           in
        FStar_Syntax_Util.mk_app fv uu____23698

and (desugar_decl_aux :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      let uu____23740 = desugar_decl_noattrs env d  in
      match uu____23740 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____23758 = mk_comment_attr d  in uu____23758 :: attrs1  in
          let uu____23759 =
            FStar_List.mapi
              (fun i  ->
                 fun sigelt  ->
                   if i = (Prims.parse_int "0")
                   then
                     let uu___299_23765 = sigelt  in
                     {
                       FStar_Syntax_Syntax.sigel =
                         (uu___299_23765.FStar_Syntax_Syntax.sigel);
                       FStar_Syntax_Syntax.sigrng =
                         (uu___299_23765.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___299_23765.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___299_23765.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs = attrs2
                     }
                   else
                     (let uu___300_23767 = sigelt  in
                      let uu____23768 =
                        FStar_List.filter
                          (fun at1  ->
                             let uu____23774 = get_fail_attr false at1  in
                             FStar_Option.isNone uu____23774) attrs2
                         in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___300_23767.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___300_23767.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___300_23767.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___300_23767.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs = uu____23768
                      })) sigelts
             in
          (env1, uu____23759)

and (desugar_decl :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      let uu____23795 = desugar_decl_aux env d  in
      match uu____23795 with
      | (env1,ses) ->
          let uu____23806 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____23806)

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
      | FStar_Parser_AST.Fsdoc uu____23834 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Friend lid ->
          let uu____23839 = FStar_Syntax_DsEnv.iface env  in
          if uu____23839
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____23849 =
               let uu____23850 =
                 let uu____23851 = FStar_Syntax_DsEnv.dep_graph env  in
                 let uu____23852 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Parser_Dep.module_has_interface uu____23851
                   uu____23852
                  in
               Prims.op_Negation uu____23850  in
             if uu____23849
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____23862 =
                  let uu____23863 =
                    let uu____23864 = FStar_Syntax_DsEnv.dep_graph env  in
                    FStar_Parser_Dep.module_has_interface uu____23864 lid  in
                  Prims.op_Negation uu____23863  in
                if uu____23862
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____23874 =
                     let uu____23875 =
                       let uu____23876 = FStar_Syntax_DsEnv.dep_graph env  in
                       FStar_Parser_Dep.deps_has_implementation uu____23876
                         lid
                        in
                     Prims.op_Negation uu____23875  in
                   if uu____23874
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____23890 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____23890, [])
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
              | (FStar_Parser_AST.TyconRecord uu____23924,uu____23925)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu____23964 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1  in
          let tcs1 =
            FStar_List.map
              (fun uu____23988  ->
                 match uu____23988 with | (x,uu____23996) -> x) tcs
             in
          let uu____24001 =
            let uu____24006 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____24006 tcs1  in
          (match uu____24001 with
           | (env1,ses) ->
               let mkclass lid =
                 let uu____24023 =
                   let uu____24024 =
                     let uu____24031 =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun
                        in
                     FStar_Syntax_Syntax.mk_binder uu____24031  in
                   [uu____24024]  in
                 let uu____24044 =
                   let uu____24047 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____24050 =
                     let uu____24061 =
                       let uu____24070 =
                         let uu____24071 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____24071  in
                       FStar_Syntax_Syntax.as_arg uu____24070  in
                     [uu____24061]  in
                   FStar_Syntax_Util.mk_app uu____24047 uu____24050  in
                 FStar_Syntax_Util.abs uu____24023 uu____24044
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____24110,id1))::uu____24112 ->
                       FStar_Pervasives_Native.Some id1
                   | uu____24115::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____24119 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____24119 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id1 ->
                     let id2 = FStar_Syntax_Util.unmangle_field_name id1  in
                     let uu____24126 = FStar_Syntax_DsEnv.qualify env1 id2
                        in
                     [uu____24126]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____24147) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____24157,uu____24158,uu____24159,uu____24160,uu____24161)
                     ->
                     let uu____24170 =
                       let uu____24171 =
                         let uu____24172 =
                           let uu____24179 = mkclass lid  in
                           (meths, uu____24179)  in
                         FStar_Syntax_Syntax.Sig_splice uu____24172  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____24171;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = []
                       }  in
                     [uu____24170]
                 | uu____24182 -> []  in
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
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____24212;
                    FStar_Parser_AST.prange = uu____24213;_},uu____24214)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____24223;
                    FStar_Parser_AST.prange = uu____24224;_},uu____24225)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____24240;
                         FStar_Parser_AST.prange = uu____24241;_},uu____24242);
                    FStar_Parser_AST.prange = uu____24243;_},uu____24244)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____24265;
                         FStar_Parser_AST.prange = uu____24266;_},uu____24267);
                    FStar_Parser_AST.prange = uu____24268;_},uu____24269)::[]
                   -> false
               | (p,uu____24297)::[] ->
                   let uu____24306 = is_app_pattern p  in
                   Prims.op_Negation uu____24306
               | uu____24307 -> false)
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
            let uu____24380 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____24380 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____24392 =
                     let uu____24393 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____24393.FStar_Syntax_Syntax.n  in
                   match uu____24392 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____24403) ->
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
                         | uu____24436::uu____24437 ->
                             FStar_List.map
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____24440 ->
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.collect
                                  (fun uu___265_24455  ->
                                     match uu___265_24455 with
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inl uu____24458;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____24459;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____24460;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____24461;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____24462;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____24463;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____24464;_}
                                         -> []
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____24476;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____24477;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____24478;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____24479;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____24480;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____24481;_}
                                         ->
                                         FStar_Syntax_DsEnv.lookup_letbinding_quals
                                           env
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                          in
                       let quals2 =
                         let uu____24495 =
                           FStar_All.pipe_right lets1
                             (FStar_Util.for_some
                                (fun uu____24526  ->
                                   match uu____24526 with
                                   | (uu____24539,(uu____24540,t)) ->
                                       t.FStar_Parser_AST.level =
                                         FStar_Parser_AST.Formula))
                            in
                         if uu____24495
                         then FStar_Syntax_Syntax.Logic :: quals1
                         else quals1  in
                       let lbs1 =
                         let uu____24558 =
                           FStar_All.pipe_right quals2
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract)
                            in
                         if uu____24558
                         then
                           let uu____24561 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu___301_24575 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___302_24577 = fv  in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___302_24577.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___302_24577.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___301_24575.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___301_24575.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___301_24575.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___301_24575.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___301_24575.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___301_24575.FStar_Syntax_Syntax.lbpos)
                                     }))
                              in
                           ((FStar_Pervasives_Native.fst lbs), uu____24561)
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
                   | uu____24604 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____24610 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____24629 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____24610 with
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
                       let uu___303_24665 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___303_24665.FStar_Parser_AST.prange)
                       }
                   | uu____24672 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___304_24679 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___304_24679.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___304_24679.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___304_24679.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____24715 id1 =
                   match uu____24715 with
                   | (env1,ses) ->
                       let main =
                         let uu____24736 =
                           let uu____24737 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____24737  in
                         FStar_Parser_AST.mk_term uu____24736
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
                       let uu____24787 = desugar_decl env1 id_decl  in
                       (match uu____24787 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____24805 = gather_pattern_bound_vars true pat  in
                   FStar_All.pipe_right uu____24805 FStar_Util.set_elements
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
            let uu____24828 = close_fun env t  in
            desugar_term env uu____24828  in
          let quals1 =
            let uu____24832 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____24832
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let se =
            let uu____24838 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____24838;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in
          let env2 =
            FStar_Syntax_DsEnv.push_doc env1 lid d.FStar_Parser_AST.doc  in
          (env2, [se])
      | FStar_Parser_AST.Exception (id1,FStar_Pervasives_Native.None ) ->
          let t =
            FStar_Syntax_DsEnv.fail_or env
              (FStar_Syntax_DsEnv.try_lookup_lid env)
              FStar_Parser_Const.exn_lid
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
      | FStar_Parser_AST.Exception (id1,FStar_Pervasives_Native.Some term) ->
          let t = desugar_term env term  in
          let t1 =
            let uu____24876 =
              let uu____24885 = FStar_Syntax_Syntax.null_binder t  in
              [uu____24885]  in
            let uu____24904 =
              let uu____24907 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_lid env)
                  FStar_Parser_Const.exn_lid
                 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____24907
               in
            FStar_Syntax_Util.arrow uu____24876 uu____24904  in
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
            let uu____24960 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____24960 with
            | FStar_Pervasives_Native.None  ->
                let uu____24963 =
                  let uu____24968 =
                    let uu____24969 =
                      let uu____24970 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.strcat uu____24970 " not found"  in
                    Prims.strcat "Effect name " uu____24969  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____24968)  in
                FStar_Errors.raise_error uu____24963
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____24974 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____24992 =
                  let uu____24995 =
                    let uu____24996 = desugar_term env t  in
                    ([], uu____24996)  in
                  FStar_Pervasives_Native.Some uu____24995  in
                (uu____24992, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____25009 =
                  let uu____25012 =
                    let uu____25013 = desugar_term env wp  in
                    ([], uu____25013)  in
                  FStar_Pervasives_Native.Some uu____25012  in
                let uu____25020 =
                  let uu____25023 =
                    let uu____25024 = desugar_term env t  in
                    ([], uu____25024)  in
                  FStar_Pervasives_Native.Some uu____25023  in
                (uu____25009, uu____25020)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____25036 =
                  let uu____25039 =
                    let uu____25040 = desugar_term env t  in
                    ([], uu____25040)  in
                  FStar_Pervasives_Native.Some uu____25039  in
                (FStar_Pervasives_Native.None, uu____25036)
             in
          (match uu____24974 with
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
            let uu____25074 =
              let uu____25075 =
                let uu____25082 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____25082, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____25075  in
            {
              FStar_Syntax_Syntax.sigel = uu____25074;
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
      let uu____25108 =
        FStar_List.fold_left
          (fun uu____25128  ->
             fun d  ->
               match uu____25128 with
               | (env1,sigelts) ->
                   let uu____25148 = desugar_decl env1 d  in
                   (match uu____25148 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____25108 with
      | (env1,sigelts) ->
          let rec forward acc uu___267_25193 =
            match uu___267_25193 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____25207,FStar_Syntax_Syntax.Sig_let uu____25208) ->
                     let uu____25221 =
                       let uu____25224 =
                         let uu___305_25225 = se2  in
                         let uu____25226 =
                           let uu____25229 =
                             FStar_List.filter
                               (fun uu___266_25243  ->
                                  match uu___266_25243 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____25247;
                                           FStar_Syntax_Syntax.vars =
                                             uu____25248;_},uu____25249);
                                      FStar_Syntax_Syntax.pos = uu____25250;
                                      FStar_Syntax_Syntax.vars = uu____25251;_}
                                      when
                                      let uu____25278 =
                                        let uu____25279 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____25279
                                         in
                                      uu____25278 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____25280 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____25229
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___305_25225.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___305_25225.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___305_25225.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___305_25225.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____25226
                         }  in
                       uu____25224 :: se1 :: acc  in
                     forward uu____25221 sigelts1
                 | uu____25285 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____25293 = forward [] sigelts  in (env1, uu____25293)
  
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
          | (FStar_Pervasives_Native.None ,uu____25354) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____25358;
               FStar_Syntax_Syntax.exports = uu____25359;
               FStar_Syntax_Syntax.is_interface = uu____25360;_},FStar_Parser_AST.Module
             (current_lid,uu____25362)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____25370) ->
              let uu____25373 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____25373
           in
        let uu____25378 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____25414 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____25414, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____25431 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____25431, mname, decls, false)
           in
        match uu____25378 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____25461 = desugar_decls env2 decls  in
            (match uu____25461 with
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
          let uu____25523 =
            (FStar_Options.interactive ()) &&
              (let uu____25525 =
                 let uu____25526 =
                   let uu____25527 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____25527  in
                 FStar_Util.get_file_extension uu____25526  in
               FStar_List.mem uu____25525 ["fsti"; "fsi"])
             in
          if uu____25523 then as_interface m else m  in
        let uu____25531 = desugar_modul_common curmod env m1  in
        match uu____25531 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____25549 = FStar_Syntax_DsEnv.pop ()  in
              (uu____25549, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul ->
      (env_t,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun m  ->
      let uu____25569 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____25569 with
      | (env1,modul,pop_when_done) ->
          let uu____25583 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____25583 with
           | (env2,modul1) ->
               ((let uu____25595 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____25595
                 then
                   let uu____25596 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____25596
                 else ());
                (let uu____25598 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____25598, modul1))))
  
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
        (fun uu____25645  ->
           let uu____25646 = desugar_modul env modul  in
           match uu____25646 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____25687  ->
           let uu____25688 = desugar_decls env decls  in
           match uu____25688 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____25742  ->
             let uu____25743 = desugar_partial_modul modul env a_modul  in
             match uu____25743 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____25841 ->
                  let t =
                    let uu____25851 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____25851  in
                  let uu____25864 =
                    let uu____25865 = FStar_Syntax_Subst.compress t  in
                    uu____25865.FStar_Syntax_Syntax.n  in
                  (match uu____25864 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____25877,uu____25878)
                       -> bs1
                   | uu____25903 -> failwith "Impossible")
               in
            let uu____25912 =
              let uu____25919 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____25919
                FStar_Syntax_Syntax.t_unit
               in
            match uu____25912 with
            | (binders,uu____25921,binders_opening) ->
                let erase_term t =
                  let uu____25929 =
                    let uu____25930 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____25930  in
                  FStar_Syntax_Subst.close binders uu____25929  in
                let erase_tscheme uu____25948 =
                  match uu____25948 with
                  | (us,t) ->
                      let t1 =
                        let uu____25968 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____25968 t  in
                      let uu____25971 =
                        let uu____25972 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____25972  in
                      ([], uu____25971)
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
                    | uu____25995 ->
                        let bs =
                          let uu____26005 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____26005  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____26045 =
                          let uu____26046 =
                            let uu____26049 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____26049  in
                          uu____26046.FStar_Syntax_Syntax.n  in
                        (match uu____26045 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____26051,uu____26052) -> bs1
                         | uu____26077 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____26084 =
                      let uu____26085 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____26085  in
                    FStar_Syntax_Subst.close binders uu____26084  in
                  let uu___306_26086 = action  in
                  let uu____26087 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____26088 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___306_26086.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___306_26086.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____26087;
                    FStar_Syntax_Syntax.action_typ = uu____26088
                  }  in
                let uu___307_26089 = ed  in
                let uu____26090 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____26091 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____26092 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____26093 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____26094 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____26095 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____26096 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____26097 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____26098 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____26099 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____26100 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____26101 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____26102 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____26103 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____26104 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____26105 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___307_26089.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___307_26089.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____26090;
                  FStar_Syntax_Syntax.signature = uu____26091;
                  FStar_Syntax_Syntax.ret_wp = uu____26092;
                  FStar_Syntax_Syntax.bind_wp = uu____26093;
                  FStar_Syntax_Syntax.if_then_else = uu____26094;
                  FStar_Syntax_Syntax.ite_wp = uu____26095;
                  FStar_Syntax_Syntax.stronger = uu____26096;
                  FStar_Syntax_Syntax.close_wp = uu____26097;
                  FStar_Syntax_Syntax.assert_p = uu____26098;
                  FStar_Syntax_Syntax.assume_p = uu____26099;
                  FStar_Syntax_Syntax.null_wp = uu____26100;
                  FStar_Syntax_Syntax.trivial = uu____26101;
                  FStar_Syntax_Syntax.repr = uu____26102;
                  FStar_Syntax_Syntax.return_repr = uu____26103;
                  FStar_Syntax_Syntax.bind_repr = uu____26104;
                  FStar_Syntax_Syntax.actions = uu____26105;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___307_26089.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___308_26121 = se  in
                  let uu____26122 =
                    let uu____26123 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____26123  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____26122;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___308_26121.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___308_26121.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___308_26121.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___308_26121.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___309_26127 = se  in
                  let uu____26128 =
                    let uu____26129 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____26129
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____26128;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___309_26127.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___309_26127.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___309_26127.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___309_26127.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____26131 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____26132 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____26132 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____26144 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____26144
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____26146 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____26146)
  