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
      fun uu___240_237  ->
        match uu___240_237 with
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
  fun uu___241_246  ->
    match uu___241_246 with
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
  fun uu___242_260  ->
    match uu___242_260 with
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
  fun uu___243_1845  ->
    match uu___243_1845 with
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
        let uu___269_2454 = s  in
        let uu____2455 =
          let uu____2456 =
            let uu____2465 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____2483,bs,t,lids1,lids2) ->
                          let uu___270_2496 = se  in
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
                              (uu___270_2496.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___270_2496.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___270_2496.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___270_2496.FStar_Syntax_Syntax.sigattrs)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____2531,t,tlid,n1,lids1) ->
                          let uu___271_2540 = se  in
                          let uu____2541 =
                            let uu____2542 =
                              let uu____2557 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____2557, tlid, n1, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____2542  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____2541;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___271_2540.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___271_2540.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___271_2540.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___271_2540.FStar_Syntax_Syntax.sigattrs)
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
            (uu___269_2454.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___269_2454.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___269_2454.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___269_2454.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2566,t) ->
        let uvs =
          let uu____2569 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____2569 FStar_Util.set_elements  in
        let uu___272_2574 = s  in
        let uu____2575 =
          let uu____2576 =
            let uu____2583 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____2583)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____2576  in
        {
          FStar_Syntax_Syntax.sigel = uu____2575;
          FStar_Syntax_Syntax.sigrng =
            (uu___272_2574.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___272_2574.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___272_2574.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___272_2574.FStar_Syntax_Syntax.sigattrs)
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
        let uu___273_2879 = s  in
        let uu____2880 =
          let uu____2881 =
            let uu____2888 =
              let uu____2889 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___274_2901 = lb  in
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
                            (uu___274_2901.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____2902;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___274_2901.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____2905;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___274_2901.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___274_2901.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____2889)  in
            (uu____2888, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____2881  in
        {
          FStar_Syntax_Syntax.sigel = uu____2880;
          FStar_Syntax_Syntax.sigrng =
            (uu___273_2879.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___273_2879.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___273_2879.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___273_2879.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____2913,fml) ->
        let uvs =
          let uu____2916 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____2916 FStar_Util.set_elements  in
        let uu___275_2921 = s  in
        let uu____2922 =
          let uu____2923 =
            let uu____2930 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____2930)  in
          FStar_Syntax_Syntax.Sig_assume uu____2923  in
        {
          FStar_Syntax_Syntax.sigel = uu____2922;
          FStar_Syntax_Syntax.sigrng =
            (uu___275_2921.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___275_2921.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___275_2921.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___275_2921.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____2932,bs,c,flags1) ->
        let uvs =
          let uu____2941 =
            let uu____2944 = bs_univnames bs  in
            let uu____2947 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____2944 uu____2947  in
          FStar_All.pipe_right uu____2941 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___276_2955 = s  in
        let uu____2956 =
          let uu____2957 =
            let uu____2970 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____2971 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____2970, uu____2971, flags1)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____2957  in
        {
          FStar_Syntax_Syntax.sigel = uu____2956;
          FStar_Syntax_Syntax.sigrng =
            (uu___276_2955.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___276_2955.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___276_2955.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___276_2955.FStar_Syntax_Syntax.sigattrs)
        }
    | uu____2974 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___244_2979  ->
    match uu___244_2979 with
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
                  (fun uu___245_3192  ->
                     match uu___245_3192 with
                     | FStar_Util.Inr uu____3197 -> true
                     | uu____3198 -> false) univargs
              then
                let uu____3203 =
                  let uu____3204 =
                    FStar_List.map
                      (fun uu___246_3213  ->
                         match uu___246_3213 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____3204  in
                FStar_Util.Inr uu____3203
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___247_3230  ->
                        match uu___247_3230 with
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
                        let uu___277_4301 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_var
                               (let uu___278_4306 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___278_4306.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___278_4306.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___277_4301.FStar_Syntax_Syntax.p)
                        }
                    | FStar_Syntax_Syntax.Pat_wild x ->
                        let uu___279_4308 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_wild
                               (let uu___280_4313 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___280_4313.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___280_4313.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___279_4308.FStar_Syntax_Syntax.p)
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
                          let uu___281_4365 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___281_4365.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___281_4365.FStar_Syntax_Syntax.index);
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
                             let uu___282_5899 = fv  in
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
                                 (uu___282_5899.FStar_Syntax_Syntax.fv_name);
                               FStar_Syntax_Syntax.fv_delta =
                                 (uu___282_5899.FStar_Syntax_Syntax.fv_delta);
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
                           let uu___283_6890 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___283_6890.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___283_6890.FStar_Syntax_Syntax.vars)
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
          let uu___284_7250 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___284_7250.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___284_7250.FStar_Syntax_Syntax.vars)
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
            ((let uu____7344 = FStar_Ident.text_of_id op_star  in
              uu____7344 = "*") &&
               (let uu____7346 =
                  op_as_term env (Prims.parse_int "2")
                    top.FStar_Parser_AST.range op_star
                   in
                FStar_All.pipe_right uu____7346 FStar_Option.isNone))
              ||
              (let uu____7352 = FStar_Ident.text_of_id op_star  in
               uu____7352 = "_*&")
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____7363;_},t1::t2::[])
                  when
                  let uu____7368 =
                    op_as_term env (Prims.parse_int "2")
                      top.FStar_Parser_AST.range op_star
                     in
                  FStar_All.pipe_right uu____7368 FStar_Option.isNone ->
                  let uu____7373 = flatten1 t1  in
                  FStar_List.append uu____7373 [t2]
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "_*&";
                     FStar_Ident.idRange = uu____7376;_},t1::t2::[])
                  ->
                  let uu____7381 = flatten1 t1  in
                  FStar_List.append uu____7381 [t2]
              | uu____7384 -> [t]  in
            let uu____7385 =
              let uu____7410 =
                let uu____7433 =
                  let uu____7436 = unparen top  in flatten1 uu____7436  in
                FStar_All.pipe_right uu____7433
                  (FStar_List.map
                     (fun t  ->
                        let uu____7471 = desugar_typ_aq env t  in
                        match uu____7471 with
                        | (t',aq) ->
                            let uu____7482 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____7482, aq)))
                 in
              FStar_All.pipe_right uu____7410 FStar_List.unzip  in
            (match uu____7385 with
             | (targs,aqs) ->
                 let tup =
                   let uu____7592 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____7592
                    in
                 let uu____7601 =
                   mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                 (uu____7601, (join_aqs aqs)))
        | FStar_Parser_AST.Tvar a ->
            let uu____7615 =
              let uu____7616 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_All.pipe_left setpos uu____7616  in
            (uu____7615, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____7622 =
              let uu____7627 =
                let uu____7628 =
                  let uu____7629 = FStar_Ident.text_of_id u  in
                  Prims.strcat uu____7629 " in non-universe context"  in
                Prims.strcat "Unexpected universe variable " uu____7628  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____7627)  in
            FStar_Errors.raise_error uu____7622 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____7640 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____7640 with
             | FStar_Pervasives_Native.None  ->
                 let uu____7647 =
                   let uu____7652 =
                     let uu____7653 = FStar_Ident.text_of_id s  in
                     Prims.strcat "Unexpected or unbound operator: "
                       uu____7653
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____7652)
                    in
                 FStar_Errors.raise_error uu____7647
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let uu____7663 =
                     let uu____7688 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____7750 = desugar_term_aq env t  in
                               match uu____7750 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____7688 FStar_List.unzip  in
                   (match uu____7663 with
                    | (args1,aqs) ->
                        let uu____7883 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____7883, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____7899)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____7914 =
              let uu___285_7915 = top  in
              let uu____7916 =
                let uu____7917 =
                  let uu____7924 =
                    let uu___286_7925 = top  in
                    let uu____7926 =
                      let uu____7927 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____7927  in
                    {
                      FStar_Parser_AST.tm = uu____7926;
                      FStar_Parser_AST.range =
                        (uu___286_7925.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___286_7925.FStar_Parser_AST.level)
                    }  in
                  (uu____7924, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____7917  in
              {
                FStar_Parser_AST.tm = uu____7916;
                FStar_Parser_AST.range =
                  (uu___285_7915.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___285_7915.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____7914
        | FStar_Parser_AST.Construct (n1,(a,uu____7930)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____7946 =
                let uu___287_7947 = top  in
                let uu____7948 =
                  let uu____7949 =
                    let uu____7956 =
                      let uu___288_7957 = top  in
                      let uu____7958 =
                        let uu____7959 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____7959  in
                      {
                        FStar_Parser_AST.tm = uu____7958;
                        FStar_Parser_AST.range =
                          (uu___288_7957.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___288_7957.FStar_Parser_AST.level)
                      }  in
                    (uu____7956, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____7949  in
                {
                  FStar_Parser_AST.tm = uu____7948;
                  FStar_Parser_AST.range =
                    (uu___287_7947.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___287_7947.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____7946))
        | FStar_Parser_AST.Construct (n1,(a,uu____7962)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____7977 =
              let uu___289_7978 = top  in
              let uu____7979 =
                let uu____7980 =
                  let uu____7987 =
                    let uu___290_7988 = top  in
                    let uu____7989 =
                      let uu____7990 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____7990  in
                    {
                      FStar_Parser_AST.tm = uu____7989;
                      FStar_Parser_AST.range =
                        (uu___290_7988.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___290_7988.FStar_Parser_AST.level)
                    }  in
                  (uu____7987, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____7980  in
              {
                FStar_Parser_AST.tm = uu____7979;
                FStar_Parser_AST.range =
                  (uu___289_7978.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___289_7978.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____7977
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____7991; FStar_Ident.ident = uu____7992;
              FStar_Ident.nsstr = uu____7993; FStar_Ident.str = "Type0";_}
            ->
            let uu____7996 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____7996, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____7997; FStar_Ident.ident = uu____7998;
              FStar_Ident.nsstr = uu____7999; FStar_Ident.str = "Type";_}
            ->
            let uu____8002 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____8002, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____8003; FStar_Ident.ident = uu____8004;
               FStar_Ident.nsstr = uu____8005; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____8023 =
              let uu____8024 =
                let uu____8025 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____8025  in
              mk1 uu____8024  in
            (uu____8023, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8026; FStar_Ident.ident = uu____8027;
              FStar_Ident.nsstr = uu____8028; FStar_Ident.str = "Effect";_}
            ->
            let uu____8031 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____8031, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8032; FStar_Ident.ident = uu____8033;
              FStar_Ident.nsstr = uu____8034; FStar_Ident.str = "True";_}
            ->
            let uu____8037 =
              let uu____8038 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8038
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8037, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8039; FStar_Ident.ident = uu____8040;
              FStar_Ident.nsstr = uu____8041; FStar_Ident.str = "False";_}
            ->
            let uu____8044 =
              let uu____8045 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8045
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8044, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____8048;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____8050 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____8050 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____8059 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_constant_at_level
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None
                     in
                  (uu____8059, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____8060 =
                    let uu____8061 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____8061 txt
                     in
                  failwith uu____8060))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8068 = desugar_name mk1 setpos env true l  in
              (uu____8068, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8071 = desugar_name mk1 setpos env true l  in
              (uu____8071, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____8082 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____8082 with
                | FStar_Pervasives_Native.Some uu____8091 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____8096 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____8096 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____8110 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____8127 =
                    let uu____8128 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____8128  in
                  (uu____8127, noaqs)
              | uu____8129 ->
                  let uu____8136 =
                    let uu____8141 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____8141)  in
                  FStar_Errors.raise_error uu____8136
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____8148 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____8148 with
              | FStar_Pervasives_Native.None  ->
                  let uu____8155 =
                    let uu____8160 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____8160)
                     in
                  FStar_Errors.raise_error uu____8155
                    top.FStar_Parser_AST.range
              | uu____8165 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____8169 = desugar_name mk1 setpos env true lid'  in
                  (uu____8169, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8185 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____8185 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____8204 ->
                       let uu____8211 =
                         FStar_Util.take
                           (fun uu____8235  ->
                              match uu____8235 with
                              | (uu____8240,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____8211 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____8285 =
                              let uu____8310 =
                                FStar_List.map
                                  (fun uu____8353  ->
                                     match uu____8353 with
                                     | (t,imp) ->
                                         let uu____8370 =
                                           desugar_term_aq env t  in
                                         (match uu____8370 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____8310
                                FStar_List.unzip
                               in
                            (match uu____8285 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____8511 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____8511, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____8529 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____8529 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.strcat "Constructor "
                             (Prims.strcat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____8536 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.strcat "Effect "
                             (Prims.strcat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____8547 =
              FStar_List.fold_left
                (fun uu____8592  ->
                   fun b  ->
                     match uu____8592 with
                     | (env1,tparams,typs) ->
                         let uu____8649 = desugar_binder env1 b  in
                         (match uu____8649 with
                          | (xopt,t1) ->
                              let uu____8678 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____8687 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____8687)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____8678 with
                               | (env2,x) ->
                                   let uu____8707 =
                                     let uu____8710 =
                                       let uu____8713 =
                                         let uu____8714 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____8714
                                          in
                                       [uu____8713]  in
                                     FStar_List.append typs uu____8710  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___291_8740 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___291_8740.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___291_8740.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____8707)))) (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      FStar_Pervasives_Native.None])
               in
            (match uu____8547 with
             | (env1,uu____8768,targs) ->
                 let tup =
                   let uu____8791 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____8791
                    in
                 let uu____8792 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_app (tup, targs))
                    in
                 (uu____8792, noaqs))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____8811 = uncurry binders t  in
            (match uu____8811 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___248_8855 =
                   match uu___248_8855 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1  in
                       let uu____8871 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____8871
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____8895 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____8895 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____8928 = aux env [] bs  in (uu____8928, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____8937 = desugar_binder env b  in
            (match uu____8937 with
             | (FStar_Pervasives_Native.None ,uu____8948) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____8962 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____8962 with
                  | ((x,uu____8978),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____8991 =
                        let uu____8992 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____8992  in
                      (uu____8991, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let bvss =
              FStar_List.map (gather_pattern_bound_vars false) binders  in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set1::sets2 ->
                    let i = FStar_Util.set_intersect acc set1  in
                    let uu____9070 = FStar_Util.set_is_empty i  in
                    if uu____9070
                    then
                      let uu____9073 = FStar_Util.set_union acc set1  in
                      aux uu____9073 sets2
                    else
                      (let uu____9077 =
                         let uu____9078 = FStar_Util.set_elements i  in
                         FStar_List.hd uu____9078  in
                       FStar_Pervasives_Native.Some uu____9077)
                 in
              let uu____9081 = FStar_Syntax_Syntax.new_id_set ()  in
              aux uu____9081 sets  in
            ((let uu____9085 = check_disjoint bvss  in
              match uu____9085 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some id1 ->
                  let uu____9089 =
                    let uu____9094 =
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        id1.FStar_Ident.idText
                       in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____9094)
                     in
                  let uu____9095 = FStar_Ident.range_of_id id1  in
                  FStar_Errors.raise_error uu____9089 uu____9095);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern)
                 in
              let uu____9103 =
                FStar_List.fold_left
                  (fun uu____9123  ->
                     fun pat  ->
                       match uu____9123 with
                       | (env1,ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____9149,(t,FStar_Pervasives_Native.None ))
                                ->
                                let uu____9159 =
                                  let uu____9162 = free_type_vars env1 t  in
                                  FStar_List.append uu____9162 ftvs  in
                                (env1, uu____9159)
                            | FStar_Parser_AST.PatAscribed
                                (uu____9167,(t,FStar_Pervasives_Native.Some
                                             tac))
                                ->
                                let uu____9178 =
                                  let uu____9181 = free_type_vars env1 t  in
                                  let uu____9184 =
                                    let uu____9187 = free_type_vars env1 tac
                                       in
                                    FStar_List.append uu____9187 ftvs  in
                                  FStar_List.append uu____9181 uu____9184  in
                                (env1, uu____9178)
                            | uu____9192 -> (env1, ftvs))) (env, []) binders1
                 in
              match uu____9103 with
              | (uu____9201,ftv) ->
                  let ftv1 = sort_ftv ftv  in
                  let binders2 =
                    let uu____9213 =
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
                    FStar_List.append uu____9213 binders1  in
                  let rec aux env1 bs sc_pat_opt uu___249_9270 =
                    match uu___249_9270 with
                    | [] ->
                        let uu____9297 = desugar_term_aq env1 body  in
                        (match uu____9297 with
                         | (body1,aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc,pat) ->
                                   let body2 =
                                     let uu____9334 =
                                       let uu____9335 =
                                         FStar_Syntax_Syntax.pat_bvs pat  in
                                       FStar_All.pipe_right uu____9335
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder)
                                        in
                                     FStar_Syntax_Subst.close uu____9334
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
                             let uu____9404 =
                               let uu____9407 =
                                 no_annot_abs (FStar_List.rev bs) body2  in
                               setpos uu____9407  in
                             (uu____9404, aq))
                    | p::rest ->
                        let uu____9422 = desugar_binding_pat env1 p  in
                        (match uu____9422 with
                         | (env2,b,pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1,uu____9456)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____9471 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange
                                in
                             let uu____9478 =
                               match b with
                               | LetBinder uu____9519 ->
                                   failwith "Impossible"
                               | LocalBinder (x,aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None
                                        ,uu____9587) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.None ) ->
                                         let uu____9641 =
                                           let uu____9650 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____9650, p1)  in
                                         FStar_Pervasives_Native.Some
                                           uu____9641
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.Some
                                        (sc,p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____9712,uu____9713) ->
                                              let tup2 =
                                                let uu____9715 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.parse_int "2")
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____9715
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____9719 =
                                                  let uu____9726 =
                                                    let uu____9727 =
                                                      let uu____9744 =
                                                        mk1
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let uu____9747 =
                                                        let uu____9758 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let uu____9767 =
                                                          let uu____9778 =
                                                            let uu____9787 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____9787
                                                             in
                                                          [uu____9778]  in
                                                        uu____9758 ::
                                                          uu____9767
                                                         in
                                                      (uu____9744,
                                                        uu____9747)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____9727
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____9726
                                                   in
                                                uu____9719
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range
                                                 in
                                              let p2 =
                                                let uu____9838 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____9838
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____9881,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____9883,pats)) ->
                                              let tupn =
                                                let uu____9926 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    ((Prims.parse_int "1") +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____9926
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____9938 =
                                                  let uu____9939 =
                                                    let uu____9956 =
                                                      mk1
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____9959 =
                                                      let uu____9970 =
                                                        let uu____9981 =
                                                          let uu____9990 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____9990
                                                           in
                                                        [uu____9981]  in
                                                      FStar_List.append args
                                                        uu____9970
                                                       in
                                                    (uu____9956, uu____9959)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____9939
                                                   in
                                                mk1 uu____9938  in
                                              let p2 =
                                                let uu____10038 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats [(p1, false)])))
                                                  uu____10038
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____10079 ->
                                              failwith "Impossible")
                                      in
                                   ((x, aq), sc_pat_opt1)
                                in
                             (match uu____9478 with
                              | (b1,sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest))
                     in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____10172,uu____10173,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____10195 =
                let uu____10196 = unparen e  in
                uu____10196.FStar_Parser_AST.tm  in
              match uu____10195 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____10206 ->
                  let uu____10207 = desugar_term_aq env e  in
                  (match uu____10207 with
                   | (head1,aq) ->
                       let uu____10220 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____10220, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____10227 ->
            let rec aux args aqs e =
              let uu____10304 =
                let uu____10305 = unparen e  in
                uu____10305.FStar_Parser_AST.tm  in
              match uu____10304 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____10323 = desugar_term_aq env t  in
                  (match uu____10323 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____10371 ->
                  let uu____10372 = desugar_term_aq env e  in
                  (match uu____10372 with
                   | (head1,aq) ->
                       let uu____10393 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____10393, (join_aqs (aq :: aqs))))
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
            let uu____10453 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____10453
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
            let uu____10505 = desugar_term_aq env t  in
            (match uu____10505 with
             | (tm,s) ->
                 let uu____10516 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____10516, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____10522 =
              let uu____10535 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____10535 then desugar_typ_aq else desugar_term_aq  in
            uu____10522 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____10590 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____10733  ->
                        match uu____10733 with
                        | (attr_opt,(p,def)) ->
                            let uu____10791 = is_app_pattern p  in
                            if uu____10791
                            then
                              let uu____10822 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____10822, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____10904 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____10904, def1)
                               | uu____10949 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____10987);
                                           FStar_Parser_AST.prange =
                                             uu____10988;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____11036 =
                                            let uu____11057 =
                                              let uu____11062 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____11062  in
                                            (uu____11057, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____11036, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____11153) ->
                                        if top_level
                                        then
                                          let uu____11188 =
                                            let uu____11209 =
                                              let uu____11214 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____11214  in
                                            (uu____11209, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____11188, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____11304 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____11335 =
                FStar_List.fold_left
                  (fun uu____11408  ->
                     fun uu____11409  ->
                       match (uu____11408, uu____11409) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____11517,uu____11518),uu____11519))
                           ->
                           let uu____11636 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____11662 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____11662 with
                                  | (env2,xx) ->
                                      let uu____11681 =
                                        let uu____11684 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____11684 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____11681))
                             | FStar_Util.Inr l ->
                                 let uu____11692 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (uu____11692, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____11636 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____11335 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____11840 =
                    match uu____11840 with
                    | (attrs_opt,(uu____11876,args,result_t),def) ->
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
                                let uu____11964 = is_comp_type env1 t  in
                                if uu____11964
                                then
                                  ((let uu____11966 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____11976 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____11976))
                                       in
                                    match uu____11966 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____11979 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____11981 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____11981))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____11979
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
                          | uu____11988 ->
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
                              let uu____12003 =
                                let uu____12004 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____12004
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____12003
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
                  let uu____12081 = desugar_term_aq env' body  in
                  (match uu____12081 with
                   | (body1,aq) ->
                       let uu____12094 =
                         let uu____12097 =
                           let uu____12098 =
                             let uu____12111 =
                               FStar_Syntax_Subst.close rec_bindings1 body1
                                in
                             ((is_rec, lbs1), uu____12111)  in
                           FStar_Syntax_Syntax.Tm_let uu____12098  in
                         FStar_All.pipe_left mk1 uu____12097  in
                       (uu____12094, aq))
               in
            let ds_non_rec attrs_opt pat t1 t2 =
              let attrs =
                match attrs_opt with
                | FStar_Pervasives_Native.None  -> []
                | FStar_Pervasives_Native.Some l ->
                    FStar_List.map (desugar_term env) l
                 in
              let t11 = desugar_term env t1  in
              let uu____12184 =
                desugar_binding_pat_maybe_top top_level env pat  in
              match uu____12184 with
              | (env1,binder,pat1) ->
                  let uu____12206 =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let uu____12232 = desugar_term_aq env1 t2  in
                        (match uu____12232 with
                         | (body1,aq) ->
                             let fv =
                               let uu____12246 =
                                 FStar_Syntax_Util.incr_delta_qualifier t11
                                  in
                               FStar_Syntax_Syntax.lid_as_fv l uu____12246
                                 FStar_Pervasives_Native.None
                                in
                             let uu____12247 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t11,
                                            (t11.FStar_Syntax_Syntax.pos))]),
                                      body1))
                                in
                             (uu____12247, aq))
                    | LocalBinder (x,uu____12277) ->
                        let uu____12278 = desugar_term_aq env1 t2  in
                        (match uu____12278 with
                         | (body1,aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | ({
                                    FStar_Syntax_Syntax.v =
                                      FStar_Syntax_Syntax.Pat_wild
                                      uu____12292;
                                    FStar_Syntax_Syntax.p = uu____12293;_},uu____12294)::[]
                                   -> body1
                               | uu____12307 ->
                                   let uu____12310 =
                                     let uu____12317 =
                                       let uu____12318 =
                                         let uu____12341 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         let uu____12344 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1
                                            in
                                         (uu____12341, uu____12344)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____12318
                                        in
                                     FStar_Syntax_Syntax.mk uu____12317  in
                                   uu____12310 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range
                                in
                             let uu____12384 =
                               let uu____12387 =
                                 let uu____12388 =
                                   let uu____12401 =
                                     let uu____12404 =
                                       let uu____12405 =
                                         FStar_Syntax_Syntax.mk_binder x  in
                                       [uu____12405]  in
                                     FStar_Syntax_Subst.close uu____12404
                                       body2
                                      in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t11,
                                           (t11.FStar_Syntax_Syntax.pos))]),
                                     uu____12401)
                                    in
                                 FStar_Syntax_Syntax.Tm_let uu____12388  in
                               FStar_All.pipe_left mk1 uu____12387  in
                             (uu____12384, aq))
                     in
                  (match uu____12206 with | (tm,aq) -> (tm, aq))
               in
            let uu____12464 = FStar_List.hd lbs  in
            (match uu____12464 with
             | (attrs,(head_pat,defn)) ->
                 let uu____12508 = is_rec || (is_app_pattern head_pat)  in
                 if uu____12508
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____12521 =
                let uu____12522 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____12522  in
              mk1 uu____12521  in
            let uu____12523 = desugar_term_aq env t1  in
            (match uu____12523 with
             | (t1',aq1) ->
                 let uu____12534 = desugar_term_aq env t2  in
                 (match uu____12534 with
                  | (t2',aq2) ->
                      let uu____12545 = desugar_term_aq env t3  in
                      (match uu____12545 with
                       | (t3',aq3) ->
                           let uu____12556 =
                             let uu____12557 =
                               let uu____12558 =
                                 let uu____12581 =
                                   let uu____12598 =
                                     let uu____12613 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t2.FStar_Parser_AST.range
                                        in
                                     (uu____12613,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____12626 =
                                     let uu____12643 =
                                       let uu____12658 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t3.FStar_Parser_AST.range
                                          in
                                       (uu____12658,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____12643]  in
                                   uu____12598 :: uu____12626  in
                                 (t1', uu____12581)  in
                               FStar_Syntax_Syntax.Tm_match uu____12558  in
                             mk1 uu____12557  in
                           (uu____12556, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____12851 =
              match uu____12851 with
              | (pat,wopt,b) ->
                  let uu____12873 = desugar_match_pat env pat  in
                  (match uu____12873 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____12904 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____12904
                          in
                       let uu____12909 = desugar_term_aq env1 b  in
                       (match uu____12909 with
                        | (b1,aq) ->
                            let uu____12922 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____12922, aq)))
               in
            let uu____12927 = desugar_term_aq env e  in
            (match uu____12927 with
             | (e1,aq) ->
                 let uu____12938 =
                   let uu____12969 =
                     let uu____13002 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____13002 FStar_List.unzip  in
                   FStar_All.pipe_right uu____12969
                     (fun uu____13132  ->
                        match uu____13132 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____12938 with
                  | (brs,aqs) ->
                      let uu____13351 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____13351, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____13385 =
              let uu____13406 = is_comp_type env t  in
              if uu____13406
              then
                let comp = desugar_comp t.FStar_Parser_AST.range env t  in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____13457 = desugar_term_aq env t  in
                 match uu____13457 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____13385 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____13549 = desugar_term_aq env e  in
                 (match uu____13549 with
                  | (e1,aq) ->
                      let uu____13560 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____13560, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____13599,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____13640 = FStar_List.hd fields  in
              match uu____13640 with | (f,uu____13652) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____13698  ->
                        match uu____13698 with
                        | (g,uu____13704) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____13710,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____13724 =
                         let uu____13729 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____13729)
                          in
                       FStar_Errors.raise_error uu____13724
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
                  let uu____13737 =
                    let uu____13748 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____13779  ->
                              match uu____13779 with
                              | (f,uu____13789) ->
                                  let uu____13790 =
                                    let uu____13791 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____13791
                                     in
                                  (uu____13790, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____13748)  in
                  FStar_Parser_AST.Construct uu____13737
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____13809 =
                      let uu____13810 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____13810  in
                    FStar_Parser_AST.mk_term uu____13809
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____13812 =
                      let uu____13825 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____13855  ->
                                match uu____13855 with
                                | (f,uu____13865) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____13825)  in
                    FStar_Parser_AST.Record uu____13812  in
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
            let uu____13925 = desugar_term_aq env recterm1  in
            (match uu____13925 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____13941;
                         FStar_Syntax_Syntax.vars = uu____13942;_},args)
                      ->
                      let uu____13968 =
                        let uu____13969 =
                          let uu____13970 =
                            let uu____13987 =
                              let uu____13990 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____13991 =
                                let uu____13994 =
                                  let uu____13995 =
                                    let uu____14002 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____14002)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____13995
                                   in
                                FStar_Pervasives_Native.Some uu____13994  in
                              FStar_Syntax_Syntax.fvar uu____13990
                                FStar_Syntax_Syntax.delta_constant
                                uu____13991
                               in
                            (uu____13987, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____13970  in
                        FStar_All.pipe_left mk1 uu____13969  in
                      (uu____13968, s)
                  | uu____14031 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____14035 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____14035 with
              | (constrname,is_rec) ->
                  let uu____14050 = desugar_term_aq env e  in
                  (match uu____14050 with
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
                       let uu____14068 =
                         let uu____14069 =
                           let uu____14070 =
                             let uu____14087 =
                               let uu____14090 =
                                 let uu____14091 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____14091
                                  in
                               FStar_Syntax_Syntax.fvar uu____14090
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1")) qual
                                in
                             let uu____14092 =
                               let uu____14103 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____14103]  in
                             (uu____14087, uu____14092)  in
                           FStar_Syntax_Syntax.Tm_app uu____14070  in
                         FStar_All.pipe_left mk1 uu____14069  in
                       (uu____14068, s))))
        | FStar_Parser_AST.NamedTyp (uu____14140,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____14149 =
              let uu____14150 = FStar_Syntax_Subst.compress tm  in
              uu____14150.FStar_Syntax_Syntax.n  in
            (match uu____14149 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____14158 =
                   let uu___292_14159 =
                     let uu____14160 =
                       let uu____14161 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____14161  in
                     FStar_Syntax_Util.exp_string uu____14160  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___292_14159.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___292_14159.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____14158, noaqs)
             | uu____14162 ->
                 let uu____14163 =
                   let uu____14168 =
                     let uu____14169 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.strcat "VQuote, expected an fvar, got: "
                       uu____14169
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____14168)  in
                 FStar_Errors.raise_error uu____14163
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____14175 = desugar_term_aq env e  in
            (match uu____14175 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____14187 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____14187, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____14192 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____14193 =
              let uu____14194 =
                let uu____14201 = desugar_term env e  in (bv, uu____14201)
                 in
              [uu____14194]  in
            (uu____14192, uu____14193)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____14226 =
              let uu____14227 =
                let uu____14228 =
                  let uu____14235 = desugar_term env e  in (uu____14235, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____14228  in
              FStar_All.pipe_left mk1 uu____14227  in
            (uu____14226, noaqs)
        | uu____14240 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____14241 = desugar_formula env top  in
            (uu____14241, noaqs)
        | uu____14242 ->
            let uu____14243 =
              let uu____14248 =
                let uu____14249 = FStar_Parser_AST.term_to_string top  in
                Prims.strcat "Unexpected term: " uu____14249  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____14248)  in
            FStar_Errors.raise_error uu____14243 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____14255 -> false
    | uu____14264 -> true

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
           (fun uu____14301  ->
              match uu____14301 with
              | (a,imp) ->
                  let uu____14314 = desugar_term env a  in
                  arg_withimp_e imp uu____14314))

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
        let is_requires uu____14346 =
          match uu____14346 with
          | (t1,uu____14352) ->
              let uu____14353 =
                let uu____14354 = unparen t1  in
                uu____14354.FStar_Parser_AST.tm  in
              (match uu____14353 with
               | FStar_Parser_AST.Requires uu____14355 -> true
               | uu____14362 -> false)
           in
        let is_ensures uu____14372 =
          match uu____14372 with
          | (t1,uu____14378) ->
              let uu____14379 =
                let uu____14380 = unparen t1  in
                uu____14380.FStar_Parser_AST.tm  in
              (match uu____14379 with
               | FStar_Parser_AST.Ensures uu____14381 -> true
               | uu____14388 -> false)
           in
        let is_app head1 uu____14403 =
          match uu____14403 with
          | (t1,uu____14409) ->
              let uu____14410 =
                let uu____14411 = unparen t1  in
                uu____14411.FStar_Parser_AST.tm  in
              (match uu____14410 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____14413;
                      FStar_Parser_AST.level = uu____14414;_},uu____14415,uu____14416)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____14417 -> false)
           in
        let is_smt_pat uu____14427 =
          match uu____14427 with
          | (t1,uu____14433) ->
              let uu____14434 =
                let uu____14435 = unparen t1  in
                uu____14435.FStar_Parser_AST.tm  in
              (match uu____14434 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____14438);
                             FStar_Parser_AST.range = uu____14439;
                             FStar_Parser_AST.level = uu____14440;_},uu____14441)::uu____14442::[])
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
                             FStar_Parser_AST.range = uu____14481;
                             FStar_Parser_AST.level = uu____14482;_},uu____14483)::uu____14484::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
               | uu____14509 -> false)
           in
        let is_decreases = is_app "decreases"  in
        let pre_process_comp_typ t1 =
          let uu____14541 = head_and_args t1  in
          match uu____14541 with
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
                   let thunk_ens uu____14639 =
                     match uu____14639 with
                     | (e,i) ->
                         let uu____14650 = thunk_ens_ e  in (uu____14650, i)
                      in
                   let fail_lemma uu____14662 =
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
                         let uu____14742 =
                           let uu____14749 =
                             let uu____14756 = thunk_ens ens  in
                             [uu____14756; nil_pat]  in
                           req_true :: uu____14749  in
                         unit_tm :: uu____14742
                     | req::ens::[] when
                         (is_requires req) && (is_ensures ens) ->
                         let uu____14803 =
                           let uu____14810 =
                             let uu____14817 = thunk_ens ens  in
                             [uu____14817; nil_pat]  in
                           req :: uu____14810  in
                         unit_tm :: uu____14803
                     | ens::smtpat::[] when
                         (((let uu____14866 = is_requires ens  in
                            Prims.op_Negation uu____14866) &&
                             (let uu____14868 = is_smt_pat ens  in
                              Prims.op_Negation uu____14868))
                            &&
                            (let uu____14870 = is_decreases ens  in
                             Prims.op_Negation uu____14870))
                           && (is_smt_pat smtpat)
                         ->
                         let uu____14871 =
                           let uu____14878 =
                             let uu____14885 = thunk_ens ens  in
                             [uu____14885; smtpat]  in
                           req_true :: uu____14878  in
                         unit_tm :: uu____14871
                     | ens::dec::[] when
                         (is_ensures ens) && (is_decreases dec) ->
                         let uu____14932 =
                           let uu____14939 =
                             let uu____14946 = thunk_ens ens  in
                             [uu____14946; nil_pat; dec]  in
                           req_true :: uu____14939  in
                         unit_tm :: uu____14932
                     | ens::dec::smtpat::[] when
                         ((is_ensures ens) && (is_decreases dec)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____15006 =
                           let uu____15013 =
                             let uu____15020 = thunk_ens ens  in
                             [uu____15020; smtpat; dec]  in
                           req_true :: uu____15013  in
                         unit_tm :: uu____15006
                     | req::ens::dec::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_decreases dec)
                         ->
                         let uu____15080 =
                           let uu____15087 =
                             let uu____15094 = thunk_ens ens  in
                             [uu____15094; nil_pat; dec]  in
                           req :: uu____15087  in
                         unit_tm :: uu____15080
                     | req::ens::smtpat::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____15154 =
                           let uu____15161 =
                             let uu____15168 = thunk_ens ens  in
                             [uu____15168; smtpat]  in
                           req :: uu____15161  in
                         unit_tm :: uu____15154
                     | req::ens::dec::smtpat::[] when
                         (((is_requires req) && (is_ensures ens)) &&
                            (is_smt_pat smtpat))
                           && (is_decreases dec)
                         ->
                         let uu____15233 =
                           let uu____15240 =
                             let uu____15247 = thunk_ens ens  in
                             [uu____15247; dec; smtpat]  in
                           req :: uu____15240  in
                         unit_tm :: uu____15233
                     | _other -> fail_lemma ()  in
                   let head_and_attributes =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) lemma
                      in
                   (head_and_attributes, args1)
               | FStar_Parser_AST.Name l when
                   FStar_Syntax_DsEnv.is_effect_name env l ->
                   let uu____15309 =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) l
                      in
                   (uu____15309, args)
               | FStar_Parser_AST.Name l when
                   (let uu____15337 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____15337
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   let uu____15338 =
                     let uu____15345 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_Tot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____15345, [])  in
                   (uu____15338, args)
               | FStar_Parser_AST.Name l when
                   (let uu____15363 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____15363
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                   ->
                   let uu____15364 =
                     let uu____15371 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_GTot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____15371, [])  in
                   (uu____15364, args)
               | FStar_Parser_AST.Name l when
                   (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                      ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                     || ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                   ->
                   let uu____15387 =
                     let uu____15394 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_Tot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____15394, [])  in
                   (uu____15387, [(t1, FStar_Parser_AST.Nothing)])
               | uu____15417 ->
                   let default_effect =
                     let uu____15419 = FStar_Options.ml_ish ()  in
                     if uu____15419
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____15422 =
                           FStar_Options.warn_default_effects ()  in
                         if uu____15422
                         then
                           FStar_Errors.log_issue
                             head1.FStar_Parser_AST.range
                             (FStar_Errors.Warning_UseDefaultEffect,
                               "Using default effect Tot")
                         else ());
                        FStar_Parser_Const.effect_Tot_lid)
                      in
                   let uu____15424 =
                     let uu____15431 =
                       FStar_Ident.set_lid_range default_effect
                         head1.FStar_Parser_AST.range
                        in
                     (uu____15431, [])  in
                   (uu____15424, [(t1, FStar_Parser_AST.Nothing)]))
           in
        let uu____15454 = pre_process_comp_typ t  in
        match uu____15454 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____15503 =
                  let uu____15508 =
                    let uu____15509 = FStar_Syntax_Print.lid_to_string eff
                       in
                    FStar_Util.format1 "Not enough args to effect %s"
                      uu____15509
                     in
                  (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____15508)  in
                fail1 uu____15503)
             else ();
             (let is_universe uu____15520 =
                match uu____15520 with
                | (uu____15525,imp) -> imp = FStar_Parser_AST.UnivApp  in
              let uu____15527 = FStar_Util.take is_universe args  in
              match uu____15527 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____15586  ->
                         match uu____15586 with
                         | (u,imp) -> desugar_universe u) universes
                     in
                  let uu____15593 =
                    let uu____15608 = FStar_List.hd args1  in
                    let uu____15617 = FStar_List.tl args1  in
                    (uu____15608, uu____15617)  in
                  (match uu____15593 with
                   | (result_arg,rest) ->
                       let result_typ =
                         desugar_typ env
                           (FStar_Pervasives_Native.fst result_arg)
                          in
                       let rest1 = desugar_args env rest  in
                       let uu____15672 =
                         let is_decrease uu____15710 =
                           match uu____15710 with
                           | (t1,uu____15720) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.pos = uu____15730;
                                       FStar_Syntax_Syntax.vars = uu____15731;_},uu____15732::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.decreases_lid
                                | uu____15771 -> false)
                            in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease)
                          in
                       (match uu____15672 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____15887  ->
                                      match uu____15887 with
                                      | (t1,uu____15897) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____15906,(arg,uu____15908)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____15947 -> failwith "impos")))
                               in
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
                                | uu____15964 -> false  in
                              (((is_empty decreases_clause) &&
                                  (is_empty rest2))
                                 && (is_empty cattributes))
                                && (is_empty universes1)
                               in
                            let uu____15975 =
                              no_additional_args &&
                                (FStar_Ident.lid_equals eff
                                   FStar_Parser_Const.effect_Tot_lid)
                               in
                            if uu____15975
                            then FStar_Syntax_Syntax.mk_Total result_typ
                            else
                              (let uu____15979 =
                                 no_additional_args &&
                                   (FStar_Ident.lid_equals eff
                                      FStar_Parser_Const.effect_GTot_lid)
                                  in
                               if uu____15979
                               then FStar_Syntax_Syntax.mk_GTotal result_typ
                               else
                                 (let flags1 =
                                    let uu____15986 =
                                      FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_Lemma_lid
                                       in
                                    if uu____15986
                                    then [FStar_Syntax_Syntax.LEMMA]
                                    else
                                      (let uu____15990 =
                                         FStar_Ident.lid_equals eff
                                           FStar_Parser_Const.effect_Tot_lid
                                          in
                                       if uu____15990
                                       then [FStar_Syntax_Syntax.TOTAL]
                                       else
                                         (let uu____15994 =
                                            FStar_Ident.lid_equals eff
                                              FStar_Parser_Const.effect_ML_lid
                                             in
                                          if uu____15994
                                          then [FStar_Syntax_Syntax.MLEFFECT]
                                          else
                                            (let uu____15998 =
                                               FStar_Ident.lid_equals eff
                                                 FStar_Parser_Const.effect_GTot_lid
                                                in
                                             if uu____15998
                                             then
                                               [FStar_Syntax_Syntax.SOMETRIVIAL]
                                             else [])))
                                     in
                                  let flags2 =
                                    FStar_List.append flags1 cattributes  in
                                  let rest3 =
                                    let uu____16016 =
                                      FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_Lemma_lid
                                       in
                                    if uu____16016
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
                                                  let uu____16105 =
                                                    FStar_Ident.set_lid_range
                                                      FStar_Parser_Const.pattern_lid
                                                      pat.FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_Syntax.fvar
                                                    uu____16105
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
                                            | uu____16126 -> pat  in
                                          let uu____16127 =
                                            let uu____16138 =
                                              let uu____16149 =
                                                let uu____16158 =
                                                  FStar_Syntax_Syntax.mk
                                                    (FStar_Syntax_Syntax.Tm_meta
                                                       (pat1,
                                                         (FStar_Syntax_Syntax.Meta_desugared
                                                            FStar_Syntax_Syntax.Meta_smt_pat)))
                                                    FStar_Pervasives_Native.None
                                                    pat1.FStar_Syntax_Syntax.pos
                                                   in
                                                (uu____16158, aq)  in
                                              [uu____16149]  in
                                            ens :: uu____16138  in
                                          req :: uu____16127
                                      | uu____16199 -> rest2
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
        | uu____16223 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___293_16244 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___293_16244.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___293_16244.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___294_16286 = b  in
             {
               FStar_Parser_AST.b = (uu___294_16286.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___294_16286.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___294_16286.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____16349 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____16349)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____16362 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____16362 with
             | (env1,a1) ->
                 let a2 =
                   let uu___295_16372 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___295_16372.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___295_16372.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____16398 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____16412 =
                     let uu____16415 =
                       let uu____16416 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____16416]  in
                     no_annot_abs uu____16415 body2  in
                   FStar_All.pipe_left setpos uu____16412  in
                 let uu____16437 =
                   let uu____16438 =
                     let uu____16455 =
                       let uu____16458 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____16458
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____16459 =
                       let uu____16470 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____16470]  in
                     (uu____16455, uu____16459)  in
                   FStar_Syntax_Syntax.Tm_app uu____16438  in
                 FStar_All.pipe_left mk1 uu____16437)
        | uu____16509 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____16589 = q (rest, pats, body)  in
              let uu____16596 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____16589 uu____16596
                FStar_Parser_AST.Formula
               in
            let uu____16597 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____16597 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____16606 -> failwith "impossible"  in
      let uu____16609 =
        let uu____16610 = unparen f  in uu____16610.FStar_Parser_AST.tm  in
      match uu____16609 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____16617,uu____16618) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____16629,uu____16630) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____16661 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____16661
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____16697 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____16697
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____16740 -> desugar_term env f

and (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                FStar_Pervasives_Native.tuple2 Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bs  ->
      let uu____16745 =
        FStar_List.fold_left
          (fun uu____16778  ->
             fun b  ->
               match uu____16778 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___296_16822 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___296_16822.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___296_16822.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___296_16822.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____16837 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____16837 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___297_16855 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___297_16855.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___297_16855.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____16856 =
                               let uu____16863 =
                                 let uu____16868 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____16868)  in
                               uu____16863 :: out  in
                             (env2, uu____16856))
                    | uu____16879 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____16745 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

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
          let uu____16950 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____16950)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____16955 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____16955)
      | FStar_Parser_AST.TVariable x ->
          let uu____16959 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____16959)
      | FStar_Parser_AST.NoName t ->
          let uu____16963 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____16963)
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
      fun uu___250_16971  ->
        match uu___250_16971 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____16993 = FStar_Syntax_Syntax.null_binder k  in
            (uu____16993, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____17010 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____17010 with
             | (env1,a1) ->
                 let uu____17027 =
                   let uu____17034 = trans_aqual env1 imp  in
                   ((let uu___298_17040 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___298_17040.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___298_17040.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____17034)
                    in
                 (uu____17027, env1))

and (trans_aqual :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___251_17048  ->
      match uu___251_17048 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____17052 =
            let uu____17053 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____17053  in
          FStar_Pervasives_Native.Some uu____17052
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None

let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b  ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x,uu____17068) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x,uu____17070) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu____17073 -> FStar_Pervasives_Native.None
  
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs  ->
    FStar_List.collect
      (fun b  ->
         let uu____17090 = binder_ident b  in
         FStar_Common.list_of_option uu____17090) bs
  
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
               (fun uu___252_17126  ->
                  match uu___252_17126 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____17127 -> false))
           in
        let quals2 q =
          let uu____17140 =
            (let uu____17143 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____17143) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____17140
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____17157 = FStar_Ident.range_of_lid disc_name  in
                let uu____17158 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____17157;
                  FStar_Syntax_Syntax.sigquals = uu____17158;
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
            let uu____17197 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____17235  ->
                        match uu____17235 with
                        | (x,uu____17245) ->
                            let uu____17250 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____17250 with
                             | (field_name,uu____17258) ->
                                 let only_decl =
                                   ((let uu____17262 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____17262)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____17264 =
                                        let uu____17265 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____17265.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____17264)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____17281 =
                                       FStar_List.filter
                                         (fun uu___253_17285  ->
                                            match uu___253_17285 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____17286 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____17281
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___254_17299  ->
                                             match uu___254_17299 with
                                             | FStar_Syntax_Syntax.NoExtract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____17300 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____17302 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____17302;
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____17307 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____17307
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          (FStar_Syntax_Syntax.Delta_equational_at_level
                                             (Prims.parse_int "1"))
                                      else
                                        FStar_Syntax_Syntax.Delta_equational_at_level
                                          (Prims.parse_int "1")
                                       in
                                    let lb =
                                      let uu____17312 =
                                        let uu____17317 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____17317  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____17312;
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
                                      let uu____17321 =
                                        let uu____17322 =
                                          let uu____17329 =
                                            let uu____17332 =
                                              let uu____17333 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____17333
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____17332]  in
                                          ((false, [lb]), uu____17329)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____17322
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____17321;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____17197 FStar_List.flatten
  
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
            (lid,uu____17377,t,uu____17379,n1,uu____17381) when
            let uu____17386 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____17386 ->
            let uu____17387 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____17387 with
             | (formals,uu____17405) ->
                 (match formals with
                  | [] -> []
                  | uu____17434 ->
                      let filter_records uu___255_17450 =
                        match uu___255_17450 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____17453,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____17465 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____17467 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____17467 with
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
                      let uu____17477 = FStar_Util.first_N n1 formals  in
                      (match uu____17477 with
                       | (uu____17506,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____17540 -> []
  
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
                    let uu____17618 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____17618
                    then
                      let uu____17621 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____17621
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____17624 =
                      let uu____17629 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____17629  in
                    let uu____17630 =
                      if FStar_Util.is_some kopt
                      then
                        let uu____17635 =
                          let uu____17638 =
                            FStar_All.pipe_right kopt FStar_Util.must  in
                          FStar_Syntax_Syntax.mk_Total uu____17638  in
                        FStar_Syntax_Util.arrow typars uu____17635
                      else FStar_Syntax_Syntax.tun  in
                    let uu____17642 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____17624;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____17630;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____17642;
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
          let tycon_id uu___256_17693 =
            match uu___256_17693 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____17695,uu____17696) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____17706,uu____17707,uu____17708) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____17718,uu____17719,uu____17720) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____17750,uu____17751,uu____17752) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____17796) ->
                let uu____17797 =
                  let uu____17798 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____17798  in
                FStar_Parser_AST.mk_term uu____17797 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____17800 =
                  let uu____17801 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____17801  in
                FStar_Parser_AST.mk_term uu____17800 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____17803) ->
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
              | uu____17834 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____17842 =
                     let uu____17843 =
                       let uu____17850 = binder_to_term b  in
                       (out, uu____17850, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____17843  in
                   FStar_Parser_AST.mk_term uu____17842
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___257_17862 =
            match uu___257_17862 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____17917  ->
                       match uu____17917 with
                       | (x,t,uu____17928) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated (x, t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____17934 =
                    let uu____17935 =
                      let uu____17936 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____17936  in
                    FStar_Parser_AST.mk_term uu____17935
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____17934 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let names1 =
                  let uu____17943 = binder_idents parms  in id1 ::
                    uu____17943
                   in
                (FStar_List.iter
                   (fun uu____17961  ->
                      match uu____17961 with
                      | (f,uu____17971,uu____17972) ->
                          let uu____17977 =
                            FStar_Util.for_some
                              (fun i  -> FStar_Ident.ident_equals f i) names1
                             in
                          if uu____17977
                          then
                            let uu____17980 =
                              let uu____17985 =
                                let uu____17986 =
                                  FStar_Ident.string_of_ident f  in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu____17986
                                 in
                              (FStar_Errors.Error_FieldShadow, uu____17985)
                               in
                            FStar_Errors.raise_error uu____17980
                              f.FStar_Ident.idRange
                          else ()) fields;
                 (let uu____17988 =
                    FStar_All.pipe_right fields
                      (FStar_List.map
                         (fun uu____18015  ->
                            match uu____18015 with
                            | (x,uu____18025,uu____18026) -> x))
                     in
                  ((FStar_Parser_AST.TyconVariant
                      (id1, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp),
                           FStar_Pervasives_Native.None, false)])),
                    uu____17988)))
            | uu____18079 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___258_18118 =
            match uu___258_18118 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____18142 = typars_of_binders _env binders  in
                (match uu____18142 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____18178 =
                         let uu____18179 =
                           let uu____18180 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____18180  in
                         FStar_Parser_AST.mk_term uu____18179
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____18178 binders  in
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
            | uu____18191 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____18233 =
              FStar_List.fold_left
                (fun uu____18267  ->
                   fun uu____18268  ->
                     match (uu____18267, uu____18268) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____18337 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____18337 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____18233 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____18428 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____18428
                | uu____18429 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____18437 = desugar_abstract_tc quals env [] tc  in
              (match uu____18437 with
               | (uu____18450,uu____18451,se,uu____18453) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____18456,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____18473 =
                                 let uu____18474 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____18474  in
                               if uu____18473
                               then
                                 let uu____18475 =
                                   let uu____18480 =
                                     let uu____18481 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____18481
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____18480)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____18475
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
                           | uu____18490 ->
                               let uu____18491 =
                                 let uu____18498 =
                                   let uu____18499 =
                                     let uu____18514 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____18514)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____18499
                                    in
                                 FStar_Syntax_Syntax.mk uu____18498  in
                               uu____18491 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___299_18530 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___299_18530.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___299_18530.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___299_18530.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____18531 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____18534 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____18534
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____18547 = typars_of_binders env binders  in
              (match uu____18547 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____18581 =
                           FStar_Util.for_some
                             (fun uu___259_18583  ->
                                match uu___259_18583 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____18584 -> false) quals
                            in
                         if uu____18581
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____18589 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____18589
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____18594 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___260_18598  ->
                               match uu___260_18598 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____18599 -> false))
                        in
                     if uu____18594
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____18608 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____18608
                     then
                       let uu____18611 =
                         let uu____18618 =
                           let uu____18619 = unparen t  in
                           uu____18619.FStar_Parser_AST.tm  in
                         match uu____18618 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____18640 =
                               match FStar_List.rev args with
                               | (last_arg,uu____18670)::args_rev ->
                                   let uu____18682 =
                                     let uu____18683 = unparen last_arg  in
                                     uu____18683.FStar_Parser_AST.tm  in
                                   (match uu____18682 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____18711 -> ([], args))
                               | uu____18720 -> ([], args)  in
                             (match uu____18640 with
                              | (cattributes,args1) ->
                                  let uu____18759 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____18759))
                         | uu____18770 -> (t, [])  in
                       match uu____18611 with
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
                                  (fun uu___261_18792  ->
                                     match uu___261_18792 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____18793 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____18800)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____18824 = tycon_record_as_variant trec  in
              (match uu____18824 with
               | (t,fs) ->
                   let uu____18841 =
                     let uu____18844 =
                       let uu____18845 =
                         let uu____18854 =
                           let uu____18857 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____18857  in
                         (uu____18854, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____18845  in
                     uu____18844 :: quals  in
                   desugar_tycon env d uu____18841 [t])
          | uu____18862::uu____18863 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____19030 = et  in
                match uu____19030 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____19255 ->
                         let trec = tc  in
                         let uu____19279 = tycon_record_as_variant trec  in
                         (match uu____19279 with
                          | (t,fs) ->
                              let uu____19338 =
                                let uu____19341 =
                                  let uu____19342 =
                                    let uu____19351 =
                                      let uu____19354 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____19354  in
                                    (uu____19351, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____19342
                                   in
                                uu____19341 :: quals1  in
                              collect_tcs uu____19338 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____19441 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____19441 with
                          | (env2,uu____19501,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____19650 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____19650 with
                          | (env2,uu____19710,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____19835 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____19882 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____19882 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___263_20387  ->
                             match uu___263_20387 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____20452,uu____20453);
                                    FStar_Syntax_Syntax.sigrng = uu____20454;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____20455;
                                    FStar_Syntax_Syntax.sigmeta = uu____20456;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____20457;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____20520 =
                                     typars_of_binders env1 binders  in
                                   match uu____20520 with
                                   | (env2,tpars1) ->
                                       let uu____20547 =
                                         push_tparams env2 tpars1  in
                                       (match uu____20547 with
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
                                 let uu____20576 =
                                   let uu____20595 =
                                     mk_typ_abbrev id1 uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____20595)
                                    in
                                 [uu____20576]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____20655);
                                    FStar_Syntax_Syntax.sigrng = uu____20656;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____20658;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____20659;_},constrs,tconstr,quals1)
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
                                 let uu____20757 = push_tparams env1 tpars
                                    in
                                 (match uu____20757 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____20824  ->
                                             match uu____20824 with
                                             | (x,uu____20836) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____20840 =
                                        let uu____20867 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____20975  ->
                                                  match uu____20975 with
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
                                                        let uu____21029 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____21029
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
                                                                uu___262_21040
                                                                 ->
                                                                match uu___262_21040
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____21052
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____21060 =
                                                        let uu____21079 =
                                                          let uu____21080 =
                                                            let uu____21081 =
                                                              let uu____21096
                                                                =
                                                                let uu____21097
                                                                  =
                                                                  let uu____21100
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____21100
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____21097
                                                                 in
                                                              (name, univs1,
                                                                uu____21096,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____21081
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____21080;
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
                                                          uu____21079)
                                                         in
                                                      (name, uu____21060)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____20867
                                         in
                                      (match uu____20840 with
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
                             | uu____21315 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____21441  ->
                             match uu____21441 with
                             | (name_doc,uu____21467,uu____21468) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____21540  ->
                             match uu____21540 with
                             | (uu____21559,uu____21560,se) -> se))
                      in
                   let uu____21586 =
                     let uu____21593 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____21593 rng
                      in
                   (match uu____21586 with
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
                               (fun uu____21655  ->
                                  match uu____21655 with
                                  | (uu____21676,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____21723,tps,k,uu____21726,constrs)
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
                                  | uu____21745 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____21762  ->
                                 match uu____21762 with
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
      let uu____21805 =
        FStar_List.fold_left
          (fun uu____21840  ->
             fun b  ->
               match uu____21840 with
               | (env1,binders1) ->
                   let uu____21884 = desugar_binder env1 b  in
                   (match uu____21884 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____21907 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____21907 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____21960 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____21805 with
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
          let uu____22061 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___264_22066  ->
                    match uu___264_22066 with
                    | FStar_Syntax_Syntax.Reflectable uu____22067 -> true
                    | uu____22068 -> false))
             in
          if uu____22061
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____22071 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____22071
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
      let uu____22103 = FStar_Syntax_Util.head_and_args at1  in
      match uu____22103 with
      | (hd1,args) ->
          let uu____22154 =
            let uu____22169 =
              let uu____22170 = FStar_Syntax_Subst.compress hd1  in
              uu____22170.FStar_Syntax_Syntax.n  in
            (uu____22169, args)  in
          (match uu____22154 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(a1,uu____22193)::[]) when
               (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr)
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.fail_lax_attr)
               ->
               let uu____22228 =
                 let uu____22233 =
                   let uu____22242 =
                     FStar_Syntax_Embeddings.e_list
                       FStar_Syntax_Embeddings.e_int
                      in
                   FStar_Syntax_Embeddings.unembed uu____22242 a1  in
                 uu____22233 true FStar_Syntax_Embeddings.id_norm_cb  in
               (match uu____22228 with
                | FStar_Pervasives_Native.Some es when
                    (FStar_List.length es) > (Prims.parse_int "0") ->
                    let b =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.fail_lax_attr
                       in
                    let uu____22267 =
                      let uu____22274 =
                        FStar_List.map FStar_BigInt.to_int_fs es  in
                      (uu____22274, b)  in
                    FStar_Pervasives_Native.Some uu____22267
                | uu____22285 ->
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
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____22327) when
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
           | uu____22356 -> FStar_Pervasives_Native.None)
  
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
                  let uu____22525 = desugar_binders monad_env eff_binders  in
                  match uu____22525 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let for_free =
                        let uu____22564 =
                          let uu____22565 =
                            let uu____22574 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____22574  in
                          FStar_List.length uu____22565  in
                        uu____22564 = (Prims.parse_int "1")  in
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
                            (uu____22620,uu____22621,(FStar_Parser_AST.TyconAbbrev
                                                      (name,uu____22623,uu____22624,uu____22625),uu____22626)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____22659 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____22660 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____22672 = name_of_eff_decl decl  in
                             FStar_List.mem uu____22672 mandatory_members)
                          eff_decls
                         in
                      (match uu____22660 with
                       | (mandatory_members_decls,actions) ->
                           let uu____22689 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____22718  ->
                                     fun decl  ->
                                       match uu____22718 with
                                       | (env2,out) ->
                                           let uu____22738 =
                                             desugar_decl env2 decl  in
                                           (match uu____22738 with
                                            | (env3,ses) ->
                                                let uu____22751 =
                                                  let uu____22754 =
                                                    FStar_List.hd ses  in
                                                  uu____22754 :: out  in
                                                (env3, uu____22751)))
                                  (env1, []))
                              in
                           (match uu____22689 with
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
                                              (uu____22823,uu____22824,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____22827,
                                                 {
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.Construct
                                                     (uu____22828,(def,uu____22830)::
                                                      (cps_type,uu____22832)::[]);
                                                   FStar_Parser_AST.range =
                                                     uu____22833;
                                                   FStar_Parser_AST.level =
                                                     uu____22834;_}),doc1)::[])
                                              when Prims.op_Negation for_free
                                              ->
                                              let uu____22886 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____22886 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____22924 =
                                                     let uu____22925 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____22926 =
                                                       let uu____22927 =
                                                         desugar_term env3
                                                           def
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____22927
                                                        in
                                                     let uu____22934 =
                                                       let uu____22935 =
                                                         desugar_typ env3
                                                           cps_type
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____22935
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____22925;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____22926;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____22934
                                                     }  in
                                                   (uu____22924, doc1))
                                          | FStar_Parser_AST.Tycon
                                              (uu____22944,uu____22945,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____22948,defn),doc1)::[])
                                              when for_free ->
                                              let uu____22983 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____22983 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____23021 =
                                                     let uu____23022 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____23023 =
                                                       let uu____23024 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____23024
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____23022;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____23023;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____23021, doc1))
                                          | uu____23033 ->
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
                                    let uu____23065 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____23065
                                     in
                                  let uu____23066 =
                                    let uu____23067 =
                                      FStar_Syntax_DsEnv.fail_or env2
                                        (FStar_Syntax_DsEnv.try_lookup_definition
                                           env2) l
                                       in
                                    FStar_All.pipe_left
                                      (FStar_Syntax_Subst.close binders1)
                                      uu____23067
                                     in
                                  ([], uu____23066)  in
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
                                      let uu____23084 =
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      ([], uu____23084)  in
                                    let uu____23091 =
                                      let uu____23092 =
                                        let uu____23093 =
                                          let uu____23094 = lookup1 "repr"
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____23094
                                           in
                                        let uu____23103 = lookup1 "return"
                                           in
                                        let uu____23104 = lookup1 "bind"  in
                                        let uu____23105 =
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
                                            uu____23093;
                                          FStar_Syntax_Syntax.return_repr =
                                            uu____23103;
                                          FStar_Syntax_Syntax.bind_repr =
                                            uu____23104;
                                          FStar_Syntax_Syntax.actions =
                                            actions1;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            uu____23105
                                        }  in
                                      FStar_Syntax_Syntax.Sig_new_effect_for_free
                                        uu____23092
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____23091;
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
                                         (fun uu___265_23111  ->
                                            match uu___265_23111 with
                                            | FStar_Syntax_Syntax.Reifiable 
                                                -> true
                                            | FStar_Syntax_Syntax.Reflectable
                                                uu____23112 -> true
                                            | uu____23113 -> false)
                                         qualifiers
                                        in
                                     let un_ts =
                                       ([], FStar_Syntax_Syntax.tun)  in
                                     let uu____23127 =
                                       let uu____23128 =
                                         let uu____23129 =
                                           lookup1 "return_wp"  in
                                         let uu____23130 = lookup1 "bind_wp"
                                            in
                                         let uu____23131 =
                                           lookup1 "if_then_else"  in
                                         let uu____23132 = lookup1 "ite_wp"
                                            in
                                         let uu____23133 = lookup1 "stronger"
                                            in
                                         let uu____23134 = lookup1 "close_wp"
                                            in
                                         let uu____23135 = lookup1 "assert_p"
                                            in
                                         let uu____23136 = lookup1 "assume_p"
                                            in
                                         let uu____23137 = lookup1 "null_wp"
                                            in
                                         let uu____23138 = lookup1 "trivial"
                                            in
                                         let uu____23139 =
                                           if rr
                                           then
                                             let uu____23140 = lookup1 "repr"
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.snd
                                               uu____23140
                                           else FStar_Syntax_Syntax.tun  in
                                         let uu____23156 =
                                           if rr
                                           then lookup1 "return"
                                           else un_ts  in
                                         let uu____23158 =
                                           if rr
                                           then lookup1 "bind"
                                           else un_ts  in
                                         let uu____23160 =
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
                                             uu____23129;
                                           FStar_Syntax_Syntax.bind_wp =
                                             uu____23130;
                                           FStar_Syntax_Syntax.if_then_else =
                                             uu____23131;
                                           FStar_Syntax_Syntax.ite_wp =
                                             uu____23132;
                                           FStar_Syntax_Syntax.stronger =
                                             uu____23133;
                                           FStar_Syntax_Syntax.close_wp =
                                             uu____23134;
                                           FStar_Syntax_Syntax.assert_p =
                                             uu____23135;
                                           FStar_Syntax_Syntax.assume_p =
                                             uu____23136;
                                           FStar_Syntax_Syntax.null_wp =
                                             uu____23137;
                                           FStar_Syntax_Syntax.trivial =
                                             uu____23138;
                                           FStar_Syntax_Syntax.repr =
                                             uu____23139;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____23156;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____23158;
                                           FStar_Syntax_Syntax.actions =
                                             actions1;
                                           FStar_Syntax_Syntax.eff_attrs =
                                             uu____23160
                                         }  in
                                       FStar_Syntax_Syntax.Sig_new_effect
                                         uu____23128
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         uu____23127;
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
                                          fun uu____23186  ->
                                            match uu____23186 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____23200 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____23200
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
                let uu____23224 = desugar_binders env1 eff_binders  in
                match uu____23224 with
                | (env2,binders) ->
                    let uu____23261 =
                      let uu____23272 = head_and_args defn  in
                      match uu____23272 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____23309 ->
                                let uu____23310 =
                                  let uu____23315 =
                                    let uu____23316 =
                                      let uu____23317 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.strcat uu____23317 " not found"
                                       in
                                    Prims.strcat "Effect " uu____23316  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____23315)
                                   in
                                FStar_Errors.raise_error uu____23310
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____23319 =
                            match FStar_List.rev args with
                            | (last_arg,uu____23349)::args_rev ->
                                let uu____23361 =
                                  let uu____23362 = unparen last_arg  in
                                  uu____23362.FStar_Parser_AST.tm  in
                                (match uu____23361 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____23390 -> ([], args))
                            | uu____23399 -> ([], args)  in
                          (match uu____23319 with
                           | (cattributes,args1) ->
                               let uu____23442 = desugar_args env2 args1  in
                               let uu____23443 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____23442, uu____23443))
                       in
                    (match uu____23261 with
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
                          (let uu____23479 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____23479 with
                           | (ed_binders,uu____23493,ed_binders_opening) ->
                               let sub1 uu____23506 =
                                 match uu____23506 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____23520 =
                                         FStar_Syntax_Subst.shift_subst
                                           (FStar_List.length us)
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____23520 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____23524 =
                                       let uu____23525 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____23525)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____23524
                                  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____23534 =
                                   let uu____23535 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____23535
                                    in
                                 let uu____23550 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____23551 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____23552 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____23553 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____23554 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____23555 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____23556 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____23557 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____23558 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____23559 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____23560 =
                                   let uu____23561 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____23561
                                    in
                                 let uu____23576 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____23577 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____23578 =
                                   FStar_List.map
                                     (fun action  ->
                                        let uu____23586 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____23587 =
                                          let uu____23588 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____23588
                                           in
                                        let uu____23603 =
                                          let uu____23604 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____23604
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____23586;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____23587;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____23603
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
                                     uu____23534;
                                   FStar_Syntax_Syntax.ret_wp = uu____23550;
                                   FStar_Syntax_Syntax.bind_wp = uu____23551;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____23552;
                                   FStar_Syntax_Syntax.ite_wp = uu____23553;
                                   FStar_Syntax_Syntax.stronger = uu____23554;
                                   FStar_Syntax_Syntax.close_wp = uu____23555;
                                   FStar_Syntax_Syntax.assert_p = uu____23556;
                                   FStar_Syntax_Syntax.assume_p = uu____23557;
                                   FStar_Syntax_Syntax.null_wp = uu____23558;
                                   FStar_Syntax_Syntax.trivial = uu____23559;
                                   FStar_Syntax_Syntax.repr = uu____23560;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____23576;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____23577;
                                   FStar_Syntax_Syntax.actions = uu____23578;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____23621 =
                                     let uu____23622 =
                                       let uu____23631 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____23631
                                        in
                                     FStar_List.length uu____23622  in
                                   uu____23621 = (Prims.parse_int "1")  in
                                 let uu____23662 =
                                   let uu____23665 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____23665 quals  in
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
                                   FStar_Syntax_Syntax.sigquals = uu____23662;
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
                                             let uu____23687 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____23687
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____23689 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____23689
                                 then
                                   let reflect_lid =
                                     let uu____23693 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____23693
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
    let uu____23703 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____23703 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.strcat "  " (Prims.strcat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____23754 ->
              let uu____23755 =
                let uu____23756 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____23756
                 in
              Prims.strcat "\n  " uu____23755
          | uu____23757 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____23770  ->
               match uu____23770 with
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
          let uu____23788 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____23788
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____23790 =
          let uu____23801 = FStar_Syntax_Syntax.as_arg arg  in [uu____23801]
           in
        FStar_Syntax_Util.mk_app fv uu____23790

and (desugar_decl_aux :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      let uu____23832 = desugar_decl_noattrs env d  in
      match uu____23832 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____23850 = mk_comment_attr d  in uu____23850 :: attrs1  in
          let uu____23851 =
            FStar_List.mapi
              (fun i  ->
                 fun sigelt  ->
                   if i = (Prims.parse_int "0")
                   then
                     let uu___300_23857 = sigelt  in
                     {
                       FStar_Syntax_Syntax.sigel =
                         (uu___300_23857.FStar_Syntax_Syntax.sigel);
                       FStar_Syntax_Syntax.sigrng =
                         (uu___300_23857.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___300_23857.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___300_23857.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs = attrs2
                     }
                   else
                     (let uu___301_23859 = sigelt  in
                      let uu____23860 =
                        FStar_List.filter
                          (fun at1  ->
                             let uu____23866 = get_fail_attr false at1  in
                             FStar_Option.isNone uu____23866) attrs2
                         in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___301_23859.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___301_23859.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___301_23859.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___301_23859.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs = uu____23860
                      })) sigelts
             in
          (env1, uu____23851)

and (desugar_decl :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      let uu____23887 = desugar_decl_aux env d  in
      match uu____23887 with
      | (env1,ses) ->
          let uu____23898 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____23898)

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
      | FStar_Parser_AST.Fsdoc uu____23926 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Friend lid ->
          let uu____23931 = FStar_Syntax_DsEnv.iface env  in
          if uu____23931
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____23941 =
               let uu____23942 =
                 let uu____23943 = FStar_Syntax_DsEnv.dep_graph env  in
                 let uu____23944 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Parser_Dep.module_has_interface uu____23943
                   uu____23944
                  in
               Prims.op_Negation uu____23942  in
             if uu____23941
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____23954 =
                  let uu____23955 =
                    let uu____23956 = FStar_Syntax_DsEnv.dep_graph env  in
                    FStar_Parser_Dep.module_has_interface uu____23956 lid  in
                  Prims.op_Negation uu____23955  in
                if uu____23954
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____23966 =
                     let uu____23967 =
                       let uu____23968 = FStar_Syntax_DsEnv.dep_graph env  in
                       FStar_Parser_Dep.deps_has_implementation uu____23968
                         lid
                        in
                     Prims.op_Negation uu____23967  in
                   if uu____23966
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____23982 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____23982, [])
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
              | (FStar_Parser_AST.TyconRecord uu____24016,uu____24017)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu____24056 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1  in
          let tcs1 =
            FStar_List.map
              (fun uu____24080  ->
                 match uu____24080 with | (x,uu____24088) -> x) tcs
             in
          let uu____24093 =
            let uu____24098 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____24098 tcs1  in
          (match uu____24093 with
           | (env1,ses) ->
               let mkclass lid =
                 let uu____24115 =
                   let uu____24116 =
                     let uu____24123 =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun
                        in
                     FStar_Syntax_Syntax.mk_binder uu____24123  in
                   [uu____24116]  in
                 let uu____24136 =
                   let uu____24139 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____24142 =
                     let uu____24153 =
                       let uu____24162 =
                         let uu____24163 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____24163  in
                       FStar_Syntax_Syntax.as_arg uu____24162  in
                     [uu____24153]  in
                   FStar_Syntax_Util.mk_app uu____24139 uu____24142  in
                 FStar_Syntax_Util.abs uu____24115 uu____24136
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____24202,id1))::uu____24204 ->
                       FStar_Pervasives_Native.Some id1
                   | uu____24207::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____24211 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____24211 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id1 ->
                     let uu____24217 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     [uu____24217]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____24238) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____24248,uu____24249,uu____24250,uu____24251,uu____24252)
                     ->
                     let uu____24261 =
                       let uu____24262 =
                         let uu____24263 =
                           let uu____24270 = mkclass lid  in
                           (meths, uu____24270)  in
                         FStar_Syntax_Syntax.Sig_splice uu____24263  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____24262;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = []
                       }  in
                     [uu____24261]
                 | uu____24273 -> []  in
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
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____24303;
                    FStar_Parser_AST.prange = uu____24304;_},uu____24305)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____24314;
                    FStar_Parser_AST.prange = uu____24315;_},uu____24316)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____24331;
                         FStar_Parser_AST.prange = uu____24332;_},uu____24333);
                    FStar_Parser_AST.prange = uu____24334;_},uu____24335)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____24356;
                         FStar_Parser_AST.prange = uu____24357;_},uu____24358);
                    FStar_Parser_AST.prange = uu____24359;_},uu____24360)::[]
                   -> false
               | (p,uu____24388)::[] ->
                   let uu____24397 = is_app_pattern p  in
                   Prims.op_Negation uu____24397
               | uu____24398 -> false)
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
            let uu____24471 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____24471 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____24483 =
                     let uu____24484 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____24484.FStar_Syntax_Syntax.n  in
                   match uu____24483 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____24494) ->
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
                         | uu____24527::uu____24528 ->
                             FStar_List.map
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____24531 ->
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.collect
                                  (fun uu___266_24546  ->
                                     match uu___266_24546 with
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inl uu____24549;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____24550;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____24551;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____24552;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____24553;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____24554;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____24555;_}
                                         -> []
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____24567;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____24568;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____24569;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____24570;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____24571;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____24572;_}
                                         ->
                                         FStar_Syntax_DsEnv.lookup_letbinding_quals
                                           env
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                          in
                       let quals2 =
                         let uu____24586 =
                           FStar_All.pipe_right lets1
                             (FStar_Util.for_some
                                (fun uu____24617  ->
                                   match uu____24617 with
                                   | (uu____24630,(uu____24631,t)) ->
                                       t.FStar_Parser_AST.level =
                                         FStar_Parser_AST.Formula))
                            in
                         if uu____24586
                         then FStar_Syntax_Syntax.Logic :: quals1
                         else quals1  in
                       let lbs1 =
                         let uu____24649 =
                           FStar_All.pipe_right quals2
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract)
                            in
                         if uu____24649
                         then
                           let uu____24652 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu___302_24666 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___303_24668 = fv  in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___303_24668.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___303_24668.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___302_24666.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___302_24666.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___302_24666.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___302_24666.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___302_24666.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___302_24666.FStar_Syntax_Syntax.lbpos)
                                     }))
                              in
                           ((FStar_Pervasives_Native.fst lbs), uu____24652)
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
                   | uu____24695 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____24701 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____24720 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____24701 with
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
                       let uu___304_24756 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___304_24756.FStar_Parser_AST.prange)
                       }
                   | uu____24763 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___305_24770 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___305_24770.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___305_24770.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___305_24770.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____24806 id1 =
                   match uu____24806 with
                   | (env1,ses) ->
                       let main =
                         let uu____24827 =
                           let uu____24828 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____24828  in
                         FStar_Parser_AST.mk_term uu____24827
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
                       let uu____24878 = desugar_decl env1 id_decl  in
                       (match uu____24878 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____24896 = gather_pattern_bound_vars true pat  in
                   FStar_All.pipe_right uu____24896 FStar_Util.set_elements
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
            let uu____24919 = close_fun env t  in
            desugar_term env uu____24919  in
          let quals1 =
            let uu____24923 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____24923
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let se =
            let uu____24929 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____24929;
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
                let uu____24943 =
                  let uu____24952 = FStar_Syntax_Syntax.null_binder t  in
                  [uu____24952]  in
                let uu____24971 =
                  let uu____24974 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total
                    uu____24974
                   in
                FStar_Syntax_Util.arrow uu____24943 uu____24971
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
            let uu____25027 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____25027 with
            | FStar_Pervasives_Native.None  ->
                let uu____25030 =
                  let uu____25035 =
                    let uu____25036 =
                      let uu____25037 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.strcat uu____25037 " not found"  in
                    Prims.strcat "Effect name " uu____25036  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____25035)  in
                FStar_Errors.raise_error uu____25030
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____25041 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____25059 =
                  let uu____25062 =
                    let uu____25063 = desugar_term env t  in
                    ([], uu____25063)  in
                  FStar_Pervasives_Native.Some uu____25062  in
                (uu____25059, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____25076 =
                  let uu____25079 =
                    let uu____25080 = desugar_term env wp  in
                    ([], uu____25080)  in
                  FStar_Pervasives_Native.Some uu____25079  in
                let uu____25087 =
                  let uu____25090 =
                    let uu____25091 = desugar_term env t  in
                    ([], uu____25091)  in
                  FStar_Pervasives_Native.Some uu____25090  in
                (uu____25076, uu____25087)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____25103 =
                  let uu____25106 =
                    let uu____25107 = desugar_term env t  in
                    ([], uu____25107)  in
                  FStar_Pervasives_Native.Some uu____25106  in
                (FStar_Pervasives_Native.None, uu____25103)
             in
          (match uu____25041 with
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
            let uu____25141 =
              let uu____25142 =
                let uu____25149 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____25149, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____25142  in
            {
              FStar_Syntax_Syntax.sigel = uu____25141;
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
      let uu____25175 =
        FStar_List.fold_left
          (fun uu____25195  ->
             fun d  ->
               match uu____25195 with
               | (env1,sigelts) ->
                   let uu____25215 = desugar_decl env1 d  in
                   (match uu____25215 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____25175 with
      | (env1,sigelts) ->
          let rec forward acc uu___268_25260 =
            match uu___268_25260 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____25274,FStar_Syntax_Syntax.Sig_let uu____25275) ->
                     let uu____25288 =
                       let uu____25291 =
                         let uu___306_25292 = se2  in
                         let uu____25293 =
                           let uu____25296 =
                             FStar_List.filter
                               (fun uu___267_25310  ->
                                  match uu___267_25310 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____25314;
                                           FStar_Syntax_Syntax.vars =
                                             uu____25315;_},uu____25316);
                                      FStar_Syntax_Syntax.pos = uu____25317;
                                      FStar_Syntax_Syntax.vars = uu____25318;_}
                                      when
                                      let uu____25345 =
                                        let uu____25346 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____25346
                                         in
                                      uu____25345 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____25347 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____25296
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___306_25292.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___306_25292.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___306_25292.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___306_25292.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____25293
                         }  in
                       uu____25291 :: se1 :: acc  in
                     forward uu____25288 sigelts1
                 | uu____25352 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____25360 = forward [] sigelts  in (env1, uu____25360)
  
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
          | (FStar_Pervasives_Native.None ,uu____25421) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____25425;
               FStar_Syntax_Syntax.exports = uu____25426;
               FStar_Syntax_Syntax.is_interface = uu____25427;_},FStar_Parser_AST.Module
             (current_lid,uu____25429)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____25437) ->
              let uu____25440 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____25440
           in
        let uu____25445 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____25481 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____25481, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____25498 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____25498, mname, decls, false)
           in
        match uu____25445 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____25528 = desugar_decls env2 decls  in
            (match uu____25528 with
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
          let uu____25590 =
            (FStar_Options.interactive ()) &&
              (let uu____25592 =
                 let uu____25593 =
                   let uu____25594 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____25594  in
                 FStar_Util.get_file_extension uu____25593  in
               FStar_List.mem uu____25592 ["fsti"; "fsi"])
             in
          if uu____25590 then as_interface m else m  in
        let uu____25598 = desugar_modul_common curmod env m1  in
        match uu____25598 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____25616 = FStar_Syntax_DsEnv.pop ()  in
              (uu____25616, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul ->
      (env_t,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun m  ->
      let uu____25636 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____25636 with
      | (env1,modul,pop_when_done) ->
          let uu____25650 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____25650 with
           | (env2,modul1) ->
               ((let uu____25662 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____25662
                 then
                   let uu____25663 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____25663
                 else ());
                (let uu____25665 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____25665, modul1))))
  
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
        (fun uu____25712  ->
           let uu____25713 = desugar_modul env modul  in
           match uu____25713 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____25754  ->
           let uu____25755 = desugar_decls env decls  in
           match uu____25755 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____25809  ->
             let uu____25810 = desugar_partial_modul modul env a_modul  in
             match uu____25810 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____25908 ->
                  let t =
                    let uu____25918 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____25918  in
                  let uu____25931 =
                    let uu____25932 = FStar_Syntax_Subst.compress t  in
                    uu____25932.FStar_Syntax_Syntax.n  in
                  (match uu____25931 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____25944,uu____25945)
                       -> bs1
                   | uu____25970 -> failwith "Impossible")
               in
            let uu____25979 =
              let uu____25986 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____25986
                FStar_Syntax_Syntax.t_unit
               in
            match uu____25979 with
            | (binders,uu____25988,binders_opening) ->
                let erase_term t =
                  let uu____25996 =
                    let uu____25997 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____25997  in
                  FStar_Syntax_Subst.close binders uu____25996  in
                let erase_tscheme uu____26015 =
                  match uu____26015 with
                  | (us,t) ->
                      let t1 =
                        let uu____26035 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____26035 t  in
                      let uu____26038 =
                        let uu____26039 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____26039  in
                      ([], uu____26038)
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
                    | uu____26062 ->
                        let bs =
                          let uu____26072 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____26072  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____26112 =
                          let uu____26113 =
                            let uu____26116 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____26116  in
                          uu____26113.FStar_Syntax_Syntax.n  in
                        (match uu____26112 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____26118,uu____26119) -> bs1
                         | uu____26144 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____26151 =
                      let uu____26152 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____26152  in
                    FStar_Syntax_Subst.close binders uu____26151  in
                  let uu___307_26153 = action  in
                  let uu____26154 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____26155 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___307_26153.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___307_26153.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____26154;
                    FStar_Syntax_Syntax.action_typ = uu____26155
                  }  in
                let uu___308_26156 = ed  in
                let uu____26157 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____26158 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____26159 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____26160 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____26161 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____26162 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____26163 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____26164 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____26165 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____26166 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____26167 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____26168 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____26169 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____26170 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____26171 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____26172 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___308_26156.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___308_26156.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____26157;
                  FStar_Syntax_Syntax.signature = uu____26158;
                  FStar_Syntax_Syntax.ret_wp = uu____26159;
                  FStar_Syntax_Syntax.bind_wp = uu____26160;
                  FStar_Syntax_Syntax.if_then_else = uu____26161;
                  FStar_Syntax_Syntax.ite_wp = uu____26162;
                  FStar_Syntax_Syntax.stronger = uu____26163;
                  FStar_Syntax_Syntax.close_wp = uu____26164;
                  FStar_Syntax_Syntax.assert_p = uu____26165;
                  FStar_Syntax_Syntax.assume_p = uu____26166;
                  FStar_Syntax_Syntax.null_wp = uu____26167;
                  FStar_Syntax_Syntax.trivial = uu____26168;
                  FStar_Syntax_Syntax.repr = uu____26169;
                  FStar_Syntax_Syntax.return_repr = uu____26170;
                  FStar_Syntax_Syntax.bind_repr = uu____26171;
                  FStar_Syntax_Syntax.actions = uu____26172;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___308_26156.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___309_26188 = se  in
                  let uu____26189 =
                    let uu____26190 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____26190  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____26189;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___309_26188.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___309_26188.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___309_26188.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___309_26188.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___310_26194 = se  in
                  let uu____26195 =
                    let uu____26196 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____26196
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____26195;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___310_26194.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___310_26194.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___310_26194.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___310_26194.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____26198 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____26199 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____26199 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____26211 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____26211
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____26213 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____26213)
  