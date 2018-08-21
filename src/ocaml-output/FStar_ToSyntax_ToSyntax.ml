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
      fun uu___238_237  ->
        match uu___238_237 with
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
  fun uu___239_246  ->
    match uu___239_246 with
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
  fun uu___240_260  ->
    match uu___240_260 with
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
        | FStar_Parser_AST.PatWild uu____1666 -> acc
        | FStar_Parser_AST.PatVar
            (uu____1669,FStar_Pervasives_Native.Some
             (FStar_Parser_AST.Implicit ))
            -> acc
        | FStar_Parser_AST.PatName uu____1672 -> acc
        | FStar_Parser_AST.PatTvar uu____1673 -> acc
        | FStar_Parser_AST.PatOp uu____1680 -> acc
        | FStar_Parser_AST.PatConst uu____1681 ->
            if fail_on_patconst
            then
              FStar_Errors.raise_error
                (FStar_Errors.Error_CannotRedefineConst,
                  "Constants cannot be redefined") p.FStar_Parser_AST.prange
            else acc
        | FStar_Parser_AST.PatApp (phead,pats) ->
            gather_pattern_bound_vars_from_list (phead :: pats)
        | FStar_Parser_AST.PatVar (x,uu____1694) -> FStar_Util.set_add x acc
        | FStar_Parser_AST.PatList pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatTuple (pats,uu____1703) ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatOr pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatRecord guarded_pats ->
            let uu____1718 =
              FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
            gather_pattern_bound_vars_from_list uu____1718
        | FStar_Parser_AST.PatAscribed (pat,uu____1726) ->
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
    match projectee with | LocalBinder _0 -> true | uu____1795 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____1831 -> false
  
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
  fun uu___241_1877  ->
    match uu___241_1877 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____1884 -> failwith "Impossible"
  
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
  fun uu____1917  ->
    match uu____1917 with
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
      let uu____1997 =
        let uu____2014 =
          let uu____2017 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____2017  in
        let uu____2018 =
          let uu____2029 =
            let uu____2038 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2038)  in
          [uu____2029]  in
        (uu____2014, uu____2018)  in
      FStar_Syntax_Syntax.Tm_app uu____1997  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____2085 =
        let uu____2102 =
          let uu____2105 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____2105  in
        let uu____2106 =
          let uu____2117 =
            let uu____2126 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2126)  in
          [uu____2117]  in
        (uu____2102, uu____2106)  in
      FStar_Syntax_Syntax.Tm_app uu____2085  in
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
          let uu____2187 =
            let uu____2204 =
              let uu____2207 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____2207  in
            let uu____2208 =
              let uu____2219 =
                let uu____2228 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____2228)  in
              let uu____2235 =
                let uu____2246 =
                  let uu____2255 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____2255)  in
                [uu____2246]  in
              uu____2219 :: uu____2235  in
            (uu____2204, uu____2208)  in
          FStar_Syntax_Syntax.Tm_app uu____2187  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let (generalize_annotated_univs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun s  ->
    let bs_univnames bs =
      let uu____2313 =
        let uu____2328 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____2347  ->
               match uu____2347 with
               | ({ FStar_Syntax_Syntax.ppname = uu____2358;
                    FStar_Syntax_Syntax.index = uu____2359;
                    FStar_Syntax_Syntax.sort = t;_},uu____2361)
                   ->
                   let uu____2368 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____2368) uu____2328
         in
      FStar_All.pipe_right bs uu____2313  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____2384 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____2401 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____2427 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____2448,uu____2449,bs,t,uu____2452,uu____2453)
                            ->
                            let uu____2462 = bs_univnames bs  in
                            let uu____2465 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____2462 uu____2465
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____2468,uu____2469,t,uu____2471,uu____2472,uu____2473)
                            -> FStar_Syntax_Free.univnames t
                        | uu____2478 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____2427 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___267_2486 = s  in
        let uu____2487 =
          let uu____2488 =
            let uu____2497 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____2515,bs,t,lids1,lids2) ->
                          let uu___268_2528 = se  in
                          let uu____2529 =
                            let uu____2530 =
                              let uu____2547 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____2548 =
                                let uu____2549 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____2549 t  in
                              (lid, uvs, uu____2547, uu____2548, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____2530
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____2529;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___268_2528.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___268_2528.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___268_2528.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___268_2528.FStar_Syntax_Syntax.sigattrs)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____2563,t,tlid,n1,lids1) ->
                          let uu___269_2572 = se  in
                          let uu____2573 =
                            let uu____2574 =
                              let uu____2589 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____2589, tlid, n1, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____2574  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____2573;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___269_2572.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___269_2572.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___269_2572.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___269_2572.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____2592 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____2497, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____2488  in
        {
          FStar_Syntax_Syntax.sigel = uu____2487;
          FStar_Syntax_Syntax.sigrng =
            (uu___267_2486.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___267_2486.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___267_2486.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___267_2486.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2598,t) ->
        let uvs =
          let uu____2601 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____2601 FStar_Util.set_elements  in
        let uu___270_2606 = s  in
        let uu____2607 =
          let uu____2608 =
            let uu____2615 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____2615)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____2608  in
        {
          FStar_Syntax_Syntax.sigel = uu____2607;
          FStar_Syntax_Syntax.sigrng =
            (uu___270_2606.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___270_2606.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___270_2606.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___270_2606.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____2637 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____2640 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____2647) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____2680,(FStar_Util.Inl t,uu____2682),uu____2683)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____2730,(FStar_Util.Inr c,uu____2732),uu____2733)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____2780 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____2781,(FStar_Util.Inl t,uu____2783),uu____2784) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____2831,(FStar_Util.Inr c,uu____2833),uu____2834) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____2881 -> empty_set  in
          FStar_Util.set_union uu____2637 uu____2640  in
        let all_lb_univs =
          let uu____2885 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____2901 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____2901) empty_set)
             in
          FStar_All.pipe_right uu____2885 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___271_2911 = s  in
        let uu____2912 =
          let uu____2913 =
            let uu____2920 =
              let uu____2921 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___272_2933 = lb  in
                        let uu____2934 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____2937 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___272_2933.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____2934;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___272_2933.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____2937;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___272_2933.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___272_2933.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____2921)  in
            (uu____2920, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____2913  in
        {
          FStar_Syntax_Syntax.sigel = uu____2912;
          FStar_Syntax_Syntax.sigrng =
            (uu___271_2911.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___271_2911.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___271_2911.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___271_2911.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____2945,fml) ->
        let uvs =
          let uu____2948 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____2948 FStar_Util.set_elements  in
        let uu___273_2953 = s  in
        let uu____2954 =
          let uu____2955 =
            let uu____2962 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____2962)  in
          FStar_Syntax_Syntax.Sig_assume uu____2955  in
        {
          FStar_Syntax_Syntax.sigel = uu____2954;
          FStar_Syntax_Syntax.sigrng =
            (uu___273_2953.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___273_2953.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___273_2953.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___273_2953.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____2964,bs,c,flags1) ->
        let uvs =
          let uu____2973 =
            let uu____2976 = bs_univnames bs  in
            let uu____2979 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____2976 uu____2979  in
          FStar_All.pipe_right uu____2973 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___274_2987 = s  in
        let uu____2988 =
          let uu____2989 =
            let uu____3002 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____3003 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____3002, uu____3003, flags1)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____2989  in
        {
          FStar_Syntax_Syntax.sigel = uu____2988;
          FStar_Syntax_Syntax.sigrng =
            (uu___274_2987.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___274_2987.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___274_2987.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___274_2987.FStar_Syntax_Syntax.sigattrs)
        }
    | uu____3006 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___242_3011  ->
    match uu___242_3011 with
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
    | uu____3012 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____3024 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____3024)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____3043 =
      let uu____3044 = unparen t  in uu____3044.FStar_Parser_AST.tm  in
    match uu____3043 with
    | FStar_Parser_AST.Wild  ->
        let uu____3049 =
          let uu____3050 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____3050  in
        FStar_Util.Inr uu____3049
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____3061)) ->
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
             let uu____3126 = sum_to_universe u n1  in
             FStar_Util.Inr uu____3126
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____3137 = sum_to_universe u n1  in
             FStar_Util.Inr uu____3137
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____3148 =
               let uu____3153 =
                 let uu____3154 = FStar_Parser_AST.term_to_string t  in
                 Prims.strcat
                   "This universe might contain a sum of two universe variables "
                   uu____3154
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____3153)
                in
             FStar_Errors.raise_error uu____3148 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____3159 ->
        let rec aux t1 univargs =
          let uu____3193 =
            let uu____3194 = unparen t1  in uu____3194.FStar_Parser_AST.tm
             in
          match uu____3193 with
          | FStar_Parser_AST.App (t2,targ,uu____3201) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___243_3224  ->
                     match uu___243_3224 with
                     | FStar_Util.Inr uu____3229 -> true
                     | uu____3230 -> false) univargs
              then
                let uu____3235 =
                  let uu____3236 =
                    FStar_List.map
                      (fun uu___244_3245  ->
                         match uu___244_3245 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____3236  in
                FStar_Util.Inr uu____3235
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___245_3262  ->
                        match uu___245_3262 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____3268 -> failwith "impossible")
                     univargs
                    in
                 let uu____3269 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____3269)
          | uu____3275 ->
              let uu____3276 =
                let uu____3281 =
                  let uu____3282 =
                    let uu____3283 = FStar_Parser_AST.term_to_string t1  in
                    Prims.strcat uu____3283 " in universe context"  in
                  Prims.strcat "Unexpected term " uu____3282  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3281)  in
              FStar_Errors.raise_error uu____3276 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____3292 ->
        let uu____3293 =
          let uu____3298 =
            let uu____3299 =
              let uu____3300 = FStar_Parser_AST.term_to_string t  in
              Prims.strcat uu____3300 " in universe context"  in
            Prims.strcat "Unexpected term " uu____3299  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3298)  in
        FStar_Errors.raise_error uu____3293 t.FStar_Parser_AST.range
  
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
                   FStar_Syntax_Syntax.antiquotes = uu____3330;_});
            FStar_Syntax_Syntax.pos = uu____3331;
            FStar_Syntax_Syntax.vars = uu____3332;_})::uu____3333
        ->
        let uu____3364 =
          let uu____3369 =
            let uu____3370 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____3370
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____3369)  in
        FStar_Errors.raise_error uu____3364 e.FStar_Syntax_Syntax.pos
    | (bv,e)::uu____3373 ->
        let uu____3392 =
          let uu____3397 =
            let uu____3398 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____3398
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____3397)  in
        FStar_Errors.raise_error uu____3392 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'Auu____3407 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident,'Auu____3407) FStar_Pervasives_Native.tuple2
        Prims.list -> FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____3435 = FStar_List.hd fields  in
        match uu____3435 with
        | (f,uu____3445) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____3457 =
                match uu____3457 with
                | (f',uu____3463) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____3465 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____3465
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
              (let uu____3469 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____3469);
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
            | FStar_Syntax_Syntax.Pat_dot_term uu____3858 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_wild uu____3865 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_constant uu____3866 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_var x ->
                FStar_Util.set_add x FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_cons (uu____3868,pats1) ->
                let aux out uu____3906 =
                  match uu____3906 with
                  | (p2,uu____3918) ->
                      let intersection =
                        let uu____3926 = pat_vars p2  in
                        FStar_Util.set_intersect uu____3926 out  in
                      let uu____3929 = FStar_Util.set_is_empty intersection
                         in
                      if uu____3929
                      then
                        let uu____3932 = pat_vars p2  in
                        FStar_Util.set_union out uu____3932
                      else
                        (let duplicate_bv =
                           let uu____3937 =
                             FStar_Util.set_elements intersection  in
                           FStar_List.hd uu____3937  in
                         let uu____3940 =
                           let uu____3945 =
                             FStar_Util.format1
                               "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                               (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                              in
                           (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                             uu____3945)
                            in
                         FStar_Errors.raise_error uu____3940 r)
                   in
                FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
             in
          match pats with
          | [] -> ()
          | p1::[] ->
              let uu____3965 = pat_vars p1  in
              FStar_All.pipe_right uu____3965 (fun a236  -> ())
          | p1::ps ->
              let pvars = pat_vars p1  in
              let aux p2 =
                let uu____3993 =
                  let uu____3994 = pat_vars p2  in
                  FStar_Util.set_eq pvars uu____3994  in
                if uu____3993
                then ()
                else
                  (let nonlinear_vars =
                     let uu____4001 = pat_vars p2  in
                     FStar_Util.set_symmetric_difference pvars uu____4001  in
                   let first_nonlinear_var =
                     let uu____4005 = FStar_Util.set_elements nonlinear_vars
                        in
                     FStar_List.hd uu____4005  in
                   let uu____4008 =
                     let uu____4013 =
                       FStar_Util.format1
                         "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                         (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                        in
                     (FStar_Errors.Fatal_IncoherentPatterns, uu____4013)  in
                   FStar_Errors.raise_error uu____4008 r)
                 in
              FStar_List.iter aux ps
           in
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false ,uu____4017) -> ()
         | (true ,FStar_Parser_AST.PatVar uu____4018) -> ()
         | (true ,uu____4025) ->
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_LetMutableForVariablesOnly,
                 "let-mutable is for variables only")
               p.FStar_Parser_AST.prange);
        (let resolvex l e x =
           let uu____4048 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText))
              in
           match uu____4048 with
           | FStar_Pervasives_Native.Some y -> (l, e, y)
           | uu____4064 ->
               let uu____4067 =
                 if is_mut
                 then FStar_Syntax_DsEnv.push_bv_mutable e x
                 else FStar_Syntax_DsEnv.push_bv e x  in
               (match uu____4067 with | (e1,x1) -> ((x1 :: l), e1, x1))
            in
         let rec aux' top loc env1 p1 =
           let pos q =
             FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange  in
           let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
           let orig = p1  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr uu____4217 -> failwith "impossible"
           | FStar_Parser_AST.PatOp op ->
               let uu____4239 =
                 let uu____4240 =
                   let uu____4241 =
                     let uu____4248 =
                       let uu____4249 =
                         let uu____4254 =
                           FStar_Parser_AST.compile_op (Prims.parse_int "0")
                             op.FStar_Ident.idText op.FStar_Ident.idRange
                            in
                         (uu____4254, (op.FStar_Ident.idRange))  in
                       FStar_Ident.mk_ident uu____4249  in
                     (uu____4248, FStar_Pervasives_Native.None)  in
                   FStar_Parser_AST.PatVar uu____4241  in
                 {
                   FStar_Parser_AST.pat = uu____4240;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 }  in
               aux loc env1 uu____4239
           | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
               ((match tacopt with
                 | FStar_Pervasives_Native.None  -> ()
                 | FStar_Pervasives_Native.Some uu____4271 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                         "Type ascriptions within patterns cannot be associated with a tactic")
                       orig.FStar_Parser_AST.prange);
                (let uu____4272 = aux loc env1 p2  in
                 match uu____4272 with
                 | (loc1,env',binder,p3,annots,imp) ->
                     let annot_pat_var p4 t1 =
                       match p4.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let uu___275_4357 = p4  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var
                                  (let uu___276_4362 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___276_4362.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___276_4362.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }));
                             FStar_Syntax_Syntax.p =
                               (uu___275_4357.FStar_Syntax_Syntax.p)
                           }
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let uu___277_4364 = p4  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild
                                  (let uu___278_4369 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___278_4369.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___278_4369.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }));
                             FStar_Syntax_Syntax.p =
                               (uu___277_4364.FStar_Syntax_Syntax.p)
                           }
                       | uu____4370 when top -> p4
                       | uu____4371 ->
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                               "Type ascriptions within patterns are only allowed on variables")
                             orig.FStar_Parser_AST.prange
                        in
                     let uu____4374 =
                       match binder with
                       | LetBinder uu____4395 -> failwith "impossible"
                       | LocalBinder (x,aq) ->
                           let t1 =
                             let uu____4419 = close_fun env1 t  in
                             desugar_term env1 uu____4419  in
                           let x1 =
                             let uu___279_4421 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___279_4421.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___279_4421.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }  in
                           ([(x1, t1)], (LocalBinder (x1, aq)))
                        in
                     (match uu____4374 with
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
               let uu____4486 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
               (loc, env1, (LocalBinder (x, aq1)), uu____4486, [], imp)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____4499 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____4499, [], false)
           | FStar_Parser_AST.PatTvar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual env1 aq  in
               let uu____4520 = resolvex loc env1 x  in
               (match uu____4520 with
                | (loc1,env2,xbv) ->
                    let uu____4548 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____4548, [],
                      imp))
           | FStar_Parser_AST.PatVar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual env1 aq  in
               let uu____4569 = resolvex loc env1 x  in
               (match uu____4569 with
                | (loc1,env2,xbv) ->
                    let uu____4597 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____4597, [],
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
               let uu____4611 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, []))
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____4611, [], false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____4637;_},args)
               ->
               let uu____4643 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____4702  ->
                        match uu____4702 with
                        | (loc1,env2,annots,args1) ->
                            let uu____4779 = aux loc1 env2 arg  in
                            (match uu____4779 with
                             | (loc2,env3,uu____4824,arg1,ans,imp) ->
                                 (loc2, env3, (FStar_List.append ans annots),
                                   ((arg1, imp) :: args1)))) args
                   (loc, env1, [], [])
                  in
               (match uu____4643 with
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
                    let uu____4946 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                       in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)),
                      uu____4946, annots, false))
           | FStar_Parser_AST.PatApp uu____4961 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                 p1.FStar_Parser_AST.prange
           | FStar_Parser_AST.PatList pats ->
               let uu____4989 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____5040  ->
                        match uu____5040 with
                        | (loc1,env2,annots,pats1) ->
                            let uu____5101 = aux loc1 env2 pat  in
                            (match uu____5101 with
                             | (loc2,env3,uu____5142,pat1,ans,uu____5145) ->
                                 (loc2, env3, (FStar_List.append ans annots),
                                   (pat1 :: pats1)))) pats
                   (loc, env1, [], [])
                  in
               (match uu____4989 with
                | (loc1,env2,annots,pats1) ->
                    let pat =
                      let uu____5239 =
                        let uu____5242 =
                          let uu____5249 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange
                             in
                          pos_r uu____5249  in
                        let uu____5250 =
                          let uu____5251 =
                            let uu____5264 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Parser_Const.nil_lid
                                FStar_Syntax_Syntax.delta_constant
                                (FStar_Pervasives_Native.Some
                                   FStar_Syntax_Syntax.Data_ctor)
                               in
                            (uu____5264, [])  in
                          FStar_Syntax_Syntax.Pat_cons uu____5251  in
                        FStar_All.pipe_left uu____5242 uu____5250  in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p
                                in
                             let uu____5296 =
                               let uu____5297 =
                                 let uu____5310 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.cons_lid
                                     FStar_Syntax_Syntax.delta_constant
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Data_ctor)
                                    in
                                 (uu____5310, [(hd1, false); (tl1, false)])
                                  in
                               FStar_Syntax_Syntax.Pat_cons uu____5297  in
                             FStar_All.pipe_left (pos_r r) uu____5296) pats1
                        uu____5239
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
               let uu____5356 =
                 FStar_List.fold_left
                   (fun uu____5414  ->
                      fun p2  ->
                        match uu____5414 with
                        | (loc1,env2,annots,pats) ->
                            let uu____5492 = aux loc1 env2 p2  in
                            (match uu____5492 with
                             | (loc2,env3,uu____5537,pat,ans,uu____5540) ->
                                 (loc2, env3, (FStar_List.append ans annots),
                                   ((pat, false) :: pats))))
                   (loc, env1, [], []) args
                  in
               (match uu____5356 with
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
                    let uu____5686 =
                      FStar_Syntax_DsEnv.fail_or env2
                        (FStar_Syntax_DsEnv.try_lookup_lid env2) l
                       in
                    (match uu____5686 with
                     | (constr,uu____5714) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____5717 -> failwith "impossible"  in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (FStar_Pervasives_Native.Some
                                (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun
                            in
                         let uu____5719 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                            in
                         (loc1, env2,
                           (LocalBinder (x, FStar_Pervasives_Native.None)),
                           uu____5719, annots, false)))
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
                      (fun uu____5794  ->
                         match uu____5794 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2)))
                  in
               let args =
                 FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                   (FStar_List.map
                      (fun uu____5824  ->
                         match uu____5824 with
                         | (f,uu____5830) ->
                             let uu____5831 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____5857  ->
                                       match uu____5857 with
                                       | (g,uu____5863) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText))
                                in
                             (match uu____5831 with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Parser_AST.mk_pattern
                                    (FStar_Parser_AST.PatWild
                                       FStar_Pervasives_Native.None)
                                    p1.FStar_Parser_AST.prange
                              | FStar_Pervasives_Native.Some (uu____5868,p2)
                                  -> p2)))
                  in
               let app =
                 let uu____5875 =
                   let uu____5876 =
                     let uu____5883 =
                       let uu____5884 =
                         let uu____5885 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                                [record.FStar_Syntax_DsEnv.constrname])
                            in
                         FStar_Parser_AST.PatName uu____5885  in
                       FStar_Parser_AST.mk_pattern uu____5884
                         p1.FStar_Parser_AST.prange
                        in
                     (uu____5883, args)  in
                   FStar_Parser_AST.PatApp uu____5876  in
                 FStar_Parser_AST.mk_pattern uu____5875
                   p1.FStar_Parser_AST.prange
                  in
               let uu____5888 = aux loc env1 app  in
               (match uu____5888 with
                | (env2,e,b,p2,annots,uu____5932) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____5968 =
                            let uu____5969 =
                              let uu____5982 =
                                let uu___280_5983 = fv  in
                                let uu____5984 =
                                  let uu____5987 =
                                    let uu____5988 =
                                      let uu____5995 =
                                        FStar_All.pipe_right
                                          record.FStar_Syntax_DsEnv.fields
                                          (FStar_List.map
                                             FStar_Pervasives_Native.fst)
                                         in
                                      ((record.FStar_Syntax_DsEnv.typename),
                                        uu____5995)
                                       in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____5988
                                     in
                                  FStar_Pervasives_Native.Some uu____5987  in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___280_5983.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___280_5983.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____5984
                                }  in
                              (uu____5982, args1)  in
                            FStar_Syntax_Syntax.Pat_cons uu____5969  in
                          FStar_All.pipe_left pos uu____5968
                      | uu____6020 -> p2  in
                    (env2, e, b, p3, annots, false))
         
         and aux loc env1 p1 = aux' false loc env1 p1
          in
         let aux_maybe_or env1 p1 =
           let loc = []  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____6102 = aux' true loc env1 p2  in
               (match uu____6102 with
                | (loc1,env2,var,p3,ans,uu____6144) ->
                    let uu____6157 =
                      FStar_List.fold_left
                        (fun uu____6206  ->
                           fun p4  ->
                             match uu____6206 with
                             | (loc2,env3,ps1) ->
                                 let uu____6271 = aux' true loc2 env3 p4  in
                                 (match uu____6271 with
                                  | (loc3,env4,uu____6310,p5,ans1,uu____6313)
                                      -> (loc3, env4, ((p5, ans1) :: ps1))))
                        (loc1, env2, []) ps
                       in
                    (match uu____6157 with
                     | (loc2,env3,ps1) ->
                         let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                         (env3, var, pats)))
           | uu____6472 ->
               let uu____6473 = aux' true loc env1 p1  in
               (match uu____6473 with
                | (loc1,env2,vars,pat,ans,b) -> (env2, vars, [(pat, ans)]))
            in
         let uu____6566 = aux_maybe_or env p  in
         match uu____6566 with
         | (env1,b,pats) ->
             ((let uu____6621 =
                 FStar_List.map FStar_Pervasives_Native.fst pats  in
               check_linear_pattern_variables uu____6621
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
          let mklet x ty tacopt =
            let uu____6694 =
              let uu____6695 =
                let uu____6706 = FStar_Syntax_DsEnv.qualify env x  in
                (uu____6706, (ty, tacopt))  in
              LetBinder uu____6695  in
            (env, uu____6694, [])  in
          let op_to_ident x =
            let uu____6723 =
              let uu____6728 =
                FStar_Parser_AST.compile_op (Prims.parse_int "0")
                  x.FStar_Ident.idText x.FStar_Ident.idRange
                 in
              (uu____6728, (x.FStar_Ident.idRange))  in
            FStar_Ident.mk_ident uu____6723  in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____6746 = op_to_ident x  in
                mklet uu____6746 FStar_Syntax_Syntax.tun
                  FStar_Pervasives_Native.None
            | FStar_Parser_AST.PatVar (x,uu____6748) ->
                mklet x FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None
            | FStar_Parser_AST.PatAscribed
                ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                   FStar_Parser_AST.prange = uu____6754;_},(t,tacopt))
                ->
                let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)
                   in
                let uu____6770 = op_to_ident x  in
                let uu____6771 = desugar_term env t  in
                mklet uu____6770 uu____6771 tacopt1
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____6773);
                   FStar_Parser_AST.prange = uu____6774;_},(t,tacopt))
                ->
                let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)
                   in
                let uu____6794 = desugar_term env t  in
                mklet x uu____6794 tacopt1
            | uu____6795 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_UnexpectedPattern,
                    "Unexpected pattern at the top-level")
                  p.FStar_Parser_AST.prange
          else
            (let uu____6805 = desugar_data_pat env p is_mut  in
             match uu____6805 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1 with
                   | ({
                        FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                          uu____6834;
                        FStar_Syntax_Syntax.p = uu____6835;_},uu____6836)::[]
                       -> []
                   | ({
                        FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                          uu____6849;
                        FStar_Syntax_Syntax.p = uu____6850;_},uu____6851)::[]
                       -> []
                   | uu____6864 -> p1  in
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
  fun uu____6871  ->
    fun env  ->
      fun pat  ->
        let uu____6874 = desugar_data_pat env pat false  in
        match uu____6874 with | (env1,uu____6890,pat1) -> (env1, pat1)

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
      let uu____6909 = desugar_term_aq env e  in
      match uu____6909 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____6926 = desugar_typ_aq env e  in
      match uu____6926 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness,FStar_Const.width)
        FStar_Pervasives_Native.tuple2 ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____6936  ->
        fun range  ->
          match uu____6936 with
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
              ((let uu____6946 =
                  let uu____6947 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____6947  in
                if uu____6946
                then
                  let uu____6948 =
                    let uu____6953 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____6953)  in
                  FStar_Errors.log_issue range uu____6948
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
                  let uu____6958 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____6958 range  in
                let lid1 =
                  let uu____6962 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____6962 with
                  | FStar_Pervasives_Native.Some (intro_term,uu____6972) ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____6981 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____6981 range  in
                           let private_fv =
                             let uu____6983 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____6983 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___281_6984 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___281_6984.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___281_6984.FStar_Syntax_Syntax.vars)
                           }
                       | uu____6985 ->
                           failwith
                             (Prims.strcat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____6992 =
                        let uu____6997 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____6997)
                         in
                      FStar_Errors.raise_error uu____6992 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____7013 =
                  let uu____7020 =
                    let uu____7021 =
                      let uu____7038 =
                        let uu____7049 =
                          let uu____7058 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____7058)  in
                        [uu____7049]  in
                      (lid1, uu____7038)  in
                    FStar_Syntax_Syntax.Tm_app uu____7021  in
                  FStar_Syntax_Syntax.mk uu____7020  in
                uu____7013 FStar_Pervasives_Native.None range))

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
            let uu____7107 =
              let uu____7116 =
                (if resolve
                 then FStar_Syntax_DsEnv.try_lookup_lid_with_attributes
                 else
                   FStar_Syntax_DsEnv.try_lookup_lid_with_attributes_no_resolve)
                  env
                 in
              FStar_Syntax_DsEnv.fail_or env uu____7116 l  in
            match uu____7107 with
            | (tm,mut,attrs) ->
                let warn_if_deprecated attrs1 =
                  FStar_List.iter
                    (fun a  ->
                       match a.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_app
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____7171;
                              FStar_Syntax_Syntax.vars = uu____7172;_},args)
                           when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____7199 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____7199 " is deprecated"  in
                           let msg1 =
                             if
                               (FStar_List.length args) >
                                 (Prims.parse_int "0")
                             then
                               let uu____7209 =
                                 let uu____7210 =
                                   let uu____7213 = FStar_List.hd args  in
                                   FStar_Pervasives_Native.fst uu____7213  in
                                 uu____7210.FStar_Syntax_Syntax.n  in
                               match uu____7209 with
                               | FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_string (s,uu____7235))
                                   when
                                   Prims.op_Negation
                                     ((FStar_Util.trim_string s) = "")
                                   ->
                                   Prims.strcat msg
                                     (Prims.strcat ", use "
                                        (Prims.strcat s " instead"))
                               | uu____7236 -> msg
                             else msg  in
                           let uu____7238 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____7238
                             (FStar_Errors.Warning_DeprecatedDefinition,
                               msg1)
                       | FStar_Syntax_Syntax.Tm_fvar fv when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____7241 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____7241 " is deprecated"  in
                           let uu____7242 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____7242
                             (FStar_Errors.Warning_DeprecatedDefinition, msg)
                       | uu____7243 -> ()) attrs1
                   in
                (warn_if_deprecated attrs;
                 (let tm1 = setpos tm  in
                  if mut
                  then
                    let uu____7248 =
                      let uu____7249 =
                        let uu____7256 = mk_ref_read tm1  in
                        (uu____7256,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Mutable_rval))
                         in
                      FStar_Syntax_Syntax.Tm_meta uu____7249  in
                    FStar_All.pipe_left mk1 uu____7248
                  else tm1))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____7274 =
          let uu____7275 = unparen t  in uu____7275.FStar_Parser_AST.tm  in
        match uu____7274 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____7276; FStar_Ident.ident = uu____7277;
              FStar_Ident.nsstr = uu____7278; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____7281 ->
            let uu____7282 =
              let uu____7287 =
                let uu____7288 = FStar_Parser_AST.term_to_string t  in
                Prims.strcat "Unknown attribute " uu____7288  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____7287)  in
            FStar_Errors.raise_error uu____7282 t.FStar_Parser_AST.range
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
          let uu___282_7371 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___282_7371.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___282_7371.FStar_Syntax_Syntax.vars)
          }  in
        let uu____7374 =
          let uu____7375 = unparen top  in uu____7375.FStar_Parser_AST.tm  in
        match uu____7374 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____7380 ->
            let uu____7387 = desugar_formula env top  in (uu____7387, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____7394 = desugar_formula env t  in (uu____7394, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____7401 = desugar_formula env t  in (uu____7401, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____7425 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____7425, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____7427 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____7427, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____7435 =
                let uu____7436 =
                  let uu____7443 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____7443, args)  in
                FStar_Parser_AST.Op uu____7436  in
              FStar_Parser_AST.mk_term uu____7435 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____7446 =
              let uu____7447 =
                let uu____7448 =
                  let uu____7455 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____7455, [e])  in
                FStar_Parser_AST.Op uu____7448  in
              FStar_Parser_AST.mk_term uu____7447 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____7446
        | FStar_Parser_AST.Op (op_star,uu____7459::uu____7460::[]) when
            (let uu____7465 = FStar_Ident.text_of_id op_star  in
             uu____7465 = "*") &&
              (let uu____7467 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____7467 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____7482;_},t1::t2::[])
                  ->
                  let uu____7487 = flatten1 t1  in
                  FStar_List.append uu____7487 [t2]
              | uu____7490 -> [t]  in
            let uu____7491 =
              let uu____7516 =
                let uu____7539 =
                  let uu____7542 = unparen top  in flatten1 uu____7542  in
                FStar_All.pipe_right uu____7539
                  (FStar_List.map
                     (fun t  ->
                        let uu____7577 = desugar_typ_aq env t  in
                        match uu____7577 with
                        | (t',aq) ->
                            let uu____7588 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____7588, aq)))
                 in
              FStar_All.pipe_right uu____7516 FStar_List.unzip  in
            (match uu____7491 with
             | (targs,aqs) ->
                 let uu____7697 =
                   let uu____7702 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____7702
                    in
                 (match uu____7697 with
                  | (tup,uu____7720) ->
                      let uu____7721 =
                        mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                      (uu____7721, (join_aqs aqs))))
        | FStar_Parser_AST.Tvar a ->
            let uu____7735 =
              let uu____7736 =
                let uu____7739 =
                  FStar_Syntax_DsEnv.fail_or2
                    (FStar_Syntax_DsEnv.try_lookup_id env) a
                   in
                FStar_Pervasives_Native.fst uu____7739  in
              FStar_All.pipe_left setpos uu____7736  in
            (uu____7735, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____7751 =
              let uu____7756 =
                let uu____7757 =
                  let uu____7758 = FStar_Ident.text_of_id u  in
                  Prims.strcat uu____7758 " in non-universe context"  in
                Prims.strcat "Unexpected universe variable " uu____7757  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____7756)  in
            FStar_Errors.raise_error uu____7751 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____7769 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____7769 with
             | FStar_Pervasives_Native.None  ->
                 let uu____7776 =
                   let uu____7781 =
                     let uu____7782 = FStar_Ident.text_of_id s  in
                     Prims.strcat "Unexpected or unbound operator: "
                       uu____7782
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____7781)
                    in
                 FStar_Errors.raise_error uu____7776
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let uu____7792 =
                     let uu____7817 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____7879 = desugar_term_aq env t  in
                               match uu____7879 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____7817 FStar_List.unzip  in
                   (match uu____7792 with
                    | (args1,aqs) ->
                        let uu____8012 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____8012, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____8028)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____8043 =
              let uu___283_8044 = top  in
              let uu____8045 =
                let uu____8046 =
                  let uu____8053 =
                    let uu___284_8054 = top  in
                    let uu____8055 =
                      let uu____8056 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8056  in
                    {
                      FStar_Parser_AST.tm = uu____8055;
                      FStar_Parser_AST.range =
                        (uu___284_8054.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___284_8054.FStar_Parser_AST.level)
                    }  in
                  (uu____8053, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8046  in
              {
                FStar_Parser_AST.tm = uu____8045;
                FStar_Parser_AST.range =
                  (uu___283_8044.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___283_8044.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8043
        | FStar_Parser_AST.Construct (n1,(a,uu____8059)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____8075 =
                let uu___285_8076 = top  in
                let uu____8077 =
                  let uu____8078 =
                    let uu____8085 =
                      let uu___286_8086 = top  in
                      let uu____8087 =
                        let uu____8088 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____8088  in
                      {
                        FStar_Parser_AST.tm = uu____8087;
                        FStar_Parser_AST.range =
                          (uu___286_8086.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___286_8086.FStar_Parser_AST.level)
                      }  in
                    (uu____8085, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____8078  in
                {
                  FStar_Parser_AST.tm = uu____8077;
                  FStar_Parser_AST.range =
                    (uu___285_8076.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___285_8076.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____8075))
        | FStar_Parser_AST.Construct (n1,(a,uu____8091)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____8106 =
              let uu___287_8107 = top  in
              let uu____8108 =
                let uu____8109 =
                  let uu____8116 =
                    let uu___288_8117 = top  in
                    let uu____8118 =
                      let uu____8119 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8119  in
                    {
                      FStar_Parser_AST.tm = uu____8118;
                      FStar_Parser_AST.range =
                        (uu___288_8117.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___288_8117.FStar_Parser_AST.level)
                    }  in
                  (uu____8116, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8109  in
              {
                FStar_Parser_AST.tm = uu____8108;
                FStar_Parser_AST.range =
                  (uu___287_8107.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___287_8107.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8106
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8120; FStar_Ident.ident = uu____8121;
              FStar_Ident.nsstr = uu____8122; FStar_Ident.str = "Type0";_}
            ->
            let uu____8125 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____8125, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8126; FStar_Ident.ident = uu____8127;
              FStar_Ident.nsstr = uu____8128; FStar_Ident.str = "Type";_}
            ->
            let uu____8131 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____8131, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____8132; FStar_Ident.ident = uu____8133;
               FStar_Ident.nsstr = uu____8134; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____8152 =
              let uu____8153 =
                let uu____8154 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____8154  in
              mk1 uu____8153  in
            (uu____8152, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8155; FStar_Ident.ident = uu____8156;
              FStar_Ident.nsstr = uu____8157; FStar_Ident.str = "Effect";_}
            ->
            let uu____8160 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____8160, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8161; FStar_Ident.ident = uu____8162;
              FStar_Ident.nsstr = uu____8163; FStar_Ident.str = "True";_}
            ->
            let uu____8166 =
              let uu____8167 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8167
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8166, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8168; FStar_Ident.ident = uu____8169;
              FStar_Ident.nsstr = uu____8170; FStar_Ident.str = "False";_}
            ->
            let uu____8173 =
              let uu____8174 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8174
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8173, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____8177;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____8179 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____8179 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____8188 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_constant_at_level
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None
                     in
                  (uu____8188, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____8189 =
                    let uu____8190 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____8190 txt
                     in
                  failwith uu____8189))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8197 = desugar_name mk1 setpos env true l  in
              (uu____8197, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8200 = desugar_name mk1 setpos env true l  in
              (uu____8200, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____8211 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____8211 with
                | FStar_Pervasives_Native.Some uu____8220 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____8225 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____8225 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____8239 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____8256 =
                    let uu____8257 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____8257  in
                  (uu____8256, noaqs)
              | uu____8258 ->
                  let uu____8265 =
                    let uu____8270 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____8270)  in
                  FStar_Errors.raise_error uu____8265
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____8277 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____8277 with
              | FStar_Pervasives_Native.None  ->
                  let uu____8284 =
                    let uu____8289 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____8289)
                     in
                  FStar_Errors.raise_error uu____8284
                    top.FStar_Parser_AST.range
              | uu____8294 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____8298 = desugar_name mk1 setpos env true lid'  in
                  (uu____8298, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8314 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____8314 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____8333 ->
                       let uu____8340 =
                         FStar_Util.take
                           (fun uu____8364  ->
                              match uu____8364 with
                              | (uu____8369,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____8340 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____8414 =
                              let uu____8439 =
                                FStar_List.map
                                  (fun uu____8482  ->
                                     match uu____8482 with
                                     | (t,imp) ->
                                         let uu____8499 =
                                           desugar_term_aq env t  in
                                         (match uu____8499 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____8439
                                FStar_List.unzip
                               in
                            (match uu____8414 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____8640 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____8640, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____8658 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____8658 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.strcat "Constructor "
                             (Prims.strcat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____8665 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.strcat "Effect "
                             (Prims.strcat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____8676 =
              FStar_List.fold_left
                (fun uu____8721  ->
                   fun b  ->
                     match uu____8721 with
                     | (env1,tparams,typs) ->
                         let uu____8778 = desugar_binder env1 b  in
                         (match uu____8778 with
                          | (xopt,t1) ->
                              let uu____8807 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____8816 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____8816)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____8807 with
                               | (env2,x) ->
                                   let uu____8836 =
                                     let uu____8839 =
                                       let uu____8842 =
                                         let uu____8843 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____8843
                                          in
                                       [uu____8842]  in
                                     FStar_List.append typs uu____8839  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___289_8869 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___289_8869.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___289_8869.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____8836)))) (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      FStar_Pervasives_Native.None])
               in
            (match uu____8676 with
             | (env1,uu____8897,targs) ->
                 let uu____8919 =
                   let uu____8924 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____8924
                    in
                 (match uu____8919 with
                  | (tup,uu____8934) ->
                      let uu____8935 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_app (tup, targs))
                         in
                      (uu____8935, noaqs)))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____8954 = uncurry binders t  in
            (match uu____8954 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___246_8998 =
                   match uu___246_8998 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1  in
                       let uu____9014 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____9014
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____9038 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____9038 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____9071 = aux env [] bs  in (uu____9071, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____9080 = desugar_binder env b  in
            (match uu____9080 with
             | (FStar_Pervasives_Native.None ,uu____9091) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____9105 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____9105 with
                  | ((x,uu____9121),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____9134 =
                        let uu____9135 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____9135  in
                      (uu____9134, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let bvss =
              FStar_List.map (gather_pattern_bound_vars false) binders  in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set1::sets2 ->
                    let i = FStar_Util.set_intersect acc set1  in
                    let uu____9213 = FStar_Util.set_is_empty i  in
                    if uu____9213
                    then
                      let uu____9216 = FStar_Util.set_union acc set1  in
                      aux uu____9216 sets2
                    else
                      (let uu____9220 =
                         let uu____9221 = FStar_Util.set_elements i  in
                         FStar_List.hd uu____9221  in
                       FStar_Pervasives_Native.Some uu____9220)
                 in
              let uu____9224 = FStar_Syntax_Syntax.new_id_set ()  in
              aux uu____9224 sets  in
            ((let uu____9228 = check_disjoint bvss  in
              match uu____9228 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some id1 ->
                  let uu____9232 =
                    let uu____9237 =
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        id1.FStar_Ident.idText
                       in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____9237)
                     in
                  let uu____9238 = FStar_Ident.range_of_id id1  in
                  FStar_Errors.raise_error uu____9232 uu____9238);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern)
                 in
              let uu____9246 =
                FStar_List.fold_left
                  (fun uu____9266  ->
                     fun pat  ->
                       match uu____9266 with
                       | (env1,ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____9292,(t,FStar_Pervasives_Native.None ))
                                ->
                                let uu____9302 =
                                  let uu____9305 = free_type_vars env1 t  in
                                  FStar_List.append uu____9305 ftvs  in
                                (env1, uu____9302)
                            | FStar_Parser_AST.PatAscribed
                                (uu____9310,(t,FStar_Pervasives_Native.Some
                                             tac))
                                ->
                                let uu____9321 =
                                  let uu____9324 = free_type_vars env1 t  in
                                  let uu____9327 =
                                    let uu____9330 = free_type_vars env1 tac
                                       in
                                    FStar_List.append uu____9330 ftvs  in
                                  FStar_List.append uu____9324 uu____9327  in
                                (env1, uu____9321)
                            | uu____9335 -> (env1, ftvs))) (env, []) binders1
                 in
              match uu____9246 with
              | (uu____9344,ftv) ->
                  let ftv1 = sort_ftv ftv  in
                  let binders2 =
                    let uu____9356 =
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
                    FStar_List.append uu____9356 binders1  in
                  let rec aux env1 bs sc_pat_opt uu___247_9413 =
                    match uu___247_9413 with
                    | [] ->
                        let uu____9440 = desugar_term_aq env1 body  in
                        (match uu____9440 with
                         | (body1,aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc,pat) ->
                                   let body2 =
                                     let uu____9477 =
                                       let uu____9478 =
                                         FStar_Syntax_Syntax.pat_bvs pat  in
                                       FStar_All.pipe_right uu____9478
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder)
                                        in
                                     FStar_Syntax_Subst.close uu____9477
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
                             let uu____9547 =
                               let uu____9550 =
                                 no_annot_abs (FStar_List.rev bs) body2  in
                               setpos uu____9550  in
                             (uu____9547, aq))
                    | p::rest ->
                        let uu____9565 = desugar_binding_pat env1 p  in
                        (match uu____9565 with
                         | (env2,b,pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1,uu____9599)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____9614 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange
                                in
                             let uu____9621 =
                               match b with
                               | LetBinder uu____9662 ->
                                   failwith "Impossible"
                               | LocalBinder (x,aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None
                                        ,uu____9730) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.None ) ->
                                         let uu____9784 =
                                           let uu____9793 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____9793, p1)  in
                                         FStar_Pervasives_Native.Some
                                           uu____9784
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.Some
                                        (sc,p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____9855,uu____9856) ->
                                              let tup2 =
                                                let uu____9858 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.parse_int "2")
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____9858
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____9862 =
                                                  let uu____9869 =
                                                    let uu____9870 =
                                                      let uu____9887 =
                                                        mk1
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let uu____9890 =
                                                        let uu____9901 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let uu____9910 =
                                                          let uu____9921 =
                                                            let uu____9930 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____9930
                                                             in
                                                          [uu____9921]  in
                                                        uu____9901 ::
                                                          uu____9910
                                                         in
                                                      (uu____9887,
                                                        uu____9890)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____9870
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____9869
                                                   in
                                                uu____9862
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range
                                                 in
                                              let p2 =
                                                let uu____9981 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____9981
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____10024,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____10026,pats)) ->
                                              let tupn =
                                                let uu____10069 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    ((Prims.parse_int "1") +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10069
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10081 =
                                                  let uu____10082 =
                                                    let uu____10099 =
                                                      mk1
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____10102 =
                                                      let uu____10113 =
                                                        let uu____10124 =
                                                          let uu____10133 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____10133
                                                           in
                                                        [uu____10124]  in
                                                      FStar_List.append args
                                                        uu____10113
                                                       in
                                                    (uu____10099,
                                                      uu____10102)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____10082
                                                   in
                                                mk1 uu____10081  in
                                              let p2 =
                                                let uu____10181 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats [(p1, false)])))
                                                  uu____10181
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____10222 ->
                                              failwith "Impossible")
                                      in
                                   ((x, aq), sc_pat_opt1)
                                in
                             (match uu____9621 with
                              | (b1,sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest))
                     in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____10315,uu____10316,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____10338 =
                let uu____10339 = unparen e  in
                uu____10339.FStar_Parser_AST.tm  in
              match uu____10338 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____10349 ->
                  let uu____10350 = desugar_term_aq env e  in
                  (match uu____10350 with
                   | (head1,aq) ->
                       let uu____10363 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____10363, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____10370 ->
            let rec aux args aqs e =
              let uu____10447 =
                let uu____10448 = unparen e  in
                uu____10448.FStar_Parser_AST.tm  in
              match uu____10447 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____10466 = desugar_term_aq env t  in
                  (match uu____10466 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____10514 ->
                  let uu____10515 = desugar_term_aq env e  in
                  (match uu____10515 with
                   | (head1,aq) ->
                       let uu____10536 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____10536, (join_aqs (aq :: aqs))))
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
            let uu____10596 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____10596
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
            let uu____10648 = desugar_term_aq env t  in
            (match uu____10648 with
             | (tm,s) ->
                 let uu____10659 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____10659, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____10665 =
              let uu____10678 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____10678 then desugar_typ_aq else desugar_term_aq  in
            uu____10665 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____10733 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____10876  ->
                        match uu____10876 with
                        | (attr_opt,(p,def)) ->
                            let uu____10934 = is_app_pattern p  in
                            if uu____10934
                            then
                              let uu____10965 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____10965, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____11047 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____11047, def1)
                               | uu____11092 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____11130);
                                           FStar_Parser_AST.prange =
                                             uu____11131;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____11179 =
                                            let uu____11200 =
                                              let uu____11205 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____11205  in
                                            (uu____11200, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____11179, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____11296) ->
                                        if top_level
                                        then
                                          let uu____11331 =
                                            let uu____11352 =
                                              let uu____11357 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____11357  in
                                            (uu____11352, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____11331, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____11447 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____11478 =
                FStar_List.fold_left
                  (fun uu____11551  ->
                     fun uu____11552  ->
                       match (uu____11551, uu____11552) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____11660,uu____11661),uu____11662))
                           ->
                           let uu____11779 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____11805 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____11805 with
                                  | (env2,xx) ->
                                      let uu____11824 =
                                        let uu____11827 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____11827 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____11824))
                             | FStar_Util.Inr l ->
                                 let uu____11835 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (uu____11835, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____11779 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____11478 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____11983 =
                    match uu____11983 with
                    | (attrs_opt,(uu____12019,args,result_t),def) ->
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
                                let uu____12107 = is_comp_type env1 t  in
                                if uu____12107
                                then
                                  ((let uu____12109 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____12119 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____12119))
                                       in
                                    match uu____12109 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____12122 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____12124 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____12124))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____12122
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
                          | uu____12131 ->
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
                              let uu____12146 =
                                let uu____12147 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____12147
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____12146
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
                  let uu____12224 = desugar_term_aq env' body  in
                  (match uu____12224 with
                   | (body1,aq) ->
                       let uu____12237 =
                         let uu____12240 =
                           let uu____12241 =
                             let uu____12254 =
                               FStar_Syntax_Subst.close rec_bindings1 body1
                                in
                             ((is_rec, lbs1), uu____12254)  in
                           FStar_Syntax_Syntax.Tm_let uu____12241  in
                         FStar_All.pipe_left mk1 uu____12240  in
                       (uu____12237, aq))
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
              let uu____12334 =
                desugar_binding_pat_maybe_top top_level env pat is_mutable
                 in
              match uu____12334 with
              | (env1,binder,pat1) ->
                  let uu____12356 =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let uu____12382 = desugar_term_aq env1 t2  in
                        (match uu____12382 with
                         | (body1,aq) ->
                             let fv =
                               let uu____12396 =
                                 FStar_Syntax_Util.incr_delta_qualifier t12
                                  in
                               FStar_Syntax_Syntax.lid_as_fv l uu____12396
                                 FStar_Pervasives_Native.None
                                in
                             let uu____12397 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t12,
                                            (t12.FStar_Syntax_Syntax.pos))]),
                                      body1))
                                in
                             (uu____12397, aq))
                    | LocalBinder (x,uu____12427) ->
                        let uu____12428 = desugar_term_aq env1 t2  in
                        (match uu____12428 with
                         | (body1,aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | ({
                                    FStar_Syntax_Syntax.v =
                                      FStar_Syntax_Syntax.Pat_wild
                                      uu____12442;
                                    FStar_Syntax_Syntax.p = uu____12443;_},uu____12444)::[]
                                   -> body1
                               | uu____12457 ->
                                   let uu____12460 =
                                     let uu____12467 =
                                       let uu____12468 =
                                         let uu____12491 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         let uu____12494 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1
                                            in
                                         (uu____12491, uu____12494)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____12468
                                        in
                                     FStar_Syntax_Syntax.mk uu____12467  in
                                   uu____12460 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range
                                in
                             let uu____12534 =
                               let uu____12537 =
                                 let uu____12538 =
                                   let uu____12551 =
                                     let uu____12554 =
                                       let uu____12555 =
                                         FStar_Syntax_Syntax.mk_binder x  in
                                       [uu____12555]  in
                                     FStar_Syntax_Subst.close uu____12554
                                       body2
                                      in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t12,
                                           (t12.FStar_Syntax_Syntax.pos))]),
                                     uu____12551)
                                    in
                                 FStar_Syntax_Syntax.Tm_let uu____12538  in
                               FStar_All.pipe_left mk1 uu____12537  in
                             (uu____12534, aq))
                     in
                  (match uu____12356 with
                   | (tm,aq) ->
                       if is_mutable
                       then
                         let uu____12618 =
                           FStar_All.pipe_left mk1
                             (FStar_Syntax_Syntax.Tm_meta
                                (tm,
                                  (FStar_Syntax_Syntax.Meta_desugared
                                     FStar_Syntax_Syntax.Mutable_alloc)))
                            in
                         (uu____12618, aq)
                       else (tm, aq))
               in
            let uu____12630 = FStar_List.hd lbs  in
            (match uu____12630 with
             | (attrs,(head_pat,defn)) ->
                 let uu____12674 = is_rec || (is_app_pattern head_pat)  in
                 if uu____12674
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____12687 =
                let uu____12688 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____12688  in
              mk1 uu____12687  in
            let uu____12689 = desugar_term_aq env t1  in
            (match uu____12689 with
             | (t1',aq1) ->
                 let uu____12700 = desugar_term_aq env t2  in
                 (match uu____12700 with
                  | (t2',aq2) ->
                      let uu____12711 = desugar_term_aq env t3  in
                      (match uu____12711 with
                       | (t3',aq3) ->
                           let uu____12722 =
                             let uu____12723 =
                               let uu____12724 =
                                 let uu____12747 =
                                   let uu____12764 =
                                     let uu____12779 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t2.FStar_Parser_AST.range
                                        in
                                     (uu____12779,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____12792 =
                                     let uu____12809 =
                                       let uu____12824 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t3.FStar_Parser_AST.range
                                          in
                                       (uu____12824,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____12809]  in
                                   uu____12764 :: uu____12792  in
                                 (t1', uu____12747)  in
                               FStar_Syntax_Syntax.Tm_match uu____12724  in
                             mk1 uu____12723  in
                           (uu____12722, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____13015 =
              match uu____13015 with
              | (pat,wopt,b) ->
                  let uu____13037 = desugar_match_pat env pat  in
                  (match uu____13037 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____13068 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____13068
                          in
                       let uu____13073 = desugar_term_aq env1 b  in
                       (match uu____13073 with
                        | (b1,aq) ->
                            let uu____13086 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____13086, aq)))
               in
            let uu____13091 = desugar_term_aq env e  in
            (match uu____13091 with
             | (e1,aq) ->
                 let uu____13102 =
                   let uu____13133 =
                     let uu____13166 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____13166 FStar_List.unzip  in
                   FStar_All.pipe_right uu____13133
                     (fun uu____13296  ->
                        match uu____13296 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____13102 with
                  | (brs,aqs) ->
                      let uu____13515 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____13515, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____13549 =
              let uu____13570 = is_comp_type env t  in
              if uu____13570
              then
                let comp = desugar_comp t.FStar_Parser_AST.range env t  in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____13621 = desugar_term_aq env t  in
                 match uu____13621 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____13549 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____13713 = desugar_term_aq env e  in
                 (match uu____13713 with
                  | (e1,aq) ->
                      let uu____13724 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____13724, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____13763,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____13804 = FStar_List.hd fields  in
              match uu____13804 with | (f,uu____13816) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____13862  ->
                        match uu____13862 with
                        | (g,uu____13868) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____13874,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____13888 =
                         let uu____13893 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____13893)
                          in
                       FStar_Errors.raise_error uu____13888
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
                  let uu____13901 =
                    let uu____13912 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____13943  ->
                              match uu____13943 with
                              | (f,uu____13953) ->
                                  let uu____13954 =
                                    let uu____13955 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____13955
                                     in
                                  (uu____13954, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____13912)  in
                  FStar_Parser_AST.Construct uu____13901
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____13973 =
                      let uu____13974 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____13974  in
                    FStar_Parser_AST.mk_term uu____13973
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____13976 =
                      let uu____13989 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____14019  ->
                                match uu____14019 with
                                | (f,uu____14029) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____13989)  in
                    FStar_Parser_AST.Record uu____13976  in
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
            let uu____14089 = desugar_term_aq env recterm1  in
            (match uu____14089 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____14105;
                         FStar_Syntax_Syntax.vars = uu____14106;_},args)
                      ->
                      let uu____14132 =
                        let uu____14133 =
                          let uu____14134 =
                            let uu____14151 =
                              let uu____14154 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____14155 =
                                let uu____14158 =
                                  let uu____14159 =
                                    let uu____14166 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____14166)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____14159
                                   in
                                FStar_Pervasives_Native.Some uu____14158  in
                              FStar_Syntax_Syntax.fvar uu____14154
                                FStar_Syntax_Syntax.delta_constant
                                uu____14155
                               in
                            (uu____14151, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____14134  in
                        FStar_All.pipe_left mk1 uu____14133  in
                      (uu____14132, s)
                  | uu____14195 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____14199 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____14199 with
              | (constrname,is_rec) ->
                  let uu____14214 = desugar_term_aq env e  in
                  (match uu____14214 with
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
                       let uu____14232 =
                         let uu____14233 =
                           let uu____14234 =
                             let uu____14251 =
                               let uu____14254 =
                                 let uu____14255 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____14255
                                  in
                               FStar_Syntax_Syntax.fvar uu____14254
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1")) qual
                                in
                             let uu____14256 =
                               let uu____14267 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____14267]  in
                             (uu____14251, uu____14256)  in
                           FStar_Syntax_Syntax.Tm_app uu____14234  in
                         FStar_All.pipe_left mk1 uu____14233  in
                       (uu____14232, s))))
        | FStar_Parser_AST.NamedTyp (uu____14304,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____14313 =
              let uu____14314 = FStar_Syntax_Subst.compress tm  in
              uu____14314.FStar_Syntax_Syntax.n  in
            (match uu____14313 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____14322 =
                   let uu___290_14323 =
                     let uu____14324 =
                       let uu____14325 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____14325  in
                     FStar_Syntax_Util.exp_string uu____14324  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___290_14323.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___290_14323.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____14322, noaqs)
             | uu____14326 ->
                 let uu____14327 =
                   let uu____14332 =
                     let uu____14333 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.strcat "VQuote, expected an fvar, got: "
                       uu____14333
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____14332)  in
                 FStar_Errors.raise_error uu____14327
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____14339 = desugar_term_aq env e  in
            (match uu____14339 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____14351 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____14351, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____14356 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____14357 =
              let uu____14358 =
                let uu____14365 = desugar_term env e  in (bv, uu____14365)
                 in
              [uu____14358]  in
            (uu____14356, uu____14357)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____14390 =
              let uu____14391 =
                let uu____14392 =
                  let uu____14399 = desugar_term env e  in (uu____14399, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____14392  in
              FStar_All.pipe_left mk1 uu____14391  in
            (uu____14390, noaqs)
        | uu____14404 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____14405 = desugar_formula env top  in
            (uu____14405, noaqs)
        | uu____14406 ->
            let uu____14407 =
              let uu____14412 =
                let uu____14413 = FStar_Parser_AST.term_to_string top  in
                Prims.strcat "Unexpected term: " uu____14413  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____14412)  in
            FStar_Errors.raise_error uu____14407 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____14419 -> false
    | uu____14428 -> true

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
           (fun uu____14465  ->
              match uu____14465 with
              | (a,imp) ->
                  let uu____14478 = desugar_term env a  in
                  arg_withimp_e imp uu____14478))

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
        let is_requires uu____14510 =
          match uu____14510 with
          | (t1,uu____14516) ->
              let uu____14517 =
                let uu____14518 = unparen t1  in
                uu____14518.FStar_Parser_AST.tm  in
              (match uu____14517 with
               | FStar_Parser_AST.Requires uu____14519 -> true
               | uu____14526 -> false)
           in
        let is_ensures uu____14536 =
          match uu____14536 with
          | (t1,uu____14542) ->
              let uu____14543 =
                let uu____14544 = unparen t1  in
                uu____14544.FStar_Parser_AST.tm  in
              (match uu____14543 with
               | FStar_Parser_AST.Ensures uu____14545 -> true
               | uu____14552 -> false)
           in
        let is_app head1 uu____14567 =
          match uu____14567 with
          | (t1,uu____14573) ->
              let uu____14574 =
                let uu____14575 = unparen t1  in
                uu____14575.FStar_Parser_AST.tm  in
              (match uu____14574 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____14577;
                      FStar_Parser_AST.level = uu____14578;_},uu____14579,uu____14580)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____14581 -> false)
           in
        let is_smt_pat uu____14591 =
          match uu____14591 with
          | (t1,uu____14597) ->
              let uu____14598 =
                let uu____14599 = unparen t1  in
                uu____14599.FStar_Parser_AST.tm  in
              (match uu____14598 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____14602);
                             FStar_Parser_AST.range = uu____14603;
                             FStar_Parser_AST.level = uu____14604;_},uu____14605)::uu____14606::[])
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
                             FStar_Parser_AST.range = uu____14645;
                             FStar_Parser_AST.level = uu____14646;_},uu____14647)::uu____14648::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
               | uu____14673 -> false)
           in
        let is_decreases = is_app "decreases"  in
        let pre_process_comp_typ t1 =
          let uu____14705 = head_and_args t1  in
          match uu____14705 with
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
                   let thunk_ens uu____14803 =
                     match uu____14803 with
                     | (e,i) ->
                         let uu____14814 = thunk_ens_ e  in (uu____14814, i)
                      in
                   let fail_lemma uu____14826 =
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
                         let uu____14906 =
                           let uu____14913 =
                             let uu____14920 = thunk_ens ens  in
                             [uu____14920; nil_pat]  in
                           req_true :: uu____14913  in
                         unit_tm :: uu____14906
                     | req::ens::[] when
                         (is_requires req) && (is_ensures ens) ->
                         let uu____14967 =
                           let uu____14974 =
                             let uu____14981 = thunk_ens ens  in
                             [uu____14981; nil_pat]  in
                           req :: uu____14974  in
                         unit_tm :: uu____14967
                     | ens::smtpat::[] when
                         (((let uu____15030 = is_requires ens  in
                            Prims.op_Negation uu____15030) &&
                             (let uu____15032 = is_smt_pat ens  in
                              Prims.op_Negation uu____15032))
                            &&
                            (let uu____15034 = is_decreases ens  in
                             Prims.op_Negation uu____15034))
                           && (is_smt_pat smtpat)
                         ->
                         let uu____15035 =
                           let uu____15042 =
                             let uu____15049 = thunk_ens ens  in
                             [uu____15049; smtpat]  in
                           req_true :: uu____15042  in
                         unit_tm :: uu____15035
                     | ens::dec::[] when
                         (is_ensures ens) && (is_decreases dec) ->
                         let uu____15096 =
                           let uu____15103 =
                             let uu____15110 = thunk_ens ens  in
                             [uu____15110; nil_pat; dec]  in
                           req_true :: uu____15103  in
                         unit_tm :: uu____15096
                     | ens::dec::smtpat::[] when
                         ((is_ensures ens) && (is_decreases dec)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____15170 =
                           let uu____15177 =
                             let uu____15184 = thunk_ens ens  in
                             [uu____15184; smtpat; dec]  in
                           req_true :: uu____15177  in
                         unit_tm :: uu____15170
                     | req::ens::dec::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_decreases dec)
                         ->
                         let uu____15244 =
                           let uu____15251 =
                             let uu____15258 = thunk_ens ens  in
                             [uu____15258; nil_pat; dec]  in
                           req :: uu____15251  in
                         unit_tm :: uu____15244
                     | req::ens::smtpat::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____15318 =
                           let uu____15325 =
                             let uu____15332 = thunk_ens ens  in
                             [uu____15332; smtpat]  in
                           req :: uu____15325  in
                         unit_tm :: uu____15318
                     | req::ens::dec::smtpat::[] when
                         (((is_requires req) && (is_ensures ens)) &&
                            (is_smt_pat smtpat))
                           && (is_decreases dec)
                         ->
                         let uu____15397 =
                           let uu____15404 =
                             let uu____15411 = thunk_ens ens  in
                             [uu____15411; dec; smtpat]  in
                           req :: uu____15404  in
                         unit_tm :: uu____15397
                     | _other -> fail_lemma ()  in
                   let head_and_attributes =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) lemma
                      in
                   (head_and_attributes, args1)
               | FStar_Parser_AST.Name l when
                   FStar_Syntax_DsEnv.is_effect_name env l ->
                   let uu____15473 =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) l
                      in
                   (uu____15473, args)
               | FStar_Parser_AST.Name l when
                   (let uu____15501 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____15501
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   let uu____15502 =
                     let uu____15509 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_Tot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____15509, [])  in
                   (uu____15502, args)
               | FStar_Parser_AST.Name l when
                   (let uu____15527 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____15527
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                   ->
                   let uu____15528 =
                     let uu____15535 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_GTot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____15535, [])  in
                   (uu____15528, args)
               | FStar_Parser_AST.Name l when
                   (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                      ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                     || ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                   ->
                   let uu____15551 =
                     let uu____15558 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_Tot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____15558, [])  in
                   (uu____15551, [(t1, FStar_Parser_AST.Nothing)])
               | uu____15581 ->
                   let default_effect =
                     let uu____15583 = FStar_Options.ml_ish ()  in
                     if uu____15583
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____15586 =
                           FStar_Options.warn_default_effects ()  in
                         if uu____15586
                         then
                           FStar_Errors.log_issue
                             head1.FStar_Parser_AST.range
                             (FStar_Errors.Warning_UseDefaultEffect,
                               "Using default effect Tot")
                         else ());
                        FStar_Parser_Const.effect_Tot_lid)
                      in
                   let uu____15588 =
                     let uu____15595 =
                       FStar_Ident.set_lid_range default_effect
                         head1.FStar_Parser_AST.range
                        in
                     (uu____15595, [])  in
                   (uu____15588, [(t1, FStar_Parser_AST.Nothing)]))
           in
        let uu____15618 = pre_process_comp_typ t  in
        match uu____15618 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____15667 =
                  let uu____15672 =
                    let uu____15673 = FStar_Syntax_Print.lid_to_string eff
                       in
                    FStar_Util.format1 "Not enough args to effect %s"
                      uu____15673
                     in
                  (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____15672)  in
                fail1 uu____15667)
             else ();
             (let is_universe uu____15684 =
                match uu____15684 with
                | (uu____15689,imp) -> imp = FStar_Parser_AST.UnivApp  in
              let uu____15691 = FStar_Util.take is_universe args  in
              match uu____15691 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____15750  ->
                         match uu____15750 with
                         | (u,imp) -> desugar_universe u) universes
                     in
                  let uu____15757 =
                    let uu____15772 = FStar_List.hd args1  in
                    let uu____15781 = FStar_List.tl args1  in
                    (uu____15772, uu____15781)  in
                  (match uu____15757 with
                   | (result_arg,rest) ->
                       let result_typ =
                         desugar_typ env
                           (FStar_Pervasives_Native.fst result_arg)
                          in
                       let rest1 = desugar_args env rest  in
                       let uu____15836 =
                         let is_decrease uu____15874 =
                           match uu____15874 with
                           | (t1,uu____15884) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.pos = uu____15894;
                                       FStar_Syntax_Syntax.vars = uu____15895;_},uu____15896::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.decreases_lid
                                | uu____15935 -> false)
                            in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease)
                          in
                       (match uu____15836 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____16051  ->
                                      match uu____16051 with
                                      | (t1,uu____16061) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____16070,(arg,uu____16072)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____16111 -> failwith "impos")))
                               in
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
                                | uu____16128 -> false  in
                              (((is_empty decreases_clause) &&
                                  (is_empty rest2))
                                 && (is_empty cattributes))
                                && (is_empty universes1)
                               in
                            let uu____16139 =
                              no_additional_args &&
                                (FStar_Ident.lid_equals eff
                                   FStar_Parser_Const.effect_Tot_lid)
                               in
                            if uu____16139
                            then FStar_Syntax_Syntax.mk_Total result_typ
                            else
                              (let uu____16143 =
                                 no_additional_args &&
                                   (FStar_Ident.lid_equals eff
                                      FStar_Parser_Const.effect_GTot_lid)
                                  in
                               if uu____16143
                               then FStar_Syntax_Syntax.mk_GTotal result_typ
                               else
                                 (let flags1 =
                                    let uu____16150 =
                                      FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_Lemma_lid
                                       in
                                    if uu____16150
                                    then [FStar_Syntax_Syntax.LEMMA]
                                    else
                                      (let uu____16154 =
                                         FStar_Ident.lid_equals eff
                                           FStar_Parser_Const.effect_Tot_lid
                                          in
                                       if uu____16154
                                       then [FStar_Syntax_Syntax.TOTAL]
                                       else
                                         (let uu____16158 =
                                            FStar_Ident.lid_equals eff
                                              FStar_Parser_Const.effect_ML_lid
                                             in
                                          if uu____16158
                                          then [FStar_Syntax_Syntax.MLEFFECT]
                                          else
                                            (let uu____16162 =
                                               FStar_Ident.lid_equals eff
                                                 FStar_Parser_Const.effect_GTot_lid
                                                in
                                             if uu____16162
                                             then
                                               [FStar_Syntax_Syntax.SOMETRIVIAL]
                                             else [])))
                                     in
                                  let flags2 =
                                    FStar_List.append flags1 cattributes  in
                                  let rest3 =
                                    let uu____16180 =
                                      FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_Lemma_lid
                                       in
                                    if uu____16180
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
                                                  let uu____16269 =
                                                    FStar_Ident.set_lid_range
                                                      FStar_Parser_Const.pattern_lid
                                                      pat.FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_Syntax.fvar
                                                    uu____16269
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
                                            | uu____16290 -> pat  in
                                          let uu____16291 =
                                            let uu____16302 =
                                              let uu____16313 =
                                                let uu____16322 =
                                                  FStar_Syntax_Syntax.mk
                                                    (FStar_Syntax_Syntax.Tm_meta
                                                       (pat1,
                                                         (FStar_Syntax_Syntax.Meta_desugared
                                                            FStar_Syntax_Syntax.Meta_smt_pat)))
                                                    FStar_Pervasives_Native.None
                                                    pat1.FStar_Syntax_Syntax.pos
                                                   in
                                                (uu____16322, aq)  in
                                              [uu____16313]  in
                                            ens :: uu____16302  in
                                          req :: uu____16291
                                      | uu____16363 -> rest2
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
        | uu____16387 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___291_16408 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___291_16408.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___291_16408.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___292_16450 = b  in
             {
               FStar_Parser_AST.b = (uu___292_16450.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___292_16450.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___292_16450.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____16513 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____16513)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____16526 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____16526 with
             | (env1,a1) ->
                 let a2 =
                   let uu___293_16536 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___293_16536.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___293_16536.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____16562 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____16576 =
                     let uu____16579 =
                       let uu____16580 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____16580]  in
                     no_annot_abs uu____16579 body2  in
                   FStar_All.pipe_left setpos uu____16576  in
                 let uu____16601 =
                   let uu____16602 =
                     let uu____16619 =
                       let uu____16622 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____16622
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____16623 =
                       let uu____16634 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____16634]  in
                     (uu____16619, uu____16623)  in
                   FStar_Syntax_Syntax.Tm_app uu____16602  in
                 FStar_All.pipe_left mk1 uu____16601)
        | uu____16673 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____16753 = q (rest, pats, body)  in
              let uu____16760 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____16753 uu____16760
                FStar_Parser_AST.Formula
               in
            let uu____16761 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____16761 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____16770 -> failwith "impossible"  in
      let uu____16773 =
        let uu____16774 = unparen f  in uu____16774.FStar_Parser_AST.tm  in
      match uu____16773 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____16781,uu____16782) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____16793,uu____16794) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____16825 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____16825
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____16861 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____16861
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____16904 -> desugar_term env f

and (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                FStar_Pervasives_Native.tuple2 Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bs  ->
      let uu____16909 =
        FStar_List.fold_left
          (fun uu____16942  ->
             fun b  ->
               match uu____16942 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___294_16986 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___294_16986.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___294_16986.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___294_16986.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____17001 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____17001 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___295_17019 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___295_17019.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___295_17019.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____17020 =
                               let uu____17027 =
                                 let uu____17032 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____17032)  in
                               uu____17027 :: out  in
                             (env2, uu____17020))
                    | uu____17043 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____16909 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

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
          let uu____17114 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____17114)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____17119 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____17119)
      | FStar_Parser_AST.TVariable x ->
          let uu____17123 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____17123)
      | FStar_Parser_AST.NoName t ->
          let uu____17127 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____17127)
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
      fun uu___248_17135  ->
        match uu___248_17135 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____17157 = FStar_Syntax_Syntax.null_binder k  in
            (uu____17157, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____17174 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____17174 with
             | (env1,a1) ->
                 let uu____17191 =
                   let uu____17198 = trans_aqual env1 imp  in
                   ((let uu___296_17204 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___296_17204.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___296_17204.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____17198)
                    in
                 (uu____17191, env1))

and (trans_aqual :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___249_17212  ->
      match uu___249_17212 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____17216 =
            let uu____17217 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____17217  in
          FStar_Pervasives_Native.Some uu____17216
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
               (fun uu___250_17253  ->
                  match uu___250_17253 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____17254 -> false))
           in
        let quals2 q =
          let uu____17267 =
            (let uu____17270 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____17270) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____17267
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____17284 = FStar_Ident.range_of_lid disc_name  in
                let uu____17285 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____17284;
                  FStar_Syntax_Syntax.sigquals = uu____17285;
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
            let uu____17324 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____17362  ->
                        match uu____17362 with
                        | (x,uu____17372) ->
                            let uu____17377 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____17377 with
                             | (field_name,uu____17385) ->
                                 let only_decl =
                                   ((let uu____17389 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____17389)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____17391 =
                                        let uu____17392 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____17392.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____17391)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____17408 =
                                       FStar_List.filter
                                         (fun uu___251_17412  ->
                                            match uu___251_17412 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____17413 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____17408
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___252_17426  ->
                                             match uu___252_17426 with
                                             | FStar_Syntax_Syntax.NoExtract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____17427 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____17429 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____17429;
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____17434 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____17434
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          (FStar_Syntax_Syntax.Delta_equational_at_level
                                             (Prims.parse_int "1"))
                                      else
                                        FStar_Syntax_Syntax.Delta_equational_at_level
                                          (Prims.parse_int "1")
                                       in
                                    let lb =
                                      let uu____17439 =
                                        let uu____17444 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____17444  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____17439;
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
                                      let uu____17448 =
                                        let uu____17449 =
                                          let uu____17456 =
                                            let uu____17459 =
                                              let uu____17460 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____17460
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____17459]  in
                                          ((false, [lb]), uu____17456)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____17449
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____17448;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____17324 FStar_List.flatten
  
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
            (lid,uu____17504,t,uu____17506,n1,uu____17508) when
            let uu____17513 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____17513 ->
            let uu____17514 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____17514 with
             | (formals,uu____17532) ->
                 (match formals with
                  | [] -> []
                  | uu____17561 ->
                      let filter_records uu___253_17577 =
                        match uu___253_17577 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____17580,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____17592 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____17594 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____17594 with
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
                      let uu____17604 = FStar_Util.first_N n1 formals  in
                      (match uu____17604 with
                       | (uu____17633,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____17667 -> []
  
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
                    let uu____17745 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____17745
                    then
                      let uu____17748 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____17748
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____17751 =
                      let uu____17756 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____17756  in
                    let uu____17757 =
                      if FStar_Util.is_some kopt
                      then
                        let uu____17762 =
                          let uu____17765 =
                            FStar_All.pipe_right kopt FStar_Util.must  in
                          FStar_Syntax_Syntax.mk_Total uu____17765  in
                        FStar_Syntax_Util.arrow typars uu____17762
                      else FStar_Syntax_Syntax.tun  in
                    let uu____17769 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____17751;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____17757;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____17769;
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
          let tycon_id uu___254_17820 =
            match uu___254_17820 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____17822,uu____17823) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____17833,uu____17834,uu____17835) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____17845,uu____17846,uu____17847) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____17877,uu____17878,uu____17879) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____17923) ->
                let uu____17924 =
                  let uu____17925 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____17925  in
                FStar_Parser_AST.mk_term uu____17924 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____17927 =
                  let uu____17928 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____17928  in
                FStar_Parser_AST.mk_term uu____17927 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____17930) ->
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
              | uu____17961 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____17969 =
                     let uu____17970 =
                       let uu____17977 = binder_to_term b  in
                       (out, uu____17977, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____17970  in
                   FStar_Parser_AST.mk_term uu____17969
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___255_17989 =
            match uu___255_17989 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____18045  ->
                       match uu____18045 with
                       | (x,t,uu____18056) ->
                           let uu____18061 =
                             let uu____18062 =
                               let uu____18067 =
                                 FStar_Syntax_Util.mangle_field_name x  in
                               (uu____18067, t)  in
                             FStar_Parser_AST.Annotated uu____18062  in
                           FStar_Parser_AST.mk_binder uu____18061
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____18069 =
                    let uu____18070 =
                      let uu____18071 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____18071  in
                    FStar_Parser_AST.mk_term uu____18070
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____18069 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let uu____18075 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____18102  ->
                          match uu____18102 with
                          | (x,uu____18112,uu____18113) ->
                              FStar_Syntax_Util.unmangle_field_name x))
                   in
                ((FStar_Parser_AST.TyconVariant
                    (id1, parms, kopt,
                      [(constrName, (FStar_Pervasives_Native.Some constrTyp),
                         FStar_Pervasives_Native.None, false)])),
                  uu____18075)
            | uu____18166 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___256_18205 =
            match uu___256_18205 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____18229 = typars_of_binders _env binders  in
                (match uu____18229 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____18265 =
                         let uu____18266 =
                           let uu____18267 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____18267  in
                         FStar_Parser_AST.mk_term uu____18266
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____18265 binders  in
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
            | uu____18278 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____18320 =
              FStar_List.fold_left
                (fun uu____18354  ->
                   fun uu____18355  ->
                     match (uu____18354, uu____18355) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____18424 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____18424 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____18320 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____18515 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____18515
                | uu____18516 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____18524 = desugar_abstract_tc quals env [] tc  in
              (match uu____18524 with
               | (uu____18537,uu____18538,se,uu____18540) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____18543,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____18560 =
                                 let uu____18561 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____18561  in
                               if uu____18560
                               then
                                 let uu____18562 =
                                   let uu____18567 =
                                     let uu____18568 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____18568
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____18567)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____18562
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
                           | uu____18577 ->
                               let uu____18578 =
                                 let uu____18585 =
                                   let uu____18586 =
                                     let uu____18601 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____18601)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____18586
                                    in
                                 FStar_Syntax_Syntax.mk uu____18585  in
                               uu____18578 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___297_18617 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___297_18617.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___297_18617.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___297_18617.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____18618 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____18621 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____18621
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____18634 = typars_of_binders env binders  in
              (match uu____18634 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____18668 =
                           FStar_Util.for_some
                             (fun uu___257_18670  ->
                                match uu___257_18670 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____18671 -> false) quals
                            in
                         if uu____18668
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____18676 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____18676
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____18681 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___258_18685  ->
                               match uu___258_18685 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____18686 -> false))
                        in
                     if uu____18681
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____18695 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____18695
                     then
                       let uu____18698 =
                         let uu____18705 =
                           let uu____18706 = unparen t  in
                           uu____18706.FStar_Parser_AST.tm  in
                         match uu____18705 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____18727 =
                               match FStar_List.rev args with
                               | (last_arg,uu____18757)::args_rev ->
                                   let uu____18769 =
                                     let uu____18770 = unparen last_arg  in
                                     uu____18770.FStar_Parser_AST.tm  in
                                   (match uu____18769 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____18798 -> ([], args))
                               | uu____18807 -> ([], args)  in
                             (match uu____18727 with
                              | (cattributes,args1) ->
                                  let uu____18846 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____18846))
                         | uu____18857 -> (t, [])  in
                       match uu____18698 with
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
                                  (fun uu___259_18879  ->
                                     match uu___259_18879 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____18880 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____18887)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____18911 = tycon_record_as_variant trec  in
              (match uu____18911 with
               | (t,fs) ->
                   let uu____18928 =
                     let uu____18931 =
                       let uu____18932 =
                         let uu____18941 =
                           let uu____18944 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____18944  in
                         (uu____18941, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____18932  in
                     uu____18931 :: quals  in
                   desugar_tycon env d uu____18928 [t])
          | uu____18949::uu____18950 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____19117 = et  in
                match uu____19117 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____19342 ->
                         let trec = tc  in
                         let uu____19366 = tycon_record_as_variant trec  in
                         (match uu____19366 with
                          | (t,fs) ->
                              let uu____19425 =
                                let uu____19428 =
                                  let uu____19429 =
                                    let uu____19438 =
                                      let uu____19441 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____19441  in
                                    (uu____19438, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____19429
                                   in
                                uu____19428 :: quals1  in
                              collect_tcs uu____19425 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____19528 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____19528 with
                          | (env2,uu____19588,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____19737 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____19737 with
                          | (env2,uu____19797,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____19922 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____19969 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____19969 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___261_20474  ->
                             match uu___261_20474 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____20539,uu____20540);
                                    FStar_Syntax_Syntax.sigrng = uu____20541;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____20542;
                                    FStar_Syntax_Syntax.sigmeta = uu____20543;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____20544;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____20607 =
                                     typars_of_binders env1 binders  in
                                   match uu____20607 with
                                   | (env2,tpars1) ->
                                       let uu____20634 =
                                         push_tparams env2 tpars1  in
                                       (match uu____20634 with
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
                                 let uu____20663 =
                                   let uu____20682 =
                                     mk_typ_abbrev id1 uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____20682)
                                    in
                                 [uu____20663]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____20742);
                                    FStar_Syntax_Syntax.sigrng = uu____20743;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____20745;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____20746;_},constrs,tconstr,quals1)
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
                                 let uu____20844 = push_tparams env1 tpars
                                    in
                                 (match uu____20844 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____20911  ->
                                             match uu____20911 with
                                             | (x,uu____20923) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____20927 =
                                        let uu____20954 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____21062  ->
                                                  match uu____21062 with
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
                                                        let uu____21116 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____21116
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
                                                                uu___260_21127
                                                                 ->
                                                                match uu___260_21127
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____21139
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____21147 =
                                                        let uu____21166 =
                                                          let uu____21167 =
                                                            let uu____21168 =
                                                              let uu____21183
                                                                =
                                                                let uu____21184
                                                                  =
                                                                  let uu____21187
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____21187
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____21184
                                                                 in
                                                              (name, univs1,
                                                                uu____21183,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____21168
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____21167;
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
                                                          uu____21166)
                                                         in
                                                      (name, uu____21147)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____20954
                                         in
                                      (match uu____20927 with
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
                             | uu____21402 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____21528  ->
                             match uu____21528 with
                             | (name_doc,uu____21554,uu____21555) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____21627  ->
                             match uu____21627 with
                             | (uu____21646,uu____21647,se) -> se))
                      in
                   let uu____21673 =
                     let uu____21680 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____21680 rng
                      in
                   (match uu____21673 with
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
                               (fun uu____21742  ->
                                  match uu____21742 with
                                  | (uu____21763,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____21810,tps,k,uu____21813,constrs)
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
                                  | uu____21832 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____21849  ->
                                 match uu____21849 with
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
      let uu____21892 =
        FStar_List.fold_left
          (fun uu____21927  ->
             fun b  ->
               match uu____21927 with
               | (env1,binders1) ->
                   let uu____21971 = desugar_binder env1 b  in
                   (match uu____21971 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____21994 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____21994 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____22047 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____21892 with
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
          let uu____22148 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___262_22153  ->
                    match uu___262_22153 with
                    | FStar_Syntax_Syntax.Reflectable uu____22154 -> true
                    | uu____22155 -> false))
             in
          if uu____22148
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____22158 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____22158
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
      let uu____22190 = FStar_Syntax_Util.head_and_args at1  in
      match uu____22190 with
      | (hd1,args) ->
          let uu____22241 =
            let uu____22256 =
              let uu____22257 = FStar_Syntax_Subst.compress hd1  in
              uu____22257.FStar_Syntax_Syntax.n  in
            (uu____22256, args)  in
          (match uu____22241 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(a1,uu____22280)::[]) when
               (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr)
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.fail_lax_attr)
               ->
               let uu____22315 =
                 let uu____22320 =
                   let uu____22329 =
                     FStar_Syntax_Embeddings.e_list
                       FStar_Syntax_Embeddings.e_int
                      in
                   FStar_Syntax_Embeddings.unembed uu____22329 a1  in
                 uu____22320 true FStar_Syntax_Embeddings.id_norm_cb  in
               (match uu____22315 with
                | FStar_Pervasives_Native.Some es when
                    (FStar_List.length es) > (Prims.parse_int "0") ->
                    let b =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.fail_lax_attr
                       in
                    let uu____22354 =
                      let uu____22361 =
                        FStar_List.map FStar_BigInt.to_int_fs es  in
                      (uu____22361, b)  in
                    FStar_Pervasives_Native.Some uu____22354
                | uu____22372 ->
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
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____22414) when
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
           | uu____22443 -> FStar_Pervasives_Native.None)
  
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
                  let uu____22612 = desugar_binders monad_env eff_binders  in
                  match uu____22612 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let for_free =
                        let uu____22651 =
                          let uu____22652 =
                            let uu____22661 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____22661  in
                          FStar_List.length uu____22652  in
                        uu____22651 = (Prims.parse_int "1")  in
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
                            (uu____22707,uu____22708,(FStar_Parser_AST.TyconAbbrev
                                                      (name,uu____22710,uu____22711,uu____22712),uu____22713)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____22746 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____22747 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____22759 = name_of_eff_decl decl  in
                             FStar_List.mem uu____22759 mandatory_members)
                          eff_decls
                         in
                      (match uu____22747 with
                       | (mandatory_members_decls,actions) ->
                           let uu____22776 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____22805  ->
                                     fun decl  ->
                                       match uu____22805 with
                                       | (env2,out) ->
                                           let uu____22825 =
                                             desugar_decl env2 decl  in
                                           (match uu____22825 with
                                            | (env3,ses) ->
                                                let uu____22838 =
                                                  let uu____22841 =
                                                    FStar_List.hd ses  in
                                                  uu____22841 :: out  in
                                                (env3, uu____22838)))
                                  (env1, []))
                              in
                           (match uu____22776 with
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
                                              (uu____22910,uu____22911,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____22914,
                                                 {
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.Construct
                                                     (uu____22915,(def,uu____22917)::
                                                      (cps_type,uu____22919)::[]);
                                                   FStar_Parser_AST.range =
                                                     uu____22920;
                                                   FStar_Parser_AST.level =
                                                     uu____22921;_}),doc1)::[])
                                              when Prims.op_Negation for_free
                                              ->
                                              let uu____22973 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____22973 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____23011 =
                                                     let uu____23012 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____23013 =
                                                       let uu____23014 =
                                                         desugar_term env3
                                                           def
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____23014
                                                        in
                                                     let uu____23021 =
                                                       let uu____23022 =
                                                         desugar_typ env3
                                                           cps_type
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____23022
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____23012;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____23013;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____23021
                                                     }  in
                                                   (uu____23011, doc1))
                                          | FStar_Parser_AST.Tycon
                                              (uu____23031,uu____23032,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____23035,defn),doc1)::[])
                                              when for_free ->
                                              let uu____23070 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____23070 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____23108 =
                                                     let uu____23109 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____23110 =
                                                       let uu____23111 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____23111
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____23109;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____23110;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____23108, doc1))
                                          | uu____23120 ->
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
                                    let uu____23152 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____23152
                                     in
                                  let uu____23153 =
                                    let uu____23154 =
                                      FStar_Syntax_DsEnv.fail_or env2
                                        (FStar_Syntax_DsEnv.try_lookup_definition
                                           env2) l
                                       in
                                    FStar_All.pipe_left
                                      (FStar_Syntax_Subst.close binders1)
                                      uu____23154
                                     in
                                  ([], uu____23153)  in
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
                                      let uu____23171 =
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      ([], uu____23171)  in
                                    let uu____23178 =
                                      let uu____23179 =
                                        let uu____23180 =
                                          let uu____23181 = lookup1 "repr"
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____23181
                                           in
                                        let uu____23190 = lookup1 "return"
                                           in
                                        let uu____23191 = lookup1 "bind"  in
                                        let uu____23192 =
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
                                            uu____23180;
                                          FStar_Syntax_Syntax.return_repr =
                                            uu____23190;
                                          FStar_Syntax_Syntax.bind_repr =
                                            uu____23191;
                                          FStar_Syntax_Syntax.actions =
                                            actions1;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            uu____23192
                                        }  in
                                      FStar_Syntax_Syntax.Sig_new_effect_for_free
                                        uu____23179
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____23178;
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
                                         (fun uu___263_23198  ->
                                            match uu___263_23198 with
                                            | FStar_Syntax_Syntax.Reifiable 
                                                -> true
                                            | FStar_Syntax_Syntax.Reflectable
                                                uu____23199 -> true
                                            | uu____23200 -> false)
                                         qualifiers
                                        in
                                     let un_ts =
                                       ([], FStar_Syntax_Syntax.tun)  in
                                     let uu____23214 =
                                       let uu____23215 =
                                         let uu____23216 =
                                           lookup1 "return_wp"  in
                                         let uu____23217 = lookup1 "bind_wp"
                                            in
                                         let uu____23218 =
                                           lookup1 "if_then_else"  in
                                         let uu____23219 = lookup1 "ite_wp"
                                            in
                                         let uu____23220 = lookup1 "stronger"
                                            in
                                         let uu____23221 = lookup1 "close_wp"
                                            in
                                         let uu____23222 = lookup1 "assert_p"
                                            in
                                         let uu____23223 = lookup1 "assume_p"
                                            in
                                         let uu____23224 = lookup1 "null_wp"
                                            in
                                         let uu____23225 = lookup1 "trivial"
                                            in
                                         let uu____23226 =
                                           if rr
                                           then
                                             let uu____23227 = lookup1 "repr"
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.snd
                                               uu____23227
                                           else FStar_Syntax_Syntax.tun  in
                                         let uu____23243 =
                                           if rr
                                           then lookup1 "return"
                                           else un_ts  in
                                         let uu____23245 =
                                           if rr
                                           then lookup1 "bind"
                                           else un_ts  in
                                         let uu____23247 =
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
                                             uu____23216;
                                           FStar_Syntax_Syntax.bind_wp =
                                             uu____23217;
                                           FStar_Syntax_Syntax.if_then_else =
                                             uu____23218;
                                           FStar_Syntax_Syntax.ite_wp =
                                             uu____23219;
                                           FStar_Syntax_Syntax.stronger =
                                             uu____23220;
                                           FStar_Syntax_Syntax.close_wp =
                                             uu____23221;
                                           FStar_Syntax_Syntax.assert_p =
                                             uu____23222;
                                           FStar_Syntax_Syntax.assume_p =
                                             uu____23223;
                                           FStar_Syntax_Syntax.null_wp =
                                             uu____23224;
                                           FStar_Syntax_Syntax.trivial =
                                             uu____23225;
                                           FStar_Syntax_Syntax.repr =
                                             uu____23226;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____23243;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____23245;
                                           FStar_Syntax_Syntax.actions =
                                             actions1;
                                           FStar_Syntax_Syntax.eff_attrs =
                                             uu____23247
                                         }  in
                                       FStar_Syntax_Syntax.Sig_new_effect
                                         uu____23215
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         uu____23214;
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
                                          fun uu____23273  ->
                                            match uu____23273 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____23287 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____23287
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
                let uu____23311 = desugar_binders env1 eff_binders  in
                match uu____23311 with
                | (env2,binders) ->
                    let uu____23348 =
                      let uu____23359 = head_and_args defn  in
                      match uu____23359 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____23396 ->
                                let uu____23397 =
                                  let uu____23402 =
                                    let uu____23403 =
                                      let uu____23404 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.strcat uu____23404 " not found"
                                       in
                                    Prims.strcat "Effect " uu____23403  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____23402)
                                   in
                                FStar_Errors.raise_error uu____23397
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____23406 =
                            match FStar_List.rev args with
                            | (last_arg,uu____23436)::args_rev ->
                                let uu____23448 =
                                  let uu____23449 = unparen last_arg  in
                                  uu____23449.FStar_Parser_AST.tm  in
                                (match uu____23448 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____23477 -> ([], args))
                            | uu____23486 -> ([], args)  in
                          (match uu____23406 with
                           | (cattributes,args1) ->
                               let uu____23529 = desugar_args env2 args1  in
                               let uu____23530 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____23529, uu____23530))
                       in
                    (match uu____23348 with
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
                          (let uu____23566 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____23566 with
                           | (ed_binders,uu____23580,ed_binders_opening) ->
                               let sub1 uu____23593 =
                                 match uu____23593 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____23607 =
                                         FStar_Syntax_Subst.shift_subst
                                           (FStar_List.length us)
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____23607 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____23611 =
                                       let uu____23612 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____23612)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____23611
                                  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____23621 =
                                   let uu____23622 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____23622
                                    in
                                 let uu____23637 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____23638 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____23639 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____23640 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____23641 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____23642 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____23643 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____23644 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____23645 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____23646 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____23647 =
                                   let uu____23648 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____23648
                                    in
                                 let uu____23663 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____23664 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____23665 =
                                   FStar_List.map
                                     (fun action  ->
                                        let uu____23673 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____23674 =
                                          let uu____23675 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____23675
                                           in
                                        let uu____23690 =
                                          let uu____23691 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____23691
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____23673;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____23674;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____23690
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
                                     uu____23621;
                                   FStar_Syntax_Syntax.ret_wp = uu____23637;
                                   FStar_Syntax_Syntax.bind_wp = uu____23638;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____23639;
                                   FStar_Syntax_Syntax.ite_wp = uu____23640;
                                   FStar_Syntax_Syntax.stronger = uu____23641;
                                   FStar_Syntax_Syntax.close_wp = uu____23642;
                                   FStar_Syntax_Syntax.assert_p = uu____23643;
                                   FStar_Syntax_Syntax.assume_p = uu____23644;
                                   FStar_Syntax_Syntax.null_wp = uu____23645;
                                   FStar_Syntax_Syntax.trivial = uu____23646;
                                   FStar_Syntax_Syntax.repr = uu____23647;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____23663;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____23664;
                                   FStar_Syntax_Syntax.actions = uu____23665;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____23708 =
                                     let uu____23709 =
                                       let uu____23718 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____23718
                                        in
                                     FStar_List.length uu____23709  in
                                   uu____23708 = (Prims.parse_int "1")  in
                                 let uu____23749 =
                                   let uu____23752 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____23752 quals  in
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
                                   FStar_Syntax_Syntax.sigquals = uu____23749;
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
                                             let uu____23774 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____23774
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____23776 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____23776
                                 then
                                   let reflect_lid =
                                     let uu____23780 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____23780
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
    let uu____23790 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____23790 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.strcat "  " (Prims.strcat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____23841 ->
              let uu____23842 =
                let uu____23843 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____23843
                 in
              Prims.strcat "\n  " uu____23842
          | uu____23844 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____23857  ->
               match uu____23857 with
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
          let uu____23875 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____23875
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____23877 =
          let uu____23888 = FStar_Syntax_Syntax.as_arg arg  in [uu____23888]
           in
        FStar_Syntax_Util.mk_app fv uu____23877

and (desugar_decl_aux :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      let uu____23919 = desugar_decl_noattrs env d  in
      match uu____23919 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____23937 = mk_comment_attr d  in uu____23937 :: attrs1  in
          let uu____23938 =
            FStar_List.mapi
              (fun i  ->
                 fun sigelt  ->
                   if i = (Prims.parse_int "0")
                   then
                     let uu___298_23944 = sigelt  in
                     {
                       FStar_Syntax_Syntax.sigel =
                         (uu___298_23944.FStar_Syntax_Syntax.sigel);
                       FStar_Syntax_Syntax.sigrng =
                         (uu___298_23944.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___298_23944.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___298_23944.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs = attrs2
                     }
                   else
                     (let uu___299_23946 = sigelt  in
                      let uu____23947 =
                        FStar_List.filter
                          (fun at1  ->
                             let uu____23953 = get_fail_attr false at1  in
                             FStar_Option.isNone uu____23953) attrs2
                         in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___299_23946.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___299_23946.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___299_23946.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___299_23946.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs = uu____23947
                      })) sigelts
             in
          (env1, uu____23938)

and (desugar_decl :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      let uu____23974 = desugar_decl_aux env d  in
      match uu____23974 with
      | (env1,ses) ->
          let uu____23985 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____23985)

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
      | FStar_Parser_AST.Fsdoc uu____24013 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Friend lid ->
          let uu____24018 = FStar_Syntax_DsEnv.iface env  in
          if uu____24018
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____24028 =
               let uu____24029 =
                 let uu____24030 = FStar_Syntax_DsEnv.dep_graph env  in
                 let uu____24031 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Parser_Dep.module_has_interface uu____24030
                   uu____24031
                  in
               Prims.op_Negation uu____24029  in
             if uu____24028
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____24041 =
                  let uu____24042 =
                    let uu____24043 = FStar_Syntax_DsEnv.dep_graph env  in
                    FStar_Parser_Dep.module_has_interface uu____24043 lid  in
                  Prims.op_Negation uu____24042  in
                if uu____24041
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____24053 =
                     let uu____24054 =
                       let uu____24055 = FStar_Syntax_DsEnv.dep_graph env  in
                       FStar_Parser_Dep.deps_has_implementation uu____24055
                         lid
                        in
                     Prims.op_Negation uu____24054  in
                   if uu____24053
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____24069 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____24069, [])
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
              (fun uu____24114  ->
                 match uu____24114 with | (x,uu____24122) -> x) tcs
             in
          let uu____24127 =
            let uu____24132 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____24132 tcs1  in
          (match uu____24127 with
           | (env1,ses) ->
               let mkclass lid =
                 let uu____24149 =
                   let uu____24150 =
                     let uu____24157 =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun
                        in
                     FStar_Syntax_Syntax.mk_binder uu____24157  in
                   [uu____24150]  in
                 let uu____24170 =
                   let uu____24173 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____24176 =
                     let uu____24187 =
                       let uu____24196 =
                         let uu____24197 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____24197  in
                       FStar_Syntax_Syntax.as_arg uu____24196  in
                     [uu____24187]  in
                   FStar_Syntax_Util.mk_app uu____24173 uu____24176  in
                 FStar_Syntax_Util.abs uu____24149 uu____24170
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____24236,id1))::uu____24238 ->
                       FStar_Pervasives_Native.Some id1
                   | uu____24241::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____24245 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____24245 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id1 ->
                     let id2 = FStar_Syntax_Util.unmangle_field_name id1  in
                     let uu____24252 = FStar_Syntax_DsEnv.qualify env1 id2
                        in
                     [uu____24252]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____24273) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____24283,uu____24284,uu____24285,uu____24286,uu____24287)
                     ->
                     let uu____24296 =
                       let uu____24297 =
                         let uu____24298 =
                           let uu____24305 = mkclass lid  in
                           (meths, uu____24305)  in
                         FStar_Syntax_Syntax.Sig_splice uu____24298  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____24297;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = []
                       }  in
                     [uu____24296]
                 | uu____24308 -> []  in
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
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____24338;
                    FStar_Parser_AST.prange = uu____24339;_},uu____24340)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____24349;
                    FStar_Parser_AST.prange = uu____24350;_},uu____24351)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____24366;
                         FStar_Parser_AST.prange = uu____24367;_},uu____24368);
                    FStar_Parser_AST.prange = uu____24369;_},uu____24370)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____24391;
                         FStar_Parser_AST.prange = uu____24392;_},uu____24393);
                    FStar_Parser_AST.prange = uu____24394;_},uu____24395)::[]
                   -> false
               | (p,uu____24423)::[] ->
                   let uu____24432 = is_app_pattern p  in
                   Prims.op_Negation uu____24432
               | uu____24433 -> false)
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
            let uu____24506 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____24506 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____24518 =
                     let uu____24519 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____24519.FStar_Syntax_Syntax.n  in
                   match uu____24518 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____24529) ->
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
                         | uu____24562::uu____24563 ->
                             FStar_List.map
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____24566 ->
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.collect
                                  (fun uu___264_24581  ->
                                     match uu___264_24581 with
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inl uu____24584;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____24585;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____24586;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____24587;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____24588;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____24589;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____24590;_}
                                         -> []
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____24602;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____24603;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____24604;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____24605;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____24606;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____24607;_}
                                         ->
                                         FStar_Syntax_DsEnv.lookup_letbinding_quals
                                           env
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                          in
                       let quals2 =
                         let uu____24621 =
                           FStar_All.pipe_right lets1
                             (FStar_Util.for_some
                                (fun uu____24652  ->
                                   match uu____24652 with
                                   | (uu____24665,(uu____24666,t)) ->
                                       t.FStar_Parser_AST.level =
                                         FStar_Parser_AST.Formula))
                            in
                         if uu____24621
                         then FStar_Syntax_Syntax.Logic :: quals1
                         else quals1  in
                       let lbs1 =
                         let uu____24684 =
                           FStar_All.pipe_right quals2
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract)
                            in
                         if uu____24684
                         then
                           let uu____24687 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu___300_24701 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___301_24703 = fv  in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___301_24703.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___301_24703.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___300_24701.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___300_24701.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___300_24701.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___300_24701.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___300_24701.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___300_24701.FStar_Syntax_Syntax.lbpos)
                                     }))
                              in
                           ((FStar_Pervasives_Native.fst lbs), uu____24687)
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
                   | uu____24730 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____24736 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____24755 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____24736 with
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
                       let uu___302_24791 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___302_24791.FStar_Parser_AST.prange)
                       }
                   | uu____24798 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___303_24805 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___303_24805.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___303_24805.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___303_24805.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____24841 id1 =
                   match uu____24841 with
                   | (env1,ses) ->
                       let main =
                         let uu____24862 =
                           let uu____24863 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____24863  in
                         FStar_Parser_AST.mk_term uu____24862
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
                       let uu____24913 = desugar_decl env1 id_decl  in
                       (match uu____24913 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____24931 = gather_pattern_bound_vars true pat  in
                   FStar_All.pipe_right uu____24931 FStar_Util.set_elements
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
            let uu____24954 = close_fun env t  in
            desugar_term env uu____24954  in
          let quals1 =
            let uu____24958 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____24958
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let se =
            let uu____24964 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____24964;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in
          let env2 =
            FStar_Syntax_DsEnv.push_doc env1 lid d.FStar_Parser_AST.doc  in
          (env2, [se])
      | FStar_Parser_AST.Exception (id1,FStar_Pervasives_Native.None ) ->
          let uu____24972 =
            FStar_Syntax_DsEnv.fail_or env
              (FStar_Syntax_DsEnv.try_lookup_lid env)
              FStar_Parser_Const.exn_lid
             in
          (match uu____24972 with
           | (t,uu____24986) ->
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
            let uu____25016 =
              let uu____25025 = FStar_Syntax_Syntax.null_binder t  in
              [uu____25025]  in
            let uu____25044 =
              let uu____25047 =
                let uu____25048 =
                  FStar_Syntax_DsEnv.fail_or env
                    (FStar_Syntax_DsEnv.try_lookup_lid env)
                    FStar_Parser_Const.exn_lid
                   in
                FStar_Pervasives_Native.fst uu____25048  in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____25047
               in
            FStar_Syntax_Util.arrow uu____25016 uu____25044  in
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
            let uu____25109 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____25109 with
            | FStar_Pervasives_Native.None  ->
                let uu____25112 =
                  let uu____25117 =
                    let uu____25118 =
                      let uu____25119 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.strcat uu____25119 " not found"  in
                    Prims.strcat "Effect name " uu____25118  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____25117)  in
                FStar_Errors.raise_error uu____25112
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____25123 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____25141 =
                  let uu____25144 =
                    let uu____25145 = desugar_term env t  in
                    ([], uu____25145)  in
                  FStar_Pervasives_Native.Some uu____25144  in
                (uu____25141, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____25158 =
                  let uu____25161 =
                    let uu____25162 = desugar_term env wp  in
                    ([], uu____25162)  in
                  FStar_Pervasives_Native.Some uu____25161  in
                let uu____25169 =
                  let uu____25172 =
                    let uu____25173 = desugar_term env t  in
                    ([], uu____25173)  in
                  FStar_Pervasives_Native.Some uu____25172  in
                (uu____25158, uu____25169)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____25185 =
                  let uu____25188 =
                    let uu____25189 = desugar_term env t  in
                    ([], uu____25189)  in
                  FStar_Pervasives_Native.Some uu____25188  in
                (FStar_Pervasives_Native.None, uu____25185)
             in
          (match uu____25123 with
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
            let uu____25223 =
              let uu____25224 =
                let uu____25231 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____25231, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____25224  in
            {
              FStar_Syntax_Syntax.sigel = uu____25223;
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
      let uu____25257 =
        FStar_List.fold_left
          (fun uu____25277  ->
             fun d  ->
               match uu____25277 with
               | (env1,sigelts) ->
                   let uu____25297 = desugar_decl env1 d  in
                   (match uu____25297 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____25257 with
      | (env1,sigelts) ->
          let rec forward acc uu___266_25342 =
            match uu___266_25342 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____25356,FStar_Syntax_Syntax.Sig_let uu____25357) ->
                     let uu____25370 =
                       let uu____25373 =
                         let uu___304_25374 = se2  in
                         let uu____25375 =
                           let uu____25378 =
                             FStar_List.filter
                               (fun uu___265_25392  ->
                                  match uu___265_25392 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____25396;
                                           FStar_Syntax_Syntax.vars =
                                             uu____25397;_},uu____25398);
                                      FStar_Syntax_Syntax.pos = uu____25399;
                                      FStar_Syntax_Syntax.vars = uu____25400;_}
                                      when
                                      let uu____25427 =
                                        let uu____25428 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____25428
                                         in
                                      uu____25427 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____25429 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____25378
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___304_25374.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___304_25374.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___304_25374.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___304_25374.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____25375
                         }  in
                       uu____25373 :: se1 :: acc  in
                     forward uu____25370 sigelts1
                 | uu____25434 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____25442 = forward [] sigelts  in (env1, uu____25442)
  
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
          | (FStar_Pervasives_Native.None ,uu____25503) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____25507;
               FStar_Syntax_Syntax.exports = uu____25508;
               FStar_Syntax_Syntax.is_interface = uu____25509;_},FStar_Parser_AST.Module
             (current_lid,uu____25511)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____25519) ->
              let uu____25522 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____25522
           in
        let uu____25527 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____25563 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____25563, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____25580 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____25580, mname, decls, false)
           in
        match uu____25527 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____25610 = desugar_decls env2 decls  in
            (match uu____25610 with
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
          let uu____25672 =
            (FStar_Options.interactive ()) &&
              (let uu____25674 =
                 let uu____25675 =
                   let uu____25676 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____25676  in
                 FStar_Util.get_file_extension uu____25675  in
               FStar_List.mem uu____25674 ["fsti"; "fsi"])
             in
          if uu____25672 then as_interface m else m  in
        let uu____25680 = desugar_modul_common curmod env m1  in
        match uu____25680 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____25698 = FStar_Syntax_DsEnv.pop ()  in
              (uu____25698, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul ->
      (env_t,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun m  ->
      let uu____25718 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____25718 with
      | (env1,modul,pop_when_done) ->
          let uu____25732 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____25732 with
           | (env2,modul1) ->
               ((let uu____25744 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____25744
                 then
                   let uu____25745 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____25745
                 else ());
                (let uu____25747 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____25747, modul1))))
  
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
        (fun uu____25794  ->
           let uu____25795 = desugar_modul env modul  in
           match uu____25795 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____25836  ->
           let uu____25837 = desugar_decls env decls  in
           match uu____25837 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____25891  ->
             let uu____25892 = desugar_partial_modul modul env a_modul  in
             match uu____25892 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____25990 ->
                  let t =
                    let uu____26000 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____26000  in
                  let uu____26013 =
                    let uu____26014 = FStar_Syntax_Subst.compress t  in
                    uu____26014.FStar_Syntax_Syntax.n  in
                  (match uu____26013 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____26026,uu____26027)
                       -> bs1
                   | uu____26052 -> failwith "Impossible")
               in
            let uu____26061 =
              let uu____26068 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____26068
                FStar_Syntax_Syntax.t_unit
               in
            match uu____26061 with
            | (binders,uu____26070,binders_opening) ->
                let erase_term t =
                  let uu____26078 =
                    let uu____26079 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____26079  in
                  FStar_Syntax_Subst.close binders uu____26078  in
                let erase_tscheme uu____26097 =
                  match uu____26097 with
                  | (us,t) ->
                      let t1 =
                        let uu____26117 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____26117 t  in
                      let uu____26120 =
                        let uu____26121 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____26121  in
                      ([], uu____26120)
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
                    | uu____26144 ->
                        let bs =
                          let uu____26154 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____26154  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____26194 =
                          let uu____26195 =
                            let uu____26198 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____26198  in
                          uu____26195.FStar_Syntax_Syntax.n  in
                        (match uu____26194 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____26200,uu____26201) -> bs1
                         | uu____26226 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____26233 =
                      let uu____26234 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____26234  in
                    FStar_Syntax_Subst.close binders uu____26233  in
                  let uu___305_26235 = action  in
                  let uu____26236 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____26237 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___305_26235.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___305_26235.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____26236;
                    FStar_Syntax_Syntax.action_typ = uu____26237
                  }  in
                let uu___306_26238 = ed  in
                let uu____26239 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____26240 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____26241 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____26242 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____26243 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____26244 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____26245 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____26246 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____26247 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____26248 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____26249 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____26250 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____26251 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____26252 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____26253 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____26254 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___306_26238.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___306_26238.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____26239;
                  FStar_Syntax_Syntax.signature = uu____26240;
                  FStar_Syntax_Syntax.ret_wp = uu____26241;
                  FStar_Syntax_Syntax.bind_wp = uu____26242;
                  FStar_Syntax_Syntax.if_then_else = uu____26243;
                  FStar_Syntax_Syntax.ite_wp = uu____26244;
                  FStar_Syntax_Syntax.stronger = uu____26245;
                  FStar_Syntax_Syntax.close_wp = uu____26246;
                  FStar_Syntax_Syntax.assert_p = uu____26247;
                  FStar_Syntax_Syntax.assume_p = uu____26248;
                  FStar_Syntax_Syntax.null_wp = uu____26249;
                  FStar_Syntax_Syntax.trivial = uu____26250;
                  FStar_Syntax_Syntax.repr = uu____26251;
                  FStar_Syntax_Syntax.return_repr = uu____26252;
                  FStar_Syntax_Syntax.bind_repr = uu____26253;
                  FStar_Syntax_Syntax.actions = uu____26254;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___306_26238.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___307_26270 = se  in
                  let uu____26271 =
                    let uu____26272 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____26272  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____26271;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___307_26270.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___307_26270.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___307_26270.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___307_26270.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___308_26276 = se  in
                  let uu____26277 =
                    let uu____26278 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____26278
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____26277;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___308_26276.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___308_26276.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___308_26276.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___308_26276.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____26280 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____26281 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____26281 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____26293 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____26293
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____26295 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____26295)
  