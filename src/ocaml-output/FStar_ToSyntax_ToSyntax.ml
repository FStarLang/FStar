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
        | FStar_Parser_AST.PatName uu____1669 -> acc
        | FStar_Parser_AST.PatTvar uu____1670 -> acc
        | FStar_Parser_AST.PatOp uu____1677 -> acc
        | FStar_Parser_AST.PatConst uu____1678 ->
            if fail_on_patconst
            then
              FStar_Errors.raise_error
                (FStar_Errors.Error_CannotRedefineConst,
                  "Constants cannot be redefined") p.FStar_Parser_AST.prange
            else acc
        | FStar_Parser_AST.PatApp (phead,pats) ->
            gather_pattern_bound_vars_from_list (phead :: pats)
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
  fun uu___242_1874  ->
    match uu___242_1874 with
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
        let uu___268_2483 = s  in
        let uu____2484 =
          let uu____2485 =
            let uu____2494 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____2512,bs,t,lids1,lids2) ->
                          let uu___269_2525 = se  in
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
                              (uu___269_2525.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___269_2525.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___269_2525.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___269_2525.FStar_Syntax_Syntax.sigattrs)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____2560,t,tlid,n1,lids1) ->
                          let uu___270_2569 = se  in
                          let uu____2570 =
                            let uu____2571 =
                              let uu____2586 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____2586, tlid, n1, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____2571  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____2570;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___270_2569.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___270_2569.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___270_2569.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___270_2569.FStar_Syntax_Syntax.sigattrs)
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
            (uu___268_2483.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___268_2483.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___268_2483.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___268_2483.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2595,t) ->
        let uvs =
          let uu____2598 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____2598 FStar_Util.set_elements  in
        let uu___271_2603 = s  in
        let uu____2604 =
          let uu____2605 =
            let uu____2612 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____2612)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____2605  in
        {
          FStar_Syntax_Syntax.sigel = uu____2604;
          FStar_Syntax_Syntax.sigrng =
            (uu___271_2603.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___271_2603.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___271_2603.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___271_2603.FStar_Syntax_Syntax.sigattrs)
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
        let uu___272_2908 = s  in
        let uu____2909 =
          let uu____2910 =
            let uu____2917 =
              let uu____2918 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___273_2930 = lb  in
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
                            (uu___273_2930.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____2931;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___273_2930.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____2934;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___273_2930.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___273_2930.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____2918)  in
            (uu____2917, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____2910  in
        {
          FStar_Syntax_Syntax.sigel = uu____2909;
          FStar_Syntax_Syntax.sigrng =
            (uu___272_2908.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___272_2908.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___272_2908.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___272_2908.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____2942,fml) ->
        let uvs =
          let uu____2945 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____2945 FStar_Util.set_elements  in
        let uu___274_2950 = s  in
        let uu____2951 =
          let uu____2952 =
            let uu____2959 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____2959)  in
          FStar_Syntax_Syntax.Sig_assume uu____2952  in
        {
          FStar_Syntax_Syntax.sigel = uu____2951;
          FStar_Syntax_Syntax.sigrng =
            (uu___274_2950.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___274_2950.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___274_2950.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___274_2950.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____2961,bs,c,flags1) ->
        let uvs =
          let uu____2970 =
            let uu____2973 = bs_univnames bs  in
            let uu____2976 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____2973 uu____2976  in
          FStar_All.pipe_right uu____2970 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___275_2984 = s  in
        let uu____2985 =
          let uu____2986 =
            let uu____2999 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____3000 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____2999, uu____3000, flags1)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____2986  in
        {
          FStar_Syntax_Syntax.sigel = uu____2985;
          FStar_Syntax_Syntax.sigrng =
            (uu___275_2984.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___275_2984.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___275_2984.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___275_2984.FStar_Syntax_Syntax.sigattrs)
        }
    | uu____3003 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___243_3008  ->
    match uu___243_3008 with
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
                  (fun uu___244_3221  ->
                     match uu___244_3221 with
                     | FStar_Util.Inr uu____3226 -> true
                     | uu____3227 -> false) univargs
              then
                let uu____3232 =
                  let uu____3233 =
                    FStar_List.map
                      (fun uu___245_3242  ->
                         match uu___245_3242 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____3233  in
                FStar_Util.Inr uu____3232
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___246_3259  ->
                        match uu___246_3259 with
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
      Prims.bool ->
        (env_t,bnd,annotated_pat Prims.list) FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun p  ->
      fun is_mut  ->
        let check_linear_pattern_variables pats r =
          let rec pat_vars p1 =
            match p1.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_dot_term uu____3855 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_wild uu____3862 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_constant uu____3863 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_var x ->
                FStar_Util.set_add x FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_cons (uu____3865,pats1) ->
                let aux out uu____3903 =
                  match uu____3903 with
                  | (p2,uu____3915) ->
                      let intersection =
                        let uu____3923 = pat_vars p2  in
                        FStar_Util.set_intersect uu____3923 out  in
                      let uu____3926 = FStar_Util.set_is_empty intersection
                         in
                      if uu____3926
                      then
                        let uu____3929 = pat_vars p2  in
                        FStar_Util.set_union out uu____3929
                      else
                        (let duplicate_bv =
                           let uu____3934 =
                             FStar_Util.set_elements intersection  in
                           FStar_List.hd uu____3934  in
                         let uu____3937 =
                           let uu____3942 =
                             FStar_Util.format1
                               "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                               (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                              in
                           (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                             uu____3942)
                            in
                         FStar_Errors.raise_error uu____3937 r)
                   in
                FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
             in
          match pats with
          | [] -> ()
          | p1::[] ->
              let uu____3962 = pat_vars p1  in
              FStar_All.pipe_right uu____3962 (fun a1  -> ())
          | p1::ps ->
              let pvars = pat_vars p1  in
              let aux p2 =
                let uu____3990 =
                  let uu____3991 = pat_vars p2  in
                  FStar_Util.set_eq pvars uu____3991  in
                if uu____3990
                then ()
                else
                  (let nonlinear_vars =
                     let uu____3998 = pat_vars p2  in
                     FStar_Util.set_symmetric_difference pvars uu____3998  in
                   let first_nonlinear_var =
                     let uu____4002 = FStar_Util.set_elements nonlinear_vars
                        in
                     FStar_List.hd uu____4002  in
                   let uu____4005 =
                     let uu____4010 =
                       FStar_Util.format1
                         "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                         (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                        in
                     (FStar_Errors.Fatal_IncoherentPatterns, uu____4010)  in
                   FStar_Errors.raise_error uu____4005 r)
                 in
              FStar_List.iter aux ps
           in
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false ,uu____4014) -> ()
         | (true ,FStar_Parser_AST.PatVar uu____4015) -> ()
         | (true ,uu____4022) ->
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_LetMutableForVariablesOnly,
                 "let-mutable is for variables only")
               p.FStar_Parser_AST.prange);
        (let resolvex l e x =
           let uu____4045 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText))
              in
           match uu____4045 with
           | FStar_Pervasives_Native.Some y -> (l, e, y)
           | uu____4061 ->
               let uu____4064 =
                 if is_mut
                 then FStar_Syntax_DsEnv.push_bv_mutable e x
                 else FStar_Syntax_DsEnv.push_bv e x  in
               (match uu____4064 with | (e1,x1) -> ((x1 :: l), e1, x1))
            in
         let rec aux' top loc env1 p1 =
           let pos q =
             FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange  in
           let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
           let orig = p1  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr uu____4214 -> failwith "impossible"
           | FStar_Parser_AST.PatOp op ->
               let uu____4236 =
                 let uu____4237 =
                   let uu____4238 =
                     let uu____4245 =
                       let uu____4246 =
                         let uu____4251 =
                           FStar_Parser_AST.compile_op (Prims.parse_int "0")
                             op.FStar_Ident.idText op.FStar_Ident.idRange
                            in
                         (uu____4251, (op.FStar_Ident.idRange))  in
                       FStar_Ident.mk_ident uu____4246  in
                     (uu____4245, FStar_Pervasives_Native.None)  in
                   FStar_Parser_AST.PatVar uu____4238  in
                 {
                   FStar_Parser_AST.pat = uu____4237;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 }  in
               aux loc env1 uu____4236
           | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
               ((match tacopt with
                 | FStar_Pervasives_Native.None  -> ()
                 | FStar_Pervasives_Native.Some uu____4268 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                         "Type ascriptions within patterns cannot be associated with a tactic")
                       orig.FStar_Parser_AST.prange);
                (let uu____4269 = aux loc env1 p2  in
                 match uu____4269 with
                 | (loc1,env',binder,p3,annots,imp) ->
                     let annot_pat_var p4 t1 =
                       match p4.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let uu___276_4354 = p4  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var
                                  (let uu___277_4359 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___277_4359.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___277_4359.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }));
                             FStar_Syntax_Syntax.p =
                               (uu___276_4354.FStar_Syntax_Syntax.p)
                           }
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let uu___278_4361 = p4  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild
                                  (let uu___279_4366 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___279_4366.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___279_4366.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }));
                             FStar_Syntax_Syntax.p =
                               (uu___278_4361.FStar_Syntax_Syntax.p)
                           }
                       | uu____4367 when top -> p4
                       | uu____4368 ->
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                               "Type ascriptions within patterns are only allowed on variables")
                             orig.FStar_Parser_AST.prange
                        in
                     let uu____4371 =
                       match binder with
                       | LetBinder uu____4392 -> failwith "impossible"
                       | LocalBinder (x,aq) ->
                           let t1 =
                             let uu____4416 = close_fun env1 t  in
                             desugar_term env1 uu____4416  in
                           let x1 =
                             let uu___280_4418 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___280_4418.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___280_4418.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }  in
                           ([(x1, t1)], (LocalBinder (x1, aq)))
                        in
                     (match uu____4371 with
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
               let uu____4483 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
               (loc, env1, (LocalBinder (x, aq1)), uu____4483, [], imp)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____4496 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____4496, [], false)
           | FStar_Parser_AST.PatTvar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual env1 aq  in
               let uu____4517 = resolvex loc env1 x  in
               (match uu____4517 with
                | (loc1,env2,xbv) ->
                    let uu____4545 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____4545, [],
                      imp))
           | FStar_Parser_AST.PatVar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual env1 aq  in
               let uu____4566 = resolvex loc env1 x  in
               (match uu____4566 with
                | (loc1,env2,xbv) ->
                    let uu____4594 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____4594, [],
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
               let uu____4608 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, []))
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____4608, [], false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____4634;_},args)
               ->
               let uu____4640 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____4699  ->
                        match uu____4699 with
                        | (loc1,env2,annots,args1) ->
                            let uu____4776 = aux loc1 env2 arg  in
                            (match uu____4776 with
                             | (loc2,env3,uu____4821,arg1,ans,imp) ->
                                 (loc2, env3, (FStar_List.append ans annots),
                                   ((arg1, imp) :: args1)))) args
                   (loc, env1, [], [])
                  in
               (match uu____4640 with
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
                    let uu____4943 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                       in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)),
                      uu____4943, annots, false))
           | FStar_Parser_AST.PatApp uu____4958 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                 p1.FStar_Parser_AST.prange
           | FStar_Parser_AST.PatList pats ->
               let uu____4986 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____5037  ->
                        match uu____5037 with
                        | (loc1,env2,annots,pats1) ->
                            let uu____5098 = aux loc1 env2 pat  in
                            (match uu____5098 with
                             | (loc2,env3,uu____5139,pat1,ans,uu____5142) ->
                                 (loc2, env3, (FStar_List.append ans annots),
                                   (pat1 :: pats1)))) pats
                   (loc, env1, [], [])
                  in
               (match uu____4986 with
                | (loc1,env2,annots,pats1) ->
                    let pat =
                      let uu____5236 =
                        let uu____5239 =
                          let uu____5246 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange
                             in
                          pos_r uu____5246  in
                        let uu____5247 =
                          let uu____5248 =
                            let uu____5261 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Parser_Const.nil_lid
                                FStar_Syntax_Syntax.delta_constant
                                (FStar_Pervasives_Native.Some
                                   FStar_Syntax_Syntax.Data_ctor)
                               in
                            (uu____5261, [])  in
                          FStar_Syntax_Syntax.Pat_cons uu____5248  in
                        FStar_All.pipe_left uu____5239 uu____5247  in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p
                                in
                             let uu____5293 =
                               let uu____5294 =
                                 let uu____5307 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.cons_lid
                                     FStar_Syntax_Syntax.delta_constant
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Data_ctor)
                                    in
                                 (uu____5307, [(hd1, false); (tl1, false)])
                                  in
                               FStar_Syntax_Syntax.Pat_cons uu____5294  in
                             FStar_All.pipe_left (pos_r r) uu____5293) pats1
                        uu____5236
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
               let uu____5353 =
                 FStar_List.fold_left
                   (fun uu____5411  ->
                      fun p2  ->
                        match uu____5411 with
                        | (loc1,env2,annots,pats) ->
                            let uu____5489 = aux loc1 env2 p2  in
                            (match uu____5489 with
                             | (loc2,env3,uu____5534,pat,ans,uu____5537) ->
                                 (loc2, env3, (FStar_List.append ans annots),
                                   ((pat, false) :: pats))))
                   (loc, env1, [], []) args
                  in
               (match uu____5353 with
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
                    let uu____5683 =
                      FStar_Syntax_DsEnv.fail_or env2
                        (FStar_Syntax_DsEnv.try_lookup_lid env2) l
                       in
                    (match uu____5683 with
                     | (constr,uu____5711) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____5714 -> failwith "impossible"  in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (FStar_Pervasives_Native.Some
                                (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun
                            in
                         let uu____5716 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                            in
                         (loc1, env2,
                           (LocalBinder (x, FStar_Pervasives_Native.None)),
                           uu____5716, annots, false)))
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
                      (fun uu____5791  ->
                         match uu____5791 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2)))
                  in
               let args =
                 FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                   (FStar_List.map
                      (fun uu____5821  ->
                         match uu____5821 with
                         | (f,uu____5827) ->
                             let uu____5828 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____5854  ->
                                       match uu____5854 with
                                       | (g,uu____5860) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText))
                                in
                             (match uu____5828 with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Parser_AST.mk_pattern
                                    (FStar_Parser_AST.PatWild
                                       FStar_Pervasives_Native.None)
                                    p1.FStar_Parser_AST.prange
                              | FStar_Pervasives_Native.Some (uu____5865,p2)
                                  -> p2)))
                  in
               let app =
                 let uu____5872 =
                   let uu____5873 =
                     let uu____5880 =
                       let uu____5881 =
                         let uu____5882 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                                [record.FStar_Syntax_DsEnv.constrname])
                            in
                         FStar_Parser_AST.PatName uu____5882  in
                       FStar_Parser_AST.mk_pattern uu____5881
                         p1.FStar_Parser_AST.prange
                        in
                     (uu____5880, args)  in
                   FStar_Parser_AST.PatApp uu____5873  in
                 FStar_Parser_AST.mk_pattern uu____5872
                   p1.FStar_Parser_AST.prange
                  in
               let uu____5885 = aux loc env1 app  in
               (match uu____5885 with
                | (env2,e,b,p2,annots,uu____5929) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____5965 =
                            let uu____5966 =
                              let uu____5979 =
                                let uu___281_5980 = fv  in
                                let uu____5981 =
                                  let uu____5984 =
                                    let uu____5985 =
                                      let uu____5992 =
                                        FStar_All.pipe_right
                                          record.FStar_Syntax_DsEnv.fields
                                          (FStar_List.map
                                             FStar_Pervasives_Native.fst)
                                         in
                                      ((record.FStar_Syntax_DsEnv.typename),
                                        uu____5992)
                                       in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____5985
                                     in
                                  FStar_Pervasives_Native.Some uu____5984  in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___281_5980.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___281_5980.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____5981
                                }  in
                              (uu____5979, args1)  in
                            FStar_Syntax_Syntax.Pat_cons uu____5966  in
                          FStar_All.pipe_left pos uu____5965
                      | uu____6017 -> p2  in
                    (env2, e, b, p3, annots, false))
         
         and aux loc env1 p1 = aux' false loc env1 p1
          in
         let aux_maybe_or env1 p1 =
           let loc = []  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____6099 = aux' true loc env1 p2  in
               (match uu____6099 with
                | (loc1,env2,var,p3,ans,uu____6141) ->
                    let uu____6154 =
                      FStar_List.fold_left
                        (fun uu____6203  ->
                           fun p4  ->
                             match uu____6203 with
                             | (loc2,env3,ps1) ->
                                 let uu____6268 = aux' true loc2 env3 p4  in
                                 (match uu____6268 with
                                  | (loc3,env4,uu____6307,p5,ans1,uu____6310)
                                      -> (loc3, env4, ((p5, ans1) :: ps1))))
                        (loc1, env2, []) ps
                       in
                    (match uu____6154 with
                     | (loc2,env3,ps1) ->
                         let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                         (env3, var, pats)))
           | uu____6469 ->
               let uu____6470 = aux' true loc env1 p1  in
               (match uu____6470 with
                | (loc1,env2,vars,pat,ans,b) -> (env2, vars, [(pat, ans)]))
            in
         let uu____6563 = aux_maybe_or env p  in
         match uu____6563 with
         | (env1,b,pats) ->
             ((let uu____6618 =
                 FStar_List.map FStar_Pervasives_Native.fst pats  in
               check_linear_pattern_variables uu____6618
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
            let uu____6691 =
              let uu____6692 =
                let uu____6703 = FStar_Syntax_DsEnv.qualify env x  in
                (uu____6703, (ty, tacopt))  in
              LetBinder uu____6692  in
            (env, uu____6691, [])  in
          let op_to_ident x =
            let uu____6720 =
              let uu____6725 =
                FStar_Parser_AST.compile_op (Prims.parse_int "0")
                  x.FStar_Ident.idText x.FStar_Ident.idRange
                 in
              (uu____6725, (x.FStar_Ident.idRange))  in
            FStar_Ident.mk_ident uu____6720  in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____6743 = op_to_ident x  in
                mklet uu____6743 FStar_Syntax_Syntax.tun
                  FStar_Pervasives_Native.None
            | FStar_Parser_AST.PatVar (x,uu____6745) ->
                mklet x FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None
            | FStar_Parser_AST.PatAscribed
                ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                   FStar_Parser_AST.prange = uu____6751;_},(t,tacopt))
                ->
                let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)
                   in
                let uu____6767 = op_to_ident x  in
                let uu____6768 = desugar_term env t  in
                mklet uu____6767 uu____6768 tacopt1
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____6770);
                   FStar_Parser_AST.prange = uu____6771;_},(t,tacopt))
                ->
                let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)
                   in
                let uu____6791 = desugar_term env t  in
                mklet x uu____6791 tacopt1
            | uu____6792 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_UnexpectedPattern,
                    "Unexpected pattern at the top-level")
                  p.FStar_Parser_AST.prange
          else
            (let uu____6802 = desugar_data_pat env p is_mut  in
             match uu____6802 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1 with
                   | ({
                        FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                          uu____6831;
                        FStar_Syntax_Syntax.p = uu____6832;_},uu____6833)::[]
                       -> []
                   | ({
                        FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                          uu____6846;
                        FStar_Syntax_Syntax.p = uu____6847;_},uu____6848)::[]
                       -> []
                   | uu____6861 -> p1  in
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
  fun uu____6868  ->
    fun env  ->
      fun pat  ->
        let uu____6871 = desugar_data_pat env pat false  in
        match uu____6871 with | (env1,uu____6887,pat1) -> (env1, pat1)

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
      let uu____6906 = desugar_term_aq env e  in
      match uu____6906 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____6923 = desugar_typ_aq env e  in
      match uu____6923 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness,FStar_Const.width)
        FStar_Pervasives_Native.tuple2 ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____6933  ->
        fun range  ->
          match uu____6933 with
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
              ((let uu____6943 =
                  let uu____6944 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____6944  in
                if uu____6943
                then
                  let uu____6945 =
                    let uu____6950 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____6950)  in
                  FStar_Errors.log_issue range uu____6945
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
                  let uu____6955 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____6955 range  in
                let lid1 =
                  let uu____6959 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____6959 with
                  | FStar_Pervasives_Native.Some (intro_term,uu____6969) ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____6978 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____6978 range  in
                           let private_fv =
                             let uu____6980 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____6980 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___282_6981 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___282_6981.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___282_6981.FStar_Syntax_Syntax.vars)
                           }
                       | uu____6982 ->
                           failwith
                             (Prims.strcat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____6989 =
                        let uu____6994 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____6994)
                         in
                      FStar_Errors.raise_error uu____6989 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____7010 =
                  let uu____7017 =
                    let uu____7018 =
                      let uu____7035 =
                        let uu____7046 =
                          let uu____7055 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____7055)  in
                        [uu____7046]  in
                      (lid1, uu____7035)  in
                    FStar_Syntax_Syntax.Tm_app uu____7018  in
                  FStar_Syntax_Syntax.mk uu____7017  in
                uu____7010 FStar_Pervasives_Native.None range))

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
            let uu____7104 =
              let uu____7113 =
                (if resolve
                 then FStar_Syntax_DsEnv.try_lookup_lid_with_attributes
                 else
                   FStar_Syntax_DsEnv.try_lookup_lid_with_attributes_no_resolve)
                  env
                 in
              FStar_Syntax_DsEnv.fail_or env uu____7113 l  in
            match uu____7104 with
            | (tm,mut,attrs) ->
                let warn_if_deprecated attrs1 =
                  FStar_List.iter
                    (fun a  ->
                       match a.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_app
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____7168;
                              FStar_Syntax_Syntax.vars = uu____7169;_},args)
                           when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____7196 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____7196 " is deprecated"  in
                           let msg1 =
                             if
                               (FStar_List.length args) >
                                 (Prims.parse_int "0")
                             then
                               let uu____7206 =
                                 let uu____7207 =
                                   let uu____7210 = FStar_List.hd args  in
                                   FStar_Pervasives_Native.fst uu____7210  in
                                 uu____7207.FStar_Syntax_Syntax.n  in
                               match uu____7206 with
                               | FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_string (s,uu____7232))
                                   when
                                   Prims.op_Negation
                                     ((FStar_Util.trim_string s) = "")
                                   ->
                                   Prims.strcat msg
                                     (Prims.strcat ", use "
                                        (Prims.strcat s " instead"))
                               | uu____7233 -> msg
                             else msg  in
                           let uu____7235 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____7235
                             (FStar_Errors.Warning_DeprecatedDefinition,
                               msg1)
                       | FStar_Syntax_Syntax.Tm_fvar fv when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____7238 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____7238 " is deprecated"  in
                           let uu____7239 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____7239
                             (FStar_Errors.Warning_DeprecatedDefinition, msg)
                       | uu____7240 -> ()) attrs1
                   in
                (warn_if_deprecated attrs;
                 (let tm1 = setpos tm  in
                  if mut
                  then
                    let uu____7245 =
                      let uu____7246 =
                        let uu____7253 = mk_ref_read tm1  in
                        (uu____7253,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Mutable_rval))
                         in
                      FStar_Syntax_Syntax.Tm_meta uu____7246  in
                    FStar_All.pipe_left mk1 uu____7245
                  else tm1))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____7271 =
          let uu____7272 = unparen t  in uu____7272.FStar_Parser_AST.tm  in
        match uu____7271 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____7273; FStar_Ident.ident = uu____7274;
              FStar_Ident.nsstr = uu____7275; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____7278 ->
            let uu____7279 =
              let uu____7284 =
                let uu____7285 = FStar_Parser_AST.term_to_string t  in
                Prims.strcat "Unknown attribute " uu____7285  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____7284)  in
            FStar_Errors.raise_error uu____7279 t.FStar_Parser_AST.range
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
          let uu___283_7368 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___283_7368.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___283_7368.FStar_Syntax_Syntax.vars)
          }  in
        let uu____7371 =
          let uu____7372 = unparen top  in uu____7372.FStar_Parser_AST.tm  in
        match uu____7371 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____7377 ->
            let uu____7384 = desugar_formula env top  in (uu____7384, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____7391 = desugar_formula env t  in (uu____7391, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____7398 = desugar_formula env t  in (uu____7398, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____7422 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____7422, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____7424 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____7424, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____7432 =
                let uu____7433 =
                  let uu____7440 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____7440, args)  in
                FStar_Parser_AST.Op uu____7433  in
              FStar_Parser_AST.mk_term uu____7432 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____7443 =
              let uu____7444 =
                let uu____7445 =
                  let uu____7452 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____7452, [e])  in
                FStar_Parser_AST.Op uu____7445  in
              FStar_Parser_AST.mk_term uu____7444 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____7443
        | FStar_Parser_AST.Op (op_star,uu____7456::uu____7457::[]) when
            (let uu____7462 = FStar_Ident.text_of_id op_star  in
             uu____7462 = "*") &&
              (let uu____7464 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____7464 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____7479;_},t1::t2::[])
                  ->
                  let uu____7484 = flatten1 t1  in
                  FStar_List.append uu____7484 [t2]
              | uu____7487 -> [t]  in
            let uu____7488 =
              let uu____7513 =
                let uu____7536 =
                  let uu____7539 = unparen top  in flatten1 uu____7539  in
                FStar_All.pipe_right uu____7536
                  (FStar_List.map
                     (fun t  ->
                        let uu____7574 = desugar_typ_aq env t  in
                        match uu____7574 with
                        | (t',aq) ->
                            let uu____7585 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____7585, aq)))
                 in
              FStar_All.pipe_right uu____7513 FStar_List.unzip  in
            (match uu____7488 with
             | (targs,aqs) ->
                 let uu____7694 =
                   let uu____7699 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____7699
                    in
                 (match uu____7694 with
                  | (tup,uu____7717) ->
                      let uu____7718 =
                        mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                      (uu____7718, (join_aqs aqs))))
        | FStar_Parser_AST.Tvar a ->
            let uu____7732 =
              let uu____7733 =
                let uu____7736 =
                  FStar_Syntax_DsEnv.fail_or2
                    (FStar_Syntax_DsEnv.try_lookup_id env) a
                   in
                FStar_Pervasives_Native.fst uu____7736  in
              FStar_All.pipe_left setpos uu____7733  in
            (uu____7732, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____7748 =
              let uu____7753 =
                let uu____7754 =
                  let uu____7755 = FStar_Ident.text_of_id u  in
                  Prims.strcat uu____7755 " in non-universe context"  in
                Prims.strcat "Unexpected universe variable " uu____7754  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____7753)  in
            FStar_Errors.raise_error uu____7748 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____7766 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____7766 with
             | FStar_Pervasives_Native.None  ->
                 let uu____7773 =
                   let uu____7778 =
                     let uu____7779 = FStar_Ident.text_of_id s  in
                     Prims.strcat "Unexpected or unbound operator: "
                       uu____7779
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____7778)
                    in
                 FStar_Errors.raise_error uu____7773
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let uu____7789 =
                     let uu____7814 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____7876 = desugar_term_aq env t  in
                               match uu____7876 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____7814 FStar_List.unzip  in
                   (match uu____7789 with
                    | (args1,aqs) ->
                        let uu____8009 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____8009, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____8025)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____8040 =
              let uu___284_8041 = top  in
              let uu____8042 =
                let uu____8043 =
                  let uu____8050 =
                    let uu___285_8051 = top  in
                    let uu____8052 =
                      let uu____8053 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8053  in
                    {
                      FStar_Parser_AST.tm = uu____8052;
                      FStar_Parser_AST.range =
                        (uu___285_8051.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___285_8051.FStar_Parser_AST.level)
                    }  in
                  (uu____8050, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8043  in
              {
                FStar_Parser_AST.tm = uu____8042;
                FStar_Parser_AST.range =
                  (uu___284_8041.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___284_8041.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8040
        | FStar_Parser_AST.Construct (n1,(a,uu____8056)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____8072 =
                let uu___286_8073 = top  in
                let uu____8074 =
                  let uu____8075 =
                    let uu____8082 =
                      let uu___287_8083 = top  in
                      let uu____8084 =
                        let uu____8085 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____8085  in
                      {
                        FStar_Parser_AST.tm = uu____8084;
                        FStar_Parser_AST.range =
                          (uu___287_8083.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___287_8083.FStar_Parser_AST.level)
                      }  in
                    (uu____8082, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____8075  in
                {
                  FStar_Parser_AST.tm = uu____8074;
                  FStar_Parser_AST.range =
                    (uu___286_8073.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___286_8073.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____8072))
        | FStar_Parser_AST.Construct (n1,(a,uu____8088)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____8103 =
              let uu___288_8104 = top  in
              let uu____8105 =
                let uu____8106 =
                  let uu____8113 =
                    let uu___289_8114 = top  in
                    let uu____8115 =
                      let uu____8116 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8116  in
                    {
                      FStar_Parser_AST.tm = uu____8115;
                      FStar_Parser_AST.range =
                        (uu___289_8114.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___289_8114.FStar_Parser_AST.level)
                    }  in
                  (uu____8113, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8106  in
              {
                FStar_Parser_AST.tm = uu____8105;
                FStar_Parser_AST.range =
                  (uu___288_8104.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___288_8104.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8103
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8117; FStar_Ident.ident = uu____8118;
              FStar_Ident.nsstr = uu____8119; FStar_Ident.str = "Type0";_}
            ->
            let uu____8122 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____8122, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8123; FStar_Ident.ident = uu____8124;
              FStar_Ident.nsstr = uu____8125; FStar_Ident.str = "Type";_}
            ->
            let uu____8128 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____8128, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____8129; FStar_Ident.ident = uu____8130;
               FStar_Ident.nsstr = uu____8131; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____8149 =
              let uu____8150 =
                let uu____8151 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____8151  in
              mk1 uu____8150  in
            (uu____8149, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8152; FStar_Ident.ident = uu____8153;
              FStar_Ident.nsstr = uu____8154; FStar_Ident.str = "Effect";_}
            ->
            let uu____8157 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____8157, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8158; FStar_Ident.ident = uu____8159;
              FStar_Ident.nsstr = uu____8160; FStar_Ident.str = "True";_}
            ->
            let uu____8163 =
              let uu____8164 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8164
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8163, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8165; FStar_Ident.ident = uu____8166;
              FStar_Ident.nsstr = uu____8167; FStar_Ident.str = "False";_}
            ->
            let uu____8170 =
              let uu____8171 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8171
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8170, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____8174;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____8176 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____8176 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____8185 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_constant_at_level
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None
                     in
                  (uu____8185, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____8186 =
                    let uu____8187 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____8187 txt
                     in
                  failwith uu____8186))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8194 = desugar_name mk1 setpos env true l  in
              (uu____8194, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8197 = desugar_name mk1 setpos env true l  in
              (uu____8197, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____8208 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____8208 with
                | FStar_Pervasives_Native.Some uu____8217 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____8222 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____8222 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____8236 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____8253 =
                    let uu____8254 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____8254  in
                  (uu____8253, noaqs)
              | uu____8255 ->
                  let uu____8262 =
                    let uu____8267 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____8267)  in
                  FStar_Errors.raise_error uu____8262
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____8274 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____8274 with
              | FStar_Pervasives_Native.None  ->
                  let uu____8281 =
                    let uu____8286 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____8286)
                     in
                  FStar_Errors.raise_error uu____8281
                    top.FStar_Parser_AST.range
              | uu____8291 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____8295 = desugar_name mk1 setpos env true lid'  in
                  (uu____8295, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8311 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____8311 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____8330 ->
                       let uu____8337 =
                         FStar_Util.take
                           (fun uu____8361  ->
                              match uu____8361 with
                              | (uu____8366,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____8337 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____8411 =
                              let uu____8436 =
                                FStar_List.map
                                  (fun uu____8479  ->
                                     match uu____8479 with
                                     | (t,imp) ->
                                         let uu____8496 =
                                           desugar_term_aq env t  in
                                         (match uu____8496 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____8436
                                FStar_List.unzip
                               in
                            (match uu____8411 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____8637 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____8637, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____8655 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____8655 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.strcat "Constructor "
                             (Prims.strcat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____8662 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.strcat "Effect "
                             (Prims.strcat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____8673 =
              FStar_List.fold_left
                (fun uu____8718  ->
                   fun b  ->
                     match uu____8718 with
                     | (env1,tparams,typs) ->
                         let uu____8775 = desugar_binder env1 b  in
                         (match uu____8775 with
                          | (xopt,t1) ->
                              let uu____8804 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____8813 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____8813)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____8804 with
                               | (env2,x) ->
                                   let uu____8833 =
                                     let uu____8836 =
                                       let uu____8839 =
                                         let uu____8840 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____8840
                                          in
                                       [uu____8839]  in
                                     FStar_List.append typs uu____8836  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___290_8866 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___290_8866.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___290_8866.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____8833)))) (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      FStar_Pervasives_Native.None])
               in
            (match uu____8673 with
             | (env1,uu____8894,targs) ->
                 let uu____8916 =
                   let uu____8921 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____8921
                    in
                 (match uu____8916 with
                  | (tup,uu____8931) ->
                      let uu____8932 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_app (tup, targs))
                         in
                      (uu____8932, noaqs)))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____8951 = uncurry binders t  in
            (match uu____8951 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___247_8995 =
                   match uu___247_8995 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1  in
                       let uu____9011 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____9011
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____9035 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____9035 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____9068 = aux env [] bs  in (uu____9068, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____9077 = desugar_binder env b  in
            (match uu____9077 with
             | (FStar_Pervasives_Native.None ,uu____9088) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____9102 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____9102 with
                  | ((x,uu____9118),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____9131 =
                        let uu____9132 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____9132  in
                      (uu____9131, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let bvss =
              FStar_List.map (gather_pattern_bound_vars false) binders  in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set1::sets2 ->
                    let i = FStar_Util.set_intersect acc set1  in
                    let uu____9210 = FStar_Util.set_is_empty i  in
                    if uu____9210
                    then
                      let uu____9213 = FStar_Util.set_union acc set1  in
                      aux uu____9213 sets2
                    else
                      (let uu____9217 =
                         let uu____9218 = FStar_Util.set_elements i  in
                         FStar_List.hd uu____9218  in
                       FStar_Pervasives_Native.Some uu____9217)
                 in
              let uu____9221 = FStar_Syntax_Syntax.new_id_set ()  in
              aux uu____9221 sets  in
            ((let uu____9225 = check_disjoint bvss  in
              match uu____9225 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some id1 ->
                  let uu____9229 =
                    let uu____9234 =
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        id1.FStar_Ident.idText
                       in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____9234)
                     in
                  let uu____9235 = FStar_Ident.range_of_id id1  in
                  FStar_Errors.raise_error uu____9229 uu____9235);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern)
                 in
              let uu____9243 =
                FStar_List.fold_left
                  (fun uu____9263  ->
                     fun pat  ->
                       match uu____9263 with
                       | (env1,ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____9289,(t,FStar_Pervasives_Native.None ))
                                ->
                                let uu____9299 =
                                  let uu____9302 = free_type_vars env1 t  in
                                  FStar_List.append uu____9302 ftvs  in
                                (env1, uu____9299)
                            | FStar_Parser_AST.PatAscribed
                                (uu____9307,(t,FStar_Pervasives_Native.Some
                                             tac))
                                ->
                                let uu____9318 =
                                  let uu____9321 = free_type_vars env1 t  in
                                  let uu____9324 =
                                    let uu____9327 = free_type_vars env1 tac
                                       in
                                    FStar_List.append uu____9327 ftvs  in
                                  FStar_List.append uu____9321 uu____9324  in
                                (env1, uu____9318)
                            | uu____9332 -> (env1, ftvs))) (env, []) binders1
                 in
              match uu____9243 with
              | (uu____9341,ftv) ->
                  let ftv1 = sort_ftv ftv  in
                  let binders2 =
                    let uu____9353 =
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
                    FStar_List.append uu____9353 binders1  in
                  let rec aux env1 bs sc_pat_opt uu___248_9410 =
                    match uu___248_9410 with
                    | [] ->
                        let uu____9437 = desugar_term_aq env1 body  in
                        (match uu____9437 with
                         | (body1,aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc,pat) ->
                                   let body2 =
                                     let uu____9474 =
                                       let uu____9475 =
                                         FStar_Syntax_Syntax.pat_bvs pat  in
                                       FStar_All.pipe_right uu____9475
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder)
                                        in
                                     FStar_Syntax_Subst.close uu____9474
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
                             let uu____9544 =
                               let uu____9547 =
                                 no_annot_abs (FStar_List.rev bs) body2  in
                               setpos uu____9547  in
                             (uu____9544, aq))
                    | p::rest ->
                        let uu____9562 = desugar_binding_pat env1 p  in
                        (match uu____9562 with
                         | (env2,b,pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1,uu____9596)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____9611 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange
                                in
                             let uu____9618 =
                               match b with
                               | LetBinder uu____9659 ->
                                   failwith "Impossible"
                               | LocalBinder (x,aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None
                                        ,uu____9727) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.None ) ->
                                         let uu____9781 =
                                           let uu____9790 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____9790, p1)  in
                                         FStar_Pervasives_Native.Some
                                           uu____9781
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.Some
                                        (sc,p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____9852,uu____9853) ->
                                              let tup2 =
                                                let uu____9855 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.parse_int "2")
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____9855
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____9859 =
                                                  let uu____9866 =
                                                    let uu____9867 =
                                                      let uu____9884 =
                                                        mk1
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let uu____9887 =
                                                        let uu____9898 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let uu____9907 =
                                                          let uu____9918 =
                                                            let uu____9927 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____9927
                                                             in
                                                          [uu____9918]  in
                                                        uu____9898 ::
                                                          uu____9907
                                                         in
                                                      (uu____9884,
                                                        uu____9887)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____9867
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____9866
                                                   in
                                                uu____9859
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range
                                                 in
                                              let p2 =
                                                let uu____9978 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____9978
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____10021,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____10023,pats)) ->
                                              let tupn =
                                                let uu____10066 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    ((Prims.parse_int "1") +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10066
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10078 =
                                                  let uu____10079 =
                                                    let uu____10096 =
                                                      mk1
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____10099 =
                                                      let uu____10110 =
                                                        let uu____10121 =
                                                          let uu____10130 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____10130
                                                           in
                                                        [uu____10121]  in
                                                      FStar_List.append args
                                                        uu____10110
                                                       in
                                                    (uu____10096,
                                                      uu____10099)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____10079
                                                   in
                                                mk1 uu____10078  in
                                              let p2 =
                                                let uu____10178 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats [(p1, false)])))
                                                  uu____10178
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____10219 ->
                                              failwith "Impossible")
                                      in
                                   ((x, aq), sc_pat_opt1)
                                in
                             (match uu____9618 with
                              | (b1,sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest))
                     in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____10312,uu____10313,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____10335 =
                let uu____10336 = unparen e  in
                uu____10336.FStar_Parser_AST.tm  in
              match uu____10335 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____10346 ->
                  let uu____10347 = desugar_term_aq env e  in
                  (match uu____10347 with
                   | (head1,aq) ->
                       let uu____10360 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____10360, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____10367 ->
            let rec aux args aqs e =
              let uu____10444 =
                let uu____10445 = unparen e  in
                uu____10445.FStar_Parser_AST.tm  in
              match uu____10444 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____10463 = desugar_term_aq env t  in
                  (match uu____10463 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____10511 ->
                  let uu____10512 = desugar_term_aq env e  in
                  (match uu____10512 with
                   | (head1,aq) ->
                       let uu____10533 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____10533, (join_aqs (aq :: aqs))))
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
            let uu____10593 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____10593
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
            let uu____10645 = desugar_term_aq env t  in
            (match uu____10645 with
             | (tm,s) ->
                 let uu____10656 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____10656, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____10662 =
              let uu____10675 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____10675 then desugar_typ_aq else desugar_term_aq  in
            uu____10662 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____10730 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____10873  ->
                        match uu____10873 with
                        | (attr_opt,(p,def)) ->
                            let uu____10931 = is_app_pattern p  in
                            if uu____10931
                            then
                              let uu____10962 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____10962, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____11044 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____11044, def1)
                               | uu____11089 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____11127);
                                           FStar_Parser_AST.prange =
                                             uu____11128;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____11176 =
                                            let uu____11197 =
                                              let uu____11202 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____11202  in
                                            (uu____11197, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____11176, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____11293) ->
                                        if top_level
                                        then
                                          let uu____11328 =
                                            let uu____11349 =
                                              let uu____11354 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____11354  in
                                            (uu____11349, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____11328, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____11444 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____11475 =
                FStar_List.fold_left
                  (fun uu____11548  ->
                     fun uu____11549  ->
                       match (uu____11548, uu____11549) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____11657,uu____11658),uu____11659))
                           ->
                           let uu____11776 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____11802 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____11802 with
                                  | (env2,xx) ->
                                      let uu____11821 =
                                        let uu____11824 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____11824 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____11821))
                             | FStar_Util.Inr l ->
                                 let uu____11832 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (uu____11832, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____11776 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____11475 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____11980 =
                    match uu____11980 with
                    | (attrs_opt,(uu____12016,args,result_t),def) ->
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
                                let uu____12104 = is_comp_type env1 t  in
                                if uu____12104
                                then
                                  ((let uu____12106 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____12116 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____12116))
                                       in
                                    match uu____12106 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____12119 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____12121 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____12121))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____12119
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
                          | uu____12128 ->
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
                              let uu____12143 =
                                let uu____12144 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____12144
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____12143
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
                  let uu____12221 = desugar_term_aq env' body  in
                  (match uu____12221 with
                   | (body1,aq) ->
                       let uu____12234 =
                         let uu____12237 =
                           let uu____12238 =
                             let uu____12251 =
                               FStar_Syntax_Subst.close rec_bindings1 body1
                                in
                             ((is_rec, lbs1), uu____12251)  in
                           FStar_Syntax_Syntax.Tm_let uu____12238  in
                         FStar_All.pipe_left mk1 uu____12237  in
                       (uu____12234, aq))
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
              let uu____12331 =
                desugar_binding_pat_maybe_top top_level env pat is_mutable
                 in
              match uu____12331 with
              | (env1,binder,pat1) ->
                  let uu____12353 =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let uu____12379 = desugar_term_aq env1 t2  in
                        (match uu____12379 with
                         | (body1,aq) ->
                             let fv =
                               let uu____12393 =
                                 FStar_Syntax_Util.incr_delta_qualifier t12
                                  in
                               FStar_Syntax_Syntax.lid_as_fv l uu____12393
                                 FStar_Pervasives_Native.None
                                in
                             let uu____12394 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t12,
                                            (t12.FStar_Syntax_Syntax.pos))]),
                                      body1))
                                in
                             (uu____12394, aq))
                    | LocalBinder (x,uu____12424) ->
                        let uu____12425 = desugar_term_aq env1 t2  in
                        (match uu____12425 with
                         | (body1,aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | ({
                                    FStar_Syntax_Syntax.v =
                                      FStar_Syntax_Syntax.Pat_wild
                                      uu____12439;
                                    FStar_Syntax_Syntax.p = uu____12440;_},uu____12441)::[]
                                   -> body1
                               | uu____12454 ->
                                   let uu____12457 =
                                     let uu____12464 =
                                       let uu____12465 =
                                         let uu____12488 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         let uu____12491 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1
                                            in
                                         (uu____12488, uu____12491)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____12465
                                        in
                                     FStar_Syntax_Syntax.mk uu____12464  in
                                   uu____12457 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range
                                in
                             let uu____12531 =
                               let uu____12534 =
                                 let uu____12535 =
                                   let uu____12548 =
                                     let uu____12551 =
                                       let uu____12552 =
                                         FStar_Syntax_Syntax.mk_binder x  in
                                       [uu____12552]  in
                                     FStar_Syntax_Subst.close uu____12551
                                       body2
                                      in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t12,
                                           (t12.FStar_Syntax_Syntax.pos))]),
                                     uu____12548)
                                    in
                                 FStar_Syntax_Syntax.Tm_let uu____12535  in
                               FStar_All.pipe_left mk1 uu____12534  in
                             (uu____12531, aq))
                     in
                  (match uu____12353 with
                   | (tm,aq) ->
                       if is_mutable
                       then
                         let uu____12615 =
                           FStar_All.pipe_left mk1
                             (FStar_Syntax_Syntax.Tm_meta
                                (tm,
                                  (FStar_Syntax_Syntax.Meta_desugared
                                     FStar_Syntax_Syntax.Mutable_alloc)))
                            in
                         (uu____12615, aq)
                       else (tm, aq))
               in
            let uu____12627 = FStar_List.hd lbs  in
            (match uu____12627 with
             | (attrs,(head_pat,defn)) ->
                 let uu____12671 = is_rec || (is_app_pattern head_pat)  in
                 if uu____12671
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____12684 =
                let uu____12685 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____12685  in
              mk1 uu____12684  in
            let uu____12686 = desugar_term_aq env t1  in
            (match uu____12686 with
             | (t1',aq1) ->
                 let uu____12697 = desugar_term_aq env t2  in
                 (match uu____12697 with
                  | (t2',aq2) ->
                      let uu____12708 = desugar_term_aq env t3  in
                      (match uu____12708 with
                       | (t3',aq3) ->
                           let uu____12719 =
                             let uu____12720 =
                               let uu____12721 =
                                 let uu____12744 =
                                   let uu____12761 =
                                     let uu____12776 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t2.FStar_Parser_AST.range
                                        in
                                     (uu____12776,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____12789 =
                                     let uu____12806 =
                                       let uu____12821 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t3.FStar_Parser_AST.range
                                          in
                                       (uu____12821,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____12806]  in
                                   uu____12761 :: uu____12789  in
                                 (t1', uu____12744)  in
                               FStar_Syntax_Syntax.Tm_match uu____12721  in
                             mk1 uu____12720  in
                           (uu____12719, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____13012 =
              match uu____13012 with
              | (pat,wopt,b) ->
                  let uu____13034 = desugar_match_pat env pat  in
                  (match uu____13034 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____13065 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____13065
                          in
                       let uu____13070 = desugar_term_aq env1 b  in
                       (match uu____13070 with
                        | (b1,aq) ->
                            let uu____13083 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____13083, aq)))
               in
            let uu____13088 = desugar_term_aq env e  in
            (match uu____13088 with
             | (e1,aq) ->
                 let uu____13099 =
                   let uu____13130 =
                     let uu____13163 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____13163 FStar_List.unzip  in
                   FStar_All.pipe_right uu____13130
                     (fun uu____13293  ->
                        match uu____13293 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____13099 with
                  | (brs,aqs) ->
                      let uu____13512 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____13512, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____13546 =
              let uu____13567 = is_comp_type env t  in
              if uu____13567
              then
                let comp = desugar_comp t.FStar_Parser_AST.range env t  in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____13618 = desugar_term_aq env t  in
                 match uu____13618 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____13546 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____13710 = desugar_term_aq env e  in
                 (match uu____13710 with
                  | (e1,aq) ->
                      let uu____13721 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____13721, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____13760,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____13801 = FStar_List.hd fields  in
              match uu____13801 with | (f,uu____13813) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____13859  ->
                        match uu____13859 with
                        | (g,uu____13865) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____13871,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____13885 =
                         let uu____13890 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____13890)
                          in
                       FStar_Errors.raise_error uu____13885
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
                  let uu____13898 =
                    let uu____13909 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____13940  ->
                              match uu____13940 with
                              | (f,uu____13950) ->
                                  let uu____13951 =
                                    let uu____13952 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____13952
                                     in
                                  (uu____13951, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____13909)  in
                  FStar_Parser_AST.Construct uu____13898
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____13970 =
                      let uu____13971 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____13971  in
                    FStar_Parser_AST.mk_term uu____13970
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____13973 =
                      let uu____13986 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____14016  ->
                                match uu____14016 with
                                | (f,uu____14026) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____13986)  in
                    FStar_Parser_AST.Record uu____13973  in
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
            let uu____14086 = desugar_term_aq env recterm1  in
            (match uu____14086 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____14102;
                         FStar_Syntax_Syntax.vars = uu____14103;_},args)
                      ->
                      let uu____14129 =
                        let uu____14130 =
                          let uu____14131 =
                            let uu____14148 =
                              let uu____14151 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____14152 =
                                let uu____14155 =
                                  let uu____14156 =
                                    let uu____14163 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____14163)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____14156
                                   in
                                FStar_Pervasives_Native.Some uu____14155  in
                              FStar_Syntax_Syntax.fvar uu____14151
                                FStar_Syntax_Syntax.delta_constant
                                uu____14152
                               in
                            (uu____14148, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____14131  in
                        FStar_All.pipe_left mk1 uu____14130  in
                      (uu____14129, s)
                  | uu____14192 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____14196 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____14196 with
              | (constrname,is_rec) ->
                  let uu____14211 = desugar_term_aq env e  in
                  (match uu____14211 with
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
                       let uu____14229 =
                         let uu____14230 =
                           let uu____14231 =
                             let uu____14248 =
                               let uu____14251 =
                                 let uu____14252 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____14252
                                  in
                               FStar_Syntax_Syntax.fvar uu____14251
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1")) qual
                                in
                             let uu____14253 =
                               let uu____14264 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____14264]  in
                             (uu____14248, uu____14253)  in
                           FStar_Syntax_Syntax.Tm_app uu____14231  in
                         FStar_All.pipe_left mk1 uu____14230  in
                       (uu____14229, s))))
        | FStar_Parser_AST.NamedTyp (uu____14301,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____14310 =
              let uu____14311 = FStar_Syntax_Subst.compress tm  in
              uu____14311.FStar_Syntax_Syntax.n  in
            (match uu____14310 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____14319 =
                   let uu___291_14320 =
                     let uu____14321 =
                       let uu____14322 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____14322  in
                     FStar_Syntax_Util.exp_string uu____14321  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___291_14320.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___291_14320.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____14319, noaqs)
             | uu____14323 ->
                 let uu____14324 =
                   let uu____14329 =
                     let uu____14330 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.strcat "VQuote, expected an fvar, got: "
                       uu____14330
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____14329)  in
                 FStar_Errors.raise_error uu____14324
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____14336 = desugar_term_aq env e  in
            (match uu____14336 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____14348 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____14348, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____14353 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____14354 =
              let uu____14355 =
                let uu____14362 = desugar_term env e  in (bv, uu____14362)
                 in
              [uu____14355]  in
            (uu____14353, uu____14354)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____14387 =
              let uu____14388 =
                let uu____14389 =
                  let uu____14396 = desugar_term env e  in (uu____14396, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____14389  in
              FStar_All.pipe_left mk1 uu____14388  in
            (uu____14387, noaqs)
        | uu____14401 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____14402 = desugar_formula env top  in
            (uu____14402, noaqs)
        | uu____14403 ->
            let uu____14404 =
              let uu____14409 =
                let uu____14410 = FStar_Parser_AST.term_to_string top  in
                Prims.strcat "Unexpected term: " uu____14410  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____14409)  in
            FStar_Errors.raise_error uu____14404 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____14416 -> false
    | uu____14425 -> true

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
           (fun uu____14462  ->
              match uu____14462 with
              | (a,imp) ->
                  let uu____14475 = desugar_term env a  in
                  arg_withimp_e imp uu____14475))

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
        let is_requires uu____14507 =
          match uu____14507 with
          | (t1,uu____14513) ->
              let uu____14514 =
                let uu____14515 = unparen t1  in
                uu____14515.FStar_Parser_AST.tm  in
              (match uu____14514 with
               | FStar_Parser_AST.Requires uu____14516 -> true
               | uu____14523 -> false)
           in
        let is_ensures uu____14533 =
          match uu____14533 with
          | (t1,uu____14539) ->
              let uu____14540 =
                let uu____14541 = unparen t1  in
                uu____14541.FStar_Parser_AST.tm  in
              (match uu____14540 with
               | FStar_Parser_AST.Ensures uu____14542 -> true
               | uu____14549 -> false)
           in
        let is_app head1 uu____14564 =
          match uu____14564 with
          | (t1,uu____14570) ->
              let uu____14571 =
                let uu____14572 = unparen t1  in
                uu____14572.FStar_Parser_AST.tm  in
              (match uu____14571 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____14574;
                      FStar_Parser_AST.level = uu____14575;_},uu____14576,uu____14577)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____14578 -> false)
           in
        let is_smt_pat uu____14588 =
          match uu____14588 with
          | (t1,uu____14594) ->
              let uu____14595 =
                let uu____14596 = unparen t1  in
                uu____14596.FStar_Parser_AST.tm  in
              (match uu____14595 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____14599);
                             FStar_Parser_AST.range = uu____14600;
                             FStar_Parser_AST.level = uu____14601;_},uu____14602)::uu____14603::[])
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
                             FStar_Parser_AST.range = uu____14642;
                             FStar_Parser_AST.level = uu____14643;_},uu____14644)::uu____14645::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
               | uu____14670 -> false)
           in
        let is_decreases = is_app "decreases"  in
        let pre_process_comp_typ t1 =
          let uu____14702 = head_and_args t1  in
          match uu____14702 with
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
                   let thunk_ens uu____14800 =
                     match uu____14800 with
                     | (e,i) ->
                         let uu____14811 = thunk_ens_ e  in (uu____14811, i)
                      in
                   let fail_lemma uu____14823 =
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
                         let uu____14903 =
                           let uu____14910 =
                             let uu____14917 = thunk_ens ens  in
                             [uu____14917; nil_pat]  in
                           req_true :: uu____14910  in
                         unit_tm :: uu____14903
                     | req::ens::[] when
                         (is_requires req) && (is_ensures ens) ->
                         let uu____14964 =
                           let uu____14971 =
                             let uu____14978 = thunk_ens ens  in
                             [uu____14978; nil_pat]  in
                           req :: uu____14971  in
                         unit_tm :: uu____14964
                     | ens::smtpat::[] when
                         (((let uu____15027 = is_requires ens  in
                            Prims.op_Negation uu____15027) &&
                             (let uu____15029 = is_smt_pat ens  in
                              Prims.op_Negation uu____15029))
                            &&
                            (let uu____15031 = is_decreases ens  in
                             Prims.op_Negation uu____15031))
                           && (is_smt_pat smtpat)
                         ->
                         let uu____15032 =
                           let uu____15039 =
                             let uu____15046 = thunk_ens ens  in
                             [uu____15046; smtpat]  in
                           req_true :: uu____15039  in
                         unit_tm :: uu____15032
                     | ens::dec::[] when
                         (is_ensures ens) && (is_decreases dec) ->
                         let uu____15093 =
                           let uu____15100 =
                             let uu____15107 = thunk_ens ens  in
                             [uu____15107; nil_pat; dec]  in
                           req_true :: uu____15100  in
                         unit_tm :: uu____15093
                     | ens::dec::smtpat::[] when
                         ((is_ensures ens) && (is_decreases dec)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____15167 =
                           let uu____15174 =
                             let uu____15181 = thunk_ens ens  in
                             [uu____15181; smtpat; dec]  in
                           req_true :: uu____15174  in
                         unit_tm :: uu____15167
                     | req::ens::dec::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_decreases dec)
                         ->
                         let uu____15241 =
                           let uu____15248 =
                             let uu____15255 = thunk_ens ens  in
                             [uu____15255; nil_pat; dec]  in
                           req :: uu____15248  in
                         unit_tm :: uu____15241
                     | req::ens::smtpat::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____15315 =
                           let uu____15322 =
                             let uu____15329 = thunk_ens ens  in
                             [uu____15329; smtpat]  in
                           req :: uu____15322  in
                         unit_tm :: uu____15315
                     | req::ens::dec::smtpat::[] when
                         (((is_requires req) && (is_ensures ens)) &&
                            (is_smt_pat smtpat))
                           && (is_decreases dec)
                         ->
                         let uu____15394 =
                           let uu____15401 =
                             let uu____15408 = thunk_ens ens  in
                             [uu____15408; dec; smtpat]  in
                           req :: uu____15401  in
                         unit_tm :: uu____15394
                     | _other -> fail_lemma ()  in
                   let head_and_attributes =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) lemma
                      in
                   (head_and_attributes, args1)
               | FStar_Parser_AST.Name l when
                   FStar_Syntax_DsEnv.is_effect_name env l ->
                   let uu____15470 =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) l
                      in
                   (uu____15470, args)
               | FStar_Parser_AST.Name l when
                   (let uu____15498 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____15498
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   let uu____15499 =
                     let uu____15506 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_Tot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____15506, [])  in
                   (uu____15499, args)
               | FStar_Parser_AST.Name l when
                   (let uu____15524 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____15524
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                   ->
                   let uu____15525 =
                     let uu____15532 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_GTot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____15532, [])  in
                   (uu____15525, args)
               | FStar_Parser_AST.Name l when
                   (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                      ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                     || ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                   ->
                   let uu____15548 =
                     let uu____15555 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_Tot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____15555, [])  in
                   (uu____15548, [(t1, FStar_Parser_AST.Nothing)])
               | uu____15578 ->
                   let default_effect =
                     let uu____15580 = FStar_Options.ml_ish ()  in
                     if uu____15580
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____15583 =
                           FStar_Options.warn_default_effects ()  in
                         if uu____15583
                         then
                           FStar_Errors.log_issue
                             head1.FStar_Parser_AST.range
                             (FStar_Errors.Warning_UseDefaultEffect,
                               "Using default effect Tot")
                         else ());
                        FStar_Parser_Const.effect_Tot_lid)
                      in
                   let uu____15585 =
                     let uu____15592 =
                       FStar_Ident.set_lid_range default_effect
                         head1.FStar_Parser_AST.range
                        in
                     (uu____15592, [])  in
                   (uu____15585, [(t1, FStar_Parser_AST.Nothing)]))
           in
        let uu____15615 = pre_process_comp_typ t  in
        match uu____15615 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____15664 =
                  let uu____15669 =
                    let uu____15670 = FStar_Syntax_Print.lid_to_string eff
                       in
                    FStar_Util.format1 "Not enough args to effect %s"
                      uu____15670
                     in
                  (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____15669)  in
                fail1 uu____15664)
             else ();
             (let is_universe uu____15681 =
                match uu____15681 with
                | (uu____15686,imp) -> imp = FStar_Parser_AST.UnivApp  in
              let uu____15688 = FStar_Util.take is_universe args  in
              match uu____15688 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____15747  ->
                         match uu____15747 with
                         | (u,imp) -> desugar_universe u) universes
                     in
                  let uu____15754 =
                    let uu____15769 = FStar_List.hd args1  in
                    let uu____15778 = FStar_List.tl args1  in
                    (uu____15769, uu____15778)  in
                  (match uu____15754 with
                   | (result_arg,rest) ->
                       let result_typ =
                         desugar_typ env
                           (FStar_Pervasives_Native.fst result_arg)
                          in
                       let rest1 = desugar_args env rest  in
                       let uu____15833 =
                         let is_decrease uu____15871 =
                           match uu____15871 with
                           | (t1,uu____15881) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.pos = uu____15891;
                                       FStar_Syntax_Syntax.vars = uu____15892;_},uu____15893::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.decreases_lid
                                | uu____15932 -> false)
                            in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease)
                          in
                       (match uu____15833 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____16048  ->
                                      match uu____16048 with
                                      | (t1,uu____16058) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____16067,(arg,uu____16069)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____16108 -> failwith "impos")))
                               in
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
                                | uu____16125 -> false  in
                              (((is_empty decreases_clause) &&
                                  (is_empty rest2))
                                 && (is_empty cattributes))
                                && (is_empty universes1)
                               in
                            let uu____16136 =
                              no_additional_args &&
                                (FStar_Ident.lid_equals eff
                                   FStar_Parser_Const.effect_Tot_lid)
                               in
                            if uu____16136
                            then FStar_Syntax_Syntax.mk_Total result_typ
                            else
                              (let uu____16140 =
                                 no_additional_args &&
                                   (FStar_Ident.lid_equals eff
                                      FStar_Parser_Const.effect_GTot_lid)
                                  in
                               if uu____16140
                               then FStar_Syntax_Syntax.mk_GTotal result_typ
                               else
                                 (let flags1 =
                                    let uu____16147 =
                                      FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_Lemma_lid
                                       in
                                    if uu____16147
                                    then [FStar_Syntax_Syntax.LEMMA]
                                    else
                                      (let uu____16151 =
                                         FStar_Ident.lid_equals eff
                                           FStar_Parser_Const.effect_Tot_lid
                                          in
                                       if uu____16151
                                       then [FStar_Syntax_Syntax.TOTAL]
                                       else
                                         (let uu____16155 =
                                            FStar_Ident.lid_equals eff
                                              FStar_Parser_Const.effect_ML_lid
                                             in
                                          if uu____16155
                                          then [FStar_Syntax_Syntax.MLEFFECT]
                                          else
                                            (let uu____16159 =
                                               FStar_Ident.lid_equals eff
                                                 FStar_Parser_Const.effect_GTot_lid
                                                in
                                             if uu____16159
                                             then
                                               [FStar_Syntax_Syntax.SOMETRIVIAL]
                                             else [])))
                                     in
                                  let flags2 =
                                    FStar_List.append flags1 cattributes  in
                                  let rest3 =
                                    let uu____16177 =
                                      FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_Lemma_lid
                                       in
                                    if uu____16177
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
                                                  let uu____16266 =
                                                    FStar_Ident.set_lid_range
                                                      FStar_Parser_Const.pattern_lid
                                                      pat.FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_Syntax.fvar
                                                    uu____16266
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
                                            | uu____16287 -> pat  in
                                          let uu____16288 =
                                            let uu____16299 =
                                              let uu____16310 =
                                                let uu____16319 =
                                                  FStar_Syntax_Syntax.mk
                                                    (FStar_Syntax_Syntax.Tm_meta
                                                       (pat1,
                                                         (FStar_Syntax_Syntax.Meta_desugared
                                                            FStar_Syntax_Syntax.Meta_smt_pat)))
                                                    FStar_Pervasives_Native.None
                                                    pat1.FStar_Syntax_Syntax.pos
                                                   in
                                                (uu____16319, aq)  in
                                              [uu____16310]  in
                                            ens :: uu____16299  in
                                          req :: uu____16288
                                      | uu____16360 -> rest2
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
        | uu____16384 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___292_16405 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___292_16405.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___292_16405.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___293_16447 = b  in
             {
               FStar_Parser_AST.b = (uu___293_16447.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___293_16447.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___293_16447.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____16510 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____16510)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____16523 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____16523 with
             | (env1,a1) ->
                 let a2 =
                   let uu___294_16533 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___294_16533.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___294_16533.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____16559 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____16573 =
                     let uu____16576 =
                       let uu____16577 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____16577]  in
                     no_annot_abs uu____16576 body2  in
                   FStar_All.pipe_left setpos uu____16573  in
                 let uu____16598 =
                   let uu____16599 =
                     let uu____16616 =
                       let uu____16619 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____16619
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____16620 =
                       let uu____16631 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____16631]  in
                     (uu____16616, uu____16620)  in
                   FStar_Syntax_Syntax.Tm_app uu____16599  in
                 FStar_All.pipe_left mk1 uu____16598)
        | uu____16670 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____16750 = q (rest, pats, body)  in
              let uu____16757 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____16750 uu____16757
                FStar_Parser_AST.Formula
               in
            let uu____16758 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____16758 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____16767 -> failwith "impossible"  in
      let uu____16770 =
        let uu____16771 = unparen f  in uu____16771.FStar_Parser_AST.tm  in
      match uu____16770 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____16778,uu____16779) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____16790,uu____16791) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____16822 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____16822
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____16858 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____16858
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____16901 -> desugar_term env f

and (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                FStar_Pervasives_Native.tuple2 Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bs  ->
      let uu____16906 =
        FStar_List.fold_left
          (fun uu____16939  ->
             fun b  ->
               match uu____16939 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___295_16983 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___295_16983.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___295_16983.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___295_16983.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____16998 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____16998 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___296_17016 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___296_17016.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___296_17016.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____17017 =
                               let uu____17024 =
                                 let uu____17029 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____17029)  in
                               uu____17024 :: out  in
                             (env2, uu____17017))
                    | uu____17040 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____16906 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

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
          let uu____17111 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____17111)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____17116 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____17116)
      | FStar_Parser_AST.TVariable x ->
          let uu____17120 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____17120)
      | FStar_Parser_AST.NoName t ->
          let uu____17124 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____17124)
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
      fun uu___249_17132  ->
        match uu___249_17132 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____17154 = FStar_Syntax_Syntax.null_binder k  in
            (uu____17154, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____17171 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____17171 with
             | (env1,a1) ->
                 let uu____17188 =
                   let uu____17195 = trans_aqual env1 imp  in
                   ((let uu___297_17201 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___297_17201.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___297_17201.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____17195)
                    in
                 (uu____17188, env1))

and (trans_aqual :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___250_17209  ->
      match uu___250_17209 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____17213 =
            let uu____17214 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____17214  in
          FStar_Pervasives_Native.Some uu____17213
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
               (fun uu___251_17250  ->
                  match uu___251_17250 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____17251 -> false))
           in
        let quals2 q =
          let uu____17264 =
            (let uu____17267 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____17267) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____17264
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____17281 = FStar_Ident.range_of_lid disc_name  in
                let uu____17282 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____17281;
                  FStar_Syntax_Syntax.sigquals = uu____17282;
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
            let uu____17321 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____17359  ->
                        match uu____17359 with
                        | (x,uu____17369) ->
                            let uu____17374 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____17374 with
                             | (field_name,uu____17382) ->
                                 let only_decl =
                                   ((let uu____17386 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____17386)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____17388 =
                                        let uu____17389 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____17389.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____17388)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____17405 =
                                       FStar_List.filter
                                         (fun uu___252_17409  ->
                                            match uu___252_17409 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____17410 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____17405
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___253_17423  ->
                                             match uu___253_17423 with
                                             | FStar_Syntax_Syntax.NoExtract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____17424 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____17426 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____17426;
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____17431 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____17431
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          (FStar_Syntax_Syntax.Delta_equational_at_level
                                             (Prims.parse_int "1"))
                                      else
                                        FStar_Syntax_Syntax.Delta_equational_at_level
                                          (Prims.parse_int "1")
                                       in
                                    let lb =
                                      let uu____17436 =
                                        let uu____17441 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____17441  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____17436;
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
                                      let uu____17445 =
                                        let uu____17446 =
                                          let uu____17453 =
                                            let uu____17456 =
                                              let uu____17457 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____17457
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____17456]  in
                                          ((false, [lb]), uu____17453)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____17446
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____17445;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____17321 FStar_List.flatten
  
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
            (lid,uu____17501,t,uu____17503,n1,uu____17505) when
            let uu____17510 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____17510 ->
            let uu____17511 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____17511 with
             | (formals,uu____17529) ->
                 (match formals with
                  | [] -> []
                  | uu____17558 ->
                      let filter_records uu___254_17574 =
                        match uu___254_17574 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____17577,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____17589 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____17591 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____17591 with
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
                      let uu____17601 = FStar_Util.first_N n1 formals  in
                      (match uu____17601 with
                       | (uu____17630,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____17664 -> []
  
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
                    let uu____17742 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____17742
                    then
                      let uu____17745 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____17745
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____17748 =
                      let uu____17753 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____17753  in
                    let uu____17754 =
                      if FStar_Util.is_some kopt
                      then
                        let uu____17759 =
                          let uu____17762 =
                            FStar_All.pipe_right kopt FStar_Util.must  in
                          FStar_Syntax_Syntax.mk_Total uu____17762  in
                        FStar_Syntax_Util.arrow typars uu____17759
                      else FStar_Syntax_Syntax.tun  in
                    let uu____17766 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____17748;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____17754;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____17766;
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
          let tycon_id uu___255_17817 =
            match uu___255_17817 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____17819,uu____17820) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____17830,uu____17831,uu____17832) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____17842,uu____17843,uu____17844) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____17874,uu____17875,uu____17876) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____17920) ->
                let uu____17921 =
                  let uu____17922 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____17922  in
                FStar_Parser_AST.mk_term uu____17921 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____17924 =
                  let uu____17925 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____17925  in
                FStar_Parser_AST.mk_term uu____17924 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____17927) ->
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
              | uu____17958 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____17966 =
                     let uu____17967 =
                       let uu____17974 = binder_to_term b  in
                       (out, uu____17974, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____17967  in
                   FStar_Parser_AST.mk_term uu____17966
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___256_17986 =
            match uu___256_17986 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____18042  ->
                       match uu____18042 with
                       | (x,t,uu____18053) ->
                           let uu____18058 =
                             let uu____18059 =
                               let uu____18064 =
                                 FStar_Syntax_Util.mangle_field_name x  in
                               (uu____18064, t)  in
                             FStar_Parser_AST.Annotated uu____18059  in
                           FStar_Parser_AST.mk_binder uu____18058
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____18066 =
                    let uu____18067 =
                      let uu____18068 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____18068  in
                    FStar_Parser_AST.mk_term uu____18067
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____18066 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let uu____18072 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____18099  ->
                          match uu____18099 with
                          | (x,uu____18109,uu____18110) ->
                              FStar_Syntax_Util.unmangle_field_name x))
                   in
                ((FStar_Parser_AST.TyconVariant
                    (id1, parms, kopt,
                      [(constrName, (FStar_Pervasives_Native.Some constrTyp),
                         FStar_Pervasives_Native.None, false)])),
                  uu____18072)
            | uu____18163 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___257_18202 =
            match uu___257_18202 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____18226 = typars_of_binders _env binders  in
                (match uu____18226 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____18262 =
                         let uu____18263 =
                           let uu____18264 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____18264  in
                         FStar_Parser_AST.mk_term uu____18263
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____18262 binders  in
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
            | uu____18275 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____18317 =
              FStar_List.fold_left
                (fun uu____18351  ->
                   fun uu____18352  ->
                     match (uu____18351, uu____18352) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____18421 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____18421 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____18317 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____18512 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____18512
                | uu____18513 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____18521 = desugar_abstract_tc quals env [] tc  in
              (match uu____18521 with
               | (uu____18534,uu____18535,se,uu____18537) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____18540,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____18557 =
                                 let uu____18558 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____18558  in
                               if uu____18557
                               then
                                 let uu____18559 =
                                   let uu____18564 =
                                     let uu____18565 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____18565
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____18564)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____18559
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
                           | uu____18574 ->
                               let uu____18575 =
                                 let uu____18582 =
                                   let uu____18583 =
                                     let uu____18598 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____18598)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____18583
                                    in
                                 FStar_Syntax_Syntax.mk uu____18582  in
                               uu____18575 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___298_18614 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___298_18614.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___298_18614.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___298_18614.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____18615 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____18618 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____18618
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____18631 = typars_of_binders env binders  in
              (match uu____18631 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____18665 =
                           FStar_Util.for_some
                             (fun uu___258_18667  ->
                                match uu___258_18667 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____18668 -> false) quals
                            in
                         if uu____18665
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____18673 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____18673
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____18678 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___259_18682  ->
                               match uu___259_18682 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____18683 -> false))
                        in
                     if uu____18678
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____18692 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____18692
                     then
                       let uu____18695 =
                         let uu____18702 =
                           let uu____18703 = unparen t  in
                           uu____18703.FStar_Parser_AST.tm  in
                         match uu____18702 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____18724 =
                               match FStar_List.rev args with
                               | (last_arg,uu____18754)::args_rev ->
                                   let uu____18766 =
                                     let uu____18767 = unparen last_arg  in
                                     uu____18767.FStar_Parser_AST.tm  in
                                   (match uu____18766 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____18795 -> ([], args))
                               | uu____18804 -> ([], args)  in
                             (match uu____18724 with
                              | (cattributes,args1) ->
                                  let uu____18843 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____18843))
                         | uu____18854 -> (t, [])  in
                       match uu____18695 with
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
                                  (fun uu___260_18876  ->
                                     match uu___260_18876 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____18877 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____18884)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____18908 = tycon_record_as_variant trec  in
              (match uu____18908 with
               | (t,fs) ->
                   let uu____18925 =
                     let uu____18928 =
                       let uu____18929 =
                         let uu____18938 =
                           let uu____18941 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____18941  in
                         (uu____18938, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____18929  in
                     uu____18928 :: quals  in
                   desugar_tycon env d uu____18925 [t])
          | uu____18946::uu____18947 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____19114 = et  in
                match uu____19114 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____19339 ->
                         let trec = tc  in
                         let uu____19363 = tycon_record_as_variant trec  in
                         (match uu____19363 with
                          | (t,fs) ->
                              let uu____19422 =
                                let uu____19425 =
                                  let uu____19426 =
                                    let uu____19435 =
                                      let uu____19438 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____19438  in
                                    (uu____19435, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____19426
                                   in
                                uu____19425 :: quals1  in
                              collect_tcs uu____19422 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____19525 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____19525 with
                          | (env2,uu____19585,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____19734 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____19734 with
                          | (env2,uu____19794,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____19919 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____19966 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____19966 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___262_20471  ->
                             match uu___262_20471 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____20536,uu____20537);
                                    FStar_Syntax_Syntax.sigrng = uu____20538;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____20539;
                                    FStar_Syntax_Syntax.sigmeta = uu____20540;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____20541;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____20604 =
                                     typars_of_binders env1 binders  in
                                   match uu____20604 with
                                   | (env2,tpars1) ->
                                       let uu____20631 =
                                         push_tparams env2 tpars1  in
                                       (match uu____20631 with
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
                                 let uu____20660 =
                                   let uu____20679 =
                                     mk_typ_abbrev id1 uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____20679)
                                    in
                                 [uu____20660]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____20739);
                                    FStar_Syntax_Syntax.sigrng = uu____20740;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____20742;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____20743;_},constrs,tconstr,quals1)
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
                                 let uu____20841 = push_tparams env1 tpars
                                    in
                                 (match uu____20841 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____20908  ->
                                             match uu____20908 with
                                             | (x,uu____20920) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____20924 =
                                        let uu____20951 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____21059  ->
                                                  match uu____21059 with
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
                                                        let uu____21113 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____21113
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
                                                                uu___261_21124
                                                                 ->
                                                                match uu___261_21124
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____21136
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____21144 =
                                                        let uu____21163 =
                                                          let uu____21164 =
                                                            let uu____21165 =
                                                              let uu____21180
                                                                =
                                                                let uu____21181
                                                                  =
                                                                  let uu____21184
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____21184
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____21181
                                                                 in
                                                              (name, univs1,
                                                                uu____21180,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____21165
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____21164;
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
                                                          uu____21163)
                                                         in
                                                      (name, uu____21144)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____20951
                                         in
                                      (match uu____20924 with
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
                             | uu____21399 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____21525  ->
                             match uu____21525 with
                             | (name_doc,uu____21551,uu____21552) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____21624  ->
                             match uu____21624 with
                             | (uu____21643,uu____21644,se) -> se))
                      in
                   let uu____21670 =
                     let uu____21677 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____21677 rng
                      in
                   (match uu____21670 with
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
                               (fun uu____21739  ->
                                  match uu____21739 with
                                  | (uu____21760,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____21807,tps,k,uu____21810,constrs)
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
                                  | uu____21829 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____21846  ->
                                 match uu____21846 with
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
      let uu____21889 =
        FStar_List.fold_left
          (fun uu____21924  ->
             fun b  ->
               match uu____21924 with
               | (env1,binders1) ->
                   let uu____21968 = desugar_binder env1 b  in
                   (match uu____21968 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____21991 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____21991 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____22044 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____21889 with
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
          let uu____22145 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___263_22150  ->
                    match uu___263_22150 with
                    | FStar_Syntax_Syntax.Reflectable uu____22151 -> true
                    | uu____22152 -> false))
             in
          if uu____22145
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____22155 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____22155
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
      let uu____22187 = FStar_Syntax_Util.head_and_args at1  in
      match uu____22187 with
      | (hd1,args) ->
          let uu____22238 =
            let uu____22253 =
              let uu____22254 = FStar_Syntax_Subst.compress hd1  in
              uu____22254.FStar_Syntax_Syntax.n  in
            (uu____22253, args)  in
          (match uu____22238 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(a1,uu____22277)::[]) when
               (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr)
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.fail_lax_attr)
               ->
               let uu____22312 =
                 let uu____22317 =
                   let uu____22326 =
                     FStar_Syntax_Embeddings.e_list
                       FStar_Syntax_Embeddings.e_int
                      in
                   FStar_Syntax_Embeddings.unembed uu____22326 a1  in
                 uu____22317 true FStar_Syntax_Embeddings.id_norm_cb  in
               (match uu____22312 with
                | FStar_Pervasives_Native.Some es when
                    (FStar_List.length es) > (Prims.parse_int "0") ->
                    let b =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.fail_lax_attr
                       in
                    let uu____22351 =
                      let uu____22358 =
                        FStar_List.map FStar_BigInt.to_int_fs es  in
                      (uu____22358, b)  in
                    FStar_Pervasives_Native.Some uu____22351
                | uu____22369 ->
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
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____22411) when
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
           | uu____22440 -> FStar_Pervasives_Native.None)
  
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
                  let uu____22609 = desugar_binders monad_env eff_binders  in
                  match uu____22609 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let for_free =
                        let uu____22648 =
                          let uu____22649 =
                            let uu____22658 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____22658  in
                          FStar_List.length uu____22649  in
                        uu____22648 = (Prims.parse_int "1")  in
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
                            (uu____22704,uu____22705,(FStar_Parser_AST.TyconAbbrev
                                                      (name,uu____22707,uu____22708,uu____22709),uu____22710)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____22743 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____22744 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____22756 = name_of_eff_decl decl  in
                             FStar_List.mem uu____22756 mandatory_members)
                          eff_decls
                         in
                      (match uu____22744 with
                       | (mandatory_members_decls,actions) ->
                           let uu____22773 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____22802  ->
                                     fun decl  ->
                                       match uu____22802 with
                                       | (env2,out) ->
                                           let uu____22822 =
                                             desugar_decl env2 decl  in
                                           (match uu____22822 with
                                            | (env3,ses) ->
                                                let uu____22835 =
                                                  let uu____22838 =
                                                    FStar_List.hd ses  in
                                                  uu____22838 :: out  in
                                                (env3, uu____22835)))
                                  (env1, []))
                              in
                           (match uu____22773 with
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
                                              (uu____22907,uu____22908,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____22911,
                                                 {
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.Construct
                                                     (uu____22912,(def,uu____22914)::
                                                      (cps_type,uu____22916)::[]);
                                                   FStar_Parser_AST.range =
                                                     uu____22917;
                                                   FStar_Parser_AST.level =
                                                     uu____22918;_}),doc1)::[])
                                              when Prims.op_Negation for_free
                                              ->
                                              let uu____22970 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____22970 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____23008 =
                                                     let uu____23009 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____23010 =
                                                       let uu____23011 =
                                                         desugar_term env3
                                                           def
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____23011
                                                        in
                                                     let uu____23018 =
                                                       let uu____23019 =
                                                         desugar_typ env3
                                                           cps_type
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____23019
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____23009;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____23010;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____23018
                                                     }  in
                                                   (uu____23008, doc1))
                                          | FStar_Parser_AST.Tycon
                                              (uu____23028,uu____23029,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____23032,defn),doc1)::[])
                                              when for_free ->
                                              let uu____23067 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____23067 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____23105 =
                                                     let uu____23106 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____23107 =
                                                       let uu____23108 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____23108
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____23106;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____23107;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____23105, doc1))
                                          | uu____23117 ->
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
                                    let uu____23149 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____23149
                                     in
                                  let uu____23150 =
                                    let uu____23151 =
                                      FStar_Syntax_DsEnv.fail_or env2
                                        (FStar_Syntax_DsEnv.try_lookup_definition
                                           env2) l
                                       in
                                    FStar_All.pipe_left
                                      (FStar_Syntax_Subst.close binders1)
                                      uu____23151
                                     in
                                  ([], uu____23150)  in
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
                                      let uu____23168 =
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      ([], uu____23168)  in
                                    let uu____23175 =
                                      let uu____23176 =
                                        let uu____23177 =
                                          let uu____23178 = lookup1 "repr"
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____23178
                                           in
                                        let uu____23187 = lookup1 "return"
                                           in
                                        let uu____23188 = lookup1 "bind"  in
                                        let uu____23189 =
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
                                            uu____23177;
                                          FStar_Syntax_Syntax.return_repr =
                                            uu____23187;
                                          FStar_Syntax_Syntax.bind_repr =
                                            uu____23188;
                                          FStar_Syntax_Syntax.actions =
                                            actions1;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            uu____23189
                                        }  in
                                      FStar_Syntax_Syntax.Sig_new_effect_for_free
                                        uu____23176
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____23175;
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
                                         (fun uu___264_23195  ->
                                            match uu___264_23195 with
                                            | FStar_Syntax_Syntax.Reifiable 
                                                -> true
                                            | FStar_Syntax_Syntax.Reflectable
                                                uu____23196 -> true
                                            | uu____23197 -> false)
                                         qualifiers
                                        in
                                     let un_ts =
                                       ([], FStar_Syntax_Syntax.tun)  in
                                     let uu____23211 =
                                       let uu____23212 =
                                         let uu____23213 =
                                           lookup1 "return_wp"  in
                                         let uu____23214 = lookup1 "bind_wp"
                                            in
                                         let uu____23215 =
                                           lookup1 "if_then_else"  in
                                         let uu____23216 = lookup1 "ite_wp"
                                            in
                                         let uu____23217 = lookup1 "stronger"
                                            in
                                         let uu____23218 = lookup1 "close_wp"
                                            in
                                         let uu____23219 = lookup1 "assert_p"
                                            in
                                         let uu____23220 = lookup1 "assume_p"
                                            in
                                         let uu____23221 = lookup1 "null_wp"
                                            in
                                         let uu____23222 = lookup1 "trivial"
                                            in
                                         let uu____23223 =
                                           if rr
                                           then
                                             let uu____23224 = lookup1 "repr"
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.snd
                                               uu____23224
                                           else FStar_Syntax_Syntax.tun  in
                                         let uu____23240 =
                                           if rr
                                           then lookup1 "return"
                                           else un_ts  in
                                         let uu____23242 =
                                           if rr
                                           then lookup1 "bind"
                                           else un_ts  in
                                         let uu____23244 =
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
                                             uu____23213;
                                           FStar_Syntax_Syntax.bind_wp =
                                             uu____23214;
                                           FStar_Syntax_Syntax.if_then_else =
                                             uu____23215;
                                           FStar_Syntax_Syntax.ite_wp =
                                             uu____23216;
                                           FStar_Syntax_Syntax.stronger =
                                             uu____23217;
                                           FStar_Syntax_Syntax.close_wp =
                                             uu____23218;
                                           FStar_Syntax_Syntax.assert_p =
                                             uu____23219;
                                           FStar_Syntax_Syntax.assume_p =
                                             uu____23220;
                                           FStar_Syntax_Syntax.null_wp =
                                             uu____23221;
                                           FStar_Syntax_Syntax.trivial =
                                             uu____23222;
                                           FStar_Syntax_Syntax.repr =
                                             uu____23223;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____23240;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____23242;
                                           FStar_Syntax_Syntax.actions =
                                             actions1;
                                           FStar_Syntax_Syntax.eff_attrs =
                                             uu____23244
                                         }  in
                                       FStar_Syntax_Syntax.Sig_new_effect
                                         uu____23212
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         uu____23211;
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
                                          fun uu____23270  ->
                                            match uu____23270 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____23284 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____23284
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
                let uu____23308 = desugar_binders env1 eff_binders  in
                match uu____23308 with
                | (env2,binders) ->
                    let uu____23345 =
                      let uu____23356 = head_and_args defn  in
                      match uu____23356 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____23393 ->
                                let uu____23394 =
                                  let uu____23399 =
                                    let uu____23400 =
                                      let uu____23401 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.strcat uu____23401 " not found"
                                       in
                                    Prims.strcat "Effect " uu____23400  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____23399)
                                   in
                                FStar_Errors.raise_error uu____23394
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____23403 =
                            match FStar_List.rev args with
                            | (last_arg,uu____23433)::args_rev ->
                                let uu____23445 =
                                  let uu____23446 = unparen last_arg  in
                                  uu____23446.FStar_Parser_AST.tm  in
                                (match uu____23445 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____23474 -> ([], args))
                            | uu____23483 -> ([], args)  in
                          (match uu____23403 with
                           | (cattributes,args1) ->
                               let uu____23526 = desugar_args env2 args1  in
                               let uu____23527 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____23526, uu____23527))
                       in
                    (match uu____23345 with
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
                          (let uu____23563 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____23563 with
                           | (ed_binders,uu____23577,ed_binders_opening) ->
                               let sub1 uu____23590 =
                                 match uu____23590 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____23604 =
                                         FStar_Syntax_Subst.shift_subst
                                           (FStar_List.length us)
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____23604 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____23608 =
                                       let uu____23609 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____23609)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____23608
                                  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____23618 =
                                   let uu____23619 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____23619
                                    in
                                 let uu____23634 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____23635 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____23636 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____23637 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____23638 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____23639 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____23640 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____23641 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____23642 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____23643 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____23644 =
                                   let uu____23645 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____23645
                                    in
                                 let uu____23660 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____23661 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____23662 =
                                   FStar_List.map
                                     (fun action  ->
                                        let uu____23670 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____23671 =
                                          let uu____23672 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____23672
                                           in
                                        let uu____23687 =
                                          let uu____23688 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____23688
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____23670;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____23671;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____23687
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
                                     uu____23618;
                                   FStar_Syntax_Syntax.ret_wp = uu____23634;
                                   FStar_Syntax_Syntax.bind_wp = uu____23635;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____23636;
                                   FStar_Syntax_Syntax.ite_wp = uu____23637;
                                   FStar_Syntax_Syntax.stronger = uu____23638;
                                   FStar_Syntax_Syntax.close_wp = uu____23639;
                                   FStar_Syntax_Syntax.assert_p = uu____23640;
                                   FStar_Syntax_Syntax.assume_p = uu____23641;
                                   FStar_Syntax_Syntax.null_wp = uu____23642;
                                   FStar_Syntax_Syntax.trivial = uu____23643;
                                   FStar_Syntax_Syntax.repr = uu____23644;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____23660;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____23661;
                                   FStar_Syntax_Syntax.actions = uu____23662;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____23705 =
                                     let uu____23706 =
                                       let uu____23715 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____23715
                                        in
                                     FStar_List.length uu____23706  in
                                   uu____23705 = (Prims.parse_int "1")  in
                                 let uu____23746 =
                                   let uu____23749 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____23749 quals  in
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
                                   FStar_Syntax_Syntax.sigquals = uu____23746;
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
                                             let uu____23771 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____23771
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____23773 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____23773
                                 then
                                   let reflect_lid =
                                     let uu____23777 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____23777
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
    let uu____23787 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____23787 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.strcat "  " (Prims.strcat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____23838 ->
              let uu____23839 =
                let uu____23840 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____23840
                 in
              Prims.strcat "\n  " uu____23839
          | uu____23841 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____23854  ->
               match uu____23854 with
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
          let uu____23872 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____23872
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____23874 =
          let uu____23885 = FStar_Syntax_Syntax.as_arg arg  in [uu____23885]
           in
        FStar_Syntax_Util.mk_app fv uu____23874

and (desugar_decl_aux :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      let uu____23916 = desugar_decl_noattrs env d  in
      match uu____23916 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____23934 = mk_comment_attr d  in uu____23934 :: attrs1  in
          let uu____23935 =
            FStar_List.mapi
              (fun i  ->
                 fun sigelt  ->
                   if i = (Prims.parse_int "0")
                   then
                     let uu___299_23941 = sigelt  in
                     {
                       FStar_Syntax_Syntax.sigel =
                         (uu___299_23941.FStar_Syntax_Syntax.sigel);
                       FStar_Syntax_Syntax.sigrng =
                         (uu___299_23941.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___299_23941.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___299_23941.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs = attrs2
                     }
                   else
                     (let uu___300_23943 = sigelt  in
                      let uu____23944 =
                        FStar_List.filter
                          (fun at1  ->
                             let uu____23950 = get_fail_attr false at1  in
                             FStar_Option.isNone uu____23950) attrs2
                         in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___300_23943.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___300_23943.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___300_23943.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___300_23943.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs = uu____23944
                      })) sigelts
             in
          (env1, uu____23935)

and (desugar_decl :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      let uu____23971 = desugar_decl_aux env d  in
      match uu____23971 with
      | (env1,ses) ->
          let uu____23982 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____23982)

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
      | FStar_Parser_AST.Fsdoc uu____24010 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Friend lid ->
          let uu____24015 = FStar_Syntax_DsEnv.iface env  in
          if uu____24015
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____24025 =
               let uu____24026 =
                 let uu____24027 = FStar_Syntax_DsEnv.dep_graph env  in
                 let uu____24028 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Parser_Dep.module_has_interface uu____24027
                   uu____24028
                  in
               Prims.op_Negation uu____24026  in
             if uu____24025
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____24038 =
                  let uu____24039 =
                    let uu____24040 = FStar_Syntax_DsEnv.dep_graph env  in
                    FStar_Parser_Dep.module_has_interface uu____24040 lid  in
                  Prims.op_Negation uu____24039  in
                if uu____24038
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____24050 =
                     let uu____24051 =
                       let uu____24052 = FStar_Syntax_DsEnv.dep_graph env  in
                       FStar_Parser_Dep.deps_has_implementation uu____24052
                         lid
                        in
                     Prims.op_Negation uu____24051  in
                   if uu____24050
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____24066 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____24066, [])
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
              (fun uu____24111  ->
                 match uu____24111 with | (x,uu____24119) -> x) tcs
             in
          let uu____24124 =
            let uu____24129 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____24129 tcs1  in
          (match uu____24124 with
           | (env1,ses) ->
               let mkclass lid =
                 let uu____24146 =
                   let uu____24147 =
                     let uu____24154 =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun
                        in
                     FStar_Syntax_Syntax.mk_binder uu____24154  in
                   [uu____24147]  in
                 let uu____24167 =
                   let uu____24170 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____24173 =
                     let uu____24184 =
                       let uu____24193 =
                         let uu____24194 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____24194  in
                       FStar_Syntax_Syntax.as_arg uu____24193  in
                     [uu____24184]  in
                   FStar_Syntax_Util.mk_app uu____24170 uu____24173  in
                 FStar_Syntax_Util.abs uu____24146 uu____24167
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____24233,id1))::uu____24235 ->
                       FStar_Pervasives_Native.Some id1
                   | uu____24238::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____24242 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____24242 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id1 ->
                     let id2 = FStar_Syntax_Util.unmangle_field_name id1  in
                     let uu____24249 = FStar_Syntax_DsEnv.qualify env1 id2
                        in
                     [uu____24249]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____24270) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____24280,uu____24281,uu____24282,uu____24283,uu____24284)
                     ->
                     let uu____24293 =
                       let uu____24294 =
                         let uu____24295 =
                           let uu____24302 = mkclass lid  in
                           (meths, uu____24302)  in
                         FStar_Syntax_Syntax.Sig_splice uu____24295  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____24294;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = []
                       }  in
                     [uu____24293]
                 | uu____24305 -> []  in
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
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____24335;
                    FStar_Parser_AST.prange = uu____24336;_},uu____24337)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____24346;
                    FStar_Parser_AST.prange = uu____24347;_},uu____24348)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____24363;
                         FStar_Parser_AST.prange = uu____24364;_},uu____24365);
                    FStar_Parser_AST.prange = uu____24366;_},uu____24367)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____24388;
                         FStar_Parser_AST.prange = uu____24389;_},uu____24390);
                    FStar_Parser_AST.prange = uu____24391;_},uu____24392)::[]
                   -> false
               | (p,uu____24420)::[] ->
                   let uu____24429 = is_app_pattern p  in
                   Prims.op_Negation uu____24429
               | uu____24430 -> false)
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
            let uu____24503 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____24503 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____24515 =
                     let uu____24516 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____24516.FStar_Syntax_Syntax.n  in
                   match uu____24515 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____24526) ->
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
                         | uu____24559::uu____24560 ->
                             FStar_List.map
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____24563 ->
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.collect
                                  (fun uu___265_24578  ->
                                     match uu___265_24578 with
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inl uu____24581;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____24582;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____24583;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____24584;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____24585;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____24586;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____24587;_}
                                         -> []
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____24599;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____24600;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____24601;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____24602;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____24603;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____24604;_}
                                         ->
                                         FStar_Syntax_DsEnv.lookup_letbinding_quals
                                           env
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                          in
                       let quals2 =
                         let uu____24618 =
                           FStar_All.pipe_right lets1
                             (FStar_Util.for_some
                                (fun uu____24649  ->
                                   match uu____24649 with
                                   | (uu____24662,(uu____24663,t)) ->
                                       t.FStar_Parser_AST.level =
                                         FStar_Parser_AST.Formula))
                            in
                         if uu____24618
                         then FStar_Syntax_Syntax.Logic :: quals1
                         else quals1  in
                       let lbs1 =
                         let uu____24681 =
                           FStar_All.pipe_right quals2
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract)
                            in
                         if uu____24681
                         then
                           let uu____24684 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu___301_24698 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___302_24700 = fv  in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___302_24700.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___302_24700.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___301_24698.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___301_24698.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___301_24698.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___301_24698.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___301_24698.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___301_24698.FStar_Syntax_Syntax.lbpos)
                                     }))
                              in
                           ((FStar_Pervasives_Native.fst lbs), uu____24684)
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
                   | uu____24727 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____24733 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____24752 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____24733 with
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
                       let uu___303_24788 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___303_24788.FStar_Parser_AST.prange)
                       }
                   | uu____24795 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___304_24802 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___304_24802.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___304_24802.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___304_24802.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____24838 id1 =
                   match uu____24838 with
                   | (env1,ses) ->
                       let main =
                         let uu____24859 =
                           let uu____24860 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____24860  in
                         FStar_Parser_AST.mk_term uu____24859
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
                       let uu____24910 = desugar_decl env1 id_decl  in
                       (match uu____24910 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____24928 = gather_pattern_bound_vars true pat  in
                   FStar_All.pipe_right uu____24928 FStar_Util.set_elements
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
            let uu____24951 = close_fun env t  in
            desugar_term env uu____24951  in
          let quals1 =
            let uu____24955 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____24955
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let se =
            let uu____24961 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____24961;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in
          let env2 =
            FStar_Syntax_DsEnv.push_doc env1 lid d.FStar_Parser_AST.doc  in
          (env2, [se])
      | FStar_Parser_AST.Exception (id1,FStar_Pervasives_Native.None ) ->
          let uu____24969 =
            FStar_Syntax_DsEnv.fail_or env
              (FStar_Syntax_DsEnv.try_lookup_lid env)
              FStar_Parser_Const.exn_lid
             in
          (match uu____24969 with
           | (t,uu____24983) ->
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
            let uu____25013 =
              let uu____25022 = FStar_Syntax_Syntax.null_binder t  in
              [uu____25022]  in
            let uu____25041 =
              let uu____25044 =
                let uu____25045 =
                  FStar_Syntax_DsEnv.fail_or env
                    (FStar_Syntax_DsEnv.try_lookup_lid env)
                    FStar_Parser_Const.exn_lid
                   in
                FStar_Pervasives_Native.fst uu____25045  in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____25044
               in
            FStar_Syntax_Util.arrow uu____25013 uu____25041  in
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
            let uu____25106 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____25106 with
            | FStar_Pervasives_Native.None  ->
                let uu____25109 =
                  let uu____25114 =
                    let uu____25115 =
                      let uu____25116 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.strcat uu____25116 " not found"  in
                    Prims.strcat "Effect name " uu____25115  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____25114)  in
                FStar_Errors.raise_error uu____25109
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____25120 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____25138 =
                  let uu____25141 =
                    let uu____25142 = desugar_term env t  in
                    ([], uu____25142)  in
                  FStar_Pervasives_Native.Some uu____25141  in
                (uu____25138, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____25155 =
                  let uu____25158 =
                    let uu____25159 = desugar_term env wp  in
                    ([], uu____25159)  in
                  FStar_Pervasives_Native.Some uu____25158  in
                let uu____25166 =
                  let uu____25169 =
                    let uu____25170 = desugar_term env t  in
                    ([], uu____25170)  in
                  FStar_Pervasives_Native.Some uu____25169  in
                (uu____25155, uu____25166)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____25182 =
                  let uu____25185 =
                    let uu____25186 = desugar_term env t  in
                    ([], uu____25186)  in
                  FStar_Pervasives_Native.Some uu____25185  in
                (FStar_Pervasives_Native.None, uu____25182)
             in
          (match uu____25120 with
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
            let uu____25220 =
              let uu____25221 =
                let uu____25228 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____25228, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____25221  in
            {
              FStar_Syntax_Syntax.sigel = uu____25220;
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
      let uu____25254 =
        FStar_List.fold_left
          (fun uu____25274  ->
             fun d  ->
               match uu____25274 with
               | (env1,sigelts) ->
                   let uu____25294 = desugar_decl env1 d  in
                   (match uu____25294 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____25254 with
      | (env1,sigelts) ->
          let rec forward acc uu___267_25339 =
            match uu___267_25339 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____25353,FStar_Syntax_Syntax.Sig_let uu____25354) ->
                     let uu____25367 =
                       let uu____25370 =
                         let uu___305_25371 = se2  in
                         let uu____25372 =
                           let uu____25375 =
                             FStar_List.filter
                               (fun uu___266_25389  ->
                                  match uu___266_25389 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____25393;
                                           FStar_Syntax_Syntax.vars =
                                             uu____25394;_},uu____25395);
                                      FStar_Syntax_Syntax.pos = uu____25396;
                                      FStar_Syntax_Syntax.vars = uu____25397;_}
                                      when
                                      let uu____25424 =
                                        let uu____25425 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____25425
                                         in
                                      uu____25424 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____25426 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____25375
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___305_25371.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___305_25371.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___305_25371.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___305_25371.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____25372
                         }  in
                       uu____25370 :: se1 :: acc  in
                     forward uu____25367 sigelts1
                 | uu____25431 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____25439 = forward [] sigelts  in (env1, uu____25439)
  
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
          | (FStar_Pervasives_Native.None ,uu____25500) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____25504;
               FStar_Syntax_Syntax.exports = uu____25505;
               FStar_Syntax_Syntax.is_interface = uu____25506;_},FStar_Parser_AST.Module
             (current_lid,uu____25508)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____25516) ->
              let uu____25519 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____25519
           in
        let uu____25524 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____25560 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____25560, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____25577 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____25577, mname, decls, false)
           in
        match uu____25524 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____25607 = desugar_decls env2 decls  in
            (match uu____25607 with
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
          let uu____25669 =
            (FStar_Options.interactive ()) &&
              (let uu____25671 =
                 let uu____25672 =
                   let uu____25673 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____25673  in
                 FStar_Util.get_file_extension uu____25672  in
               FStar_List.mem uu____25671 ["fsti"; "fsi"])
             in
          if uu____25669 then as_interface m else m  in
        let uu____25677 = desugar_modul_common curmod env m1  in
        match uu____25677 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____25695 = FStar_Syntax_DsEnv.pop ()  in
              (uu____25695, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul ->
      (env_t,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun m  ->
      let uu____25715 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____25715 with
      | (env1,modul,pop_when_done) ->
          let uu____25729 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____25729 with
           | (env2,modul1) ->
               ((let uu____25741 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____25741
                 then
                   let uu____25742 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____25742
                 else ());
                (let uu____25744 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____25744, modul1))))
  
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
        (fun uu____25791  ->
           let uu____25792 = desugar_modul env modul  in
           match uu____25792 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____25833  ->
           let uu____25834 = desugar_decls env decls  in
           match uu____25834 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____25888  ->
             let uu____25889 = desugar_partial_modul modul env a_modul  in
             match uu____25889 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____25987 ->
                  let t =
                    let uu____25997 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____25997  in
                  let uu____26010 =
                    let uu____26011 = FStar_Syntax_Subst.compress t  in
                    uu____26011.FStar_Syntax_Syntax.n  in
                  (match uu____26010 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____26023,uu____26024)
                       -> bs1
                   | uu____26049 -> failwith "Impossible")
               in
            let uu____26058 =
              let uu____26065 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____26065
                FStar_Syntax_Syntax.t_unit
               in
            match uu____26058 with
            | (binders,uu____26067,binders_opening) ->
                let erase_term t =
                  let uu____26075 =
                    let uu____26076 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____26076  in
                  FStar_Syntax_Subst.close binders uu____26075  in
                let erase_tscheme uu____26094 =
                  match uu____26094 with
                  | (us,t) ->
                      let t1 =
                        let uu____26114 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____26114 t  in
                      let uu____26117 =
                        let uu____26118 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____26118  in
                      ([], uu____26117)
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
                    | uu____26141 ->
                        let bs =
                          let uu____26151 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____26151  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____26191 =
                          let uu____26192 =
                            let uu____26195 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____26195  in
                          uu____26192.FStar_Syntax_Syntax.n  in
                        (match uu____26191 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____26197,uu____26198) -> bs1
                         | uu____26223 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____26230 =
                      let uu____26231 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____26231  in
                    FStar_Syntax_Subst.close binders uu____26230  in
                  let uu___306_26232 = action  in
                  let uu____26233 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____26234 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___306_26232.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___306_26232.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____26233;
                    FStar_Syntax_Syntax.action_typ = uu____26234
                  }  in
                let uu___307_26235 = ed  in
                let uu____26236 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____26237 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____26238 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____26239 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____26240 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____26241 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____26242 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____26243 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____26244 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____26245 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____26246 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____26247 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____26248 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____26249 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____26250 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____26251 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___307_26235.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___307_26235.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____26236;
                  FStar_Syntax_Syntax.signature = uu____26237;
                  FStar_Syntax_Syntax.ret_wp = uu____26238;
                  FStar_Syntax_Syntax.bind_wp = uu____26239;
                  FStar_Syntax_Syntax.if_then_else = uu____26240;
                  FStar_Syntax_Syntax.ite_wp = uu____26241;
                  FStar_Syntax_Syntax.stronger = uu____26242;
                  FStar_Syntax_Syntax.close_wp = uu____26243;
                  FStar_Syntax_Syntax.assert_p = uu____26244;
                  FStar_Syntax_Syntax.assume_p = uu____26245;
                  FStar_Syntax_Syntax.null_wp = uu____26246;
                  FStar_Syntax_Syntax.trivial = uu____26247;
                  FStar_Syntax_Syntax.repr = uu____26248;
                  FStar_Syntax_Syntax.return_repr = uu____26249;
                  FStar_Syntax_Syntax.bind_repr = uu____26250;
                  FStar_Syntax_Syntax.actions = uu____26251;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___307_26235.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___308_26267 = se  in
                  let uu____26268 =
                    let uu____26269 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____26269  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____26268;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___308_26267.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___308_26267.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___308_26267.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___308_26267.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___309_26273 = se  in
                  let uu____26274 =
                    let uu____26275 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____26275
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____26274;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___309_26273.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___309_26273.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___309_26273.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___309_26273.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____26277 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____26278 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____26278 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____26290 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____26290
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____26292 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____26292)
  