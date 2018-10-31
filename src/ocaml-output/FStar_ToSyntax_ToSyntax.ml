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
      fun uu___246_241  ->
        match uu___246_241 with
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
  fun uu___247_261  ->
    match uu___247_261 with
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
  fun uu___248_279  ->
    match uu___248_279 with
    | FStar_Parser_AST.Hash  ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | uu____282 -> FStar_Pervasives_Native.None
  
let arg_withimp_e :
  'Auu____290 .
    FStar_Parser_AST.imp ->
      'Auu____290 ->
        ('Auu____290,FStar_Syntax_Syntax.arg_qualifier
                       FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2
  = fun imp  -> fun t  -> (t, (as_imp imp)) 
let arg_withimp_t :
  'Auu____316 .
    FStar_Parser_AST.imp ->
      'Auu____316 ->
        ('Auu____316,FStar_Syntax_Syntax.arg_qualifier
                       FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2
  =
  fun imp  ->
    fun t  ->
      match imp with
      | FStar_Parser_AST.Hash  ->
          (t, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag))
      | uu____335 -> (t, FStar_Pervasives_Native.None)
  
let (contains_binder : FStar_Parser_AST.binder Prims.list -> Prims.bool) =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b  ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____356 -> true
            | uu____362 -> false))
  
let rec (unparen : FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____371 -> t
  
let (tm_type_z : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____378 =
      let uu____379 = FStar_Ident.lid_of_path ["Type0"] r  in
      FStar_Parser_AST.Name uu____379  in
    FStar_Parser_AST.mk_term uu____378 r FStar_Parser_AST.Kind
  
let (tm_type : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____389 =
      let uu____390 = FStar_Ident.lid_of_path ["Type"] r  in
      FStar_Parser_AST.Name uu____390  in
    FStar_Parser_AST.mk_term uu____389 r FStar_Parser_AST.Kind
  
let rec (is_comp_type :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____406 =
        let uu____407 = unparen t  in uu____407.FStar_Parser_AST.tm  in
      match uu____406 with
      | FStar_Parser_AST.Name l ->
          let uu____410 = FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
          FStar_All.pipe_right uu____410 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l,uu____417) ->
          let uu____430 = FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
          FStar_All.pipe_right uu____430 FStar_Option.isSome
      | FStar_Parser_AST.App (head1,uu____437,uu____438) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,uu____443,uu____444) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____449,t1) -> is_comp_type env t1
      | uu____451 -> false
  
let (unit_ty : FStar_Parser_AST.term) =
  FStar_Parser_AST.mk_term
    (FStar_Parser_AST.Name FStar_Parser_Const.unit_lid)
    FStar_Range.dummyRange FStar_Parser_AST.Type_level
  
let (compile_op_lid :
  Prims.int -> Prims.string -> FStar_Range.range -> FStar_Ident.lident) =
  fun n1  ->
    fun s  ->
      fun r  ->
        let uu____474 =
          let uu____477 =
            let uu____478 =
              let uu____484 = FStar_Parser_AST.compile_op n1 s r  in
              (uu____484, r)  in
            FStar_Ident.mk_ident uu____478  in
          [uu____477]  in
        FStar_All.pipe_right uu____474 FStar_Ident.lid_of_ids
  
let op_as_term :
  'Auu____500 .
    FStar_Syntax_DsEnv.env ->
      Prims.int ->
        'Auu____500 ->
          FStar_Ident.ident ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun arity  ->
      fun rng  ->
        fun op  ->
          let r l dd =
            let uu____538 =
              let uu____539 =
                let uu____540 =
                  FStar_Ident.set_lid_range l op.FStar_Ident.idRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____540 dd
                  FStar_Pervasives_Native.None
                 in
              FStar_All.pipe_right uu____539 FStar_Syntax_Syntax.fv_to_tm  in
            FStar_Pervasives_Native.Some uu____538  in
          let fallback uu____548 =
            let uu____549 = FStar_Ident.text_of_id op  in
            match uu____549 with
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
                let uu____570 = FStar_Options.ml_ish ()  in
                if uu____570
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
            | uu____596 -> FStar_Pervasives_Native.None  in
          let uu____598 =
            let uu____601 =
              compile_op_lid arity op.FStar_Ident.idText
                op.FStar_Ident.idRange
               in
            FStar_Syntax_DsEnv.try_lookup_lid env uu____601  in
          match uu____598 with
          | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
          | uu____605 -> fallback ()
  
let (sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list)
  =
  fun ftv  ->
    let uu____620 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv
       in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____620
  
let rec (free_type_vars_b :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Syntax_DsEnv.env,FStar_Ident.ident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____669 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____673 = FStar_Syntax_DsEnv.push_bv env x  in
          (match uu____673 with | (env1,uu____685) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____688,term) ->
          let uu____690 = free_type_vars env term  in (env, uu____690)
      | FStar_Parser_AST.TAnnotated (id1,uu____696) ->
          let uu____697 = FStar_Syntax_DsEnv.push_bv env id1  in
          (match uu____697 with | (env1,uu____709) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____713 = free_type_vars env t  in (env, uu____713)

and (free_type_vars :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun t  ->
      let uu____720 =
        let uu____721 = unparen t  in uu____721.FStar_Parser_AST.tm  in
      match uu____720 with
      | FStar_Parser_AST.Labeled uu____724 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____737 = FStar_Syntax_DsEnv.try_lookup_id env a  in
          (match uu____737 with
           | FStar_Pervasives_Native.None  -> [a]
           | uu____742 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____745 -> []
      | FStar_Parser_AST.Uvar uu____746 -> []
      | FStar_Parser_AST.Var uu____747 -> []
      | FStar_Parser_AST.Projector uu____748 -> []
      | FStar_Parser_AST.Discrim uu____753 -> []
      | FStar_Parser_AST.Name uu____754 -> []
      | FStar_Parser_AST.Requires (t1,uu____756) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____764) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____771,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None  -> []
             | FStar_Pervasives_Native.Some t2 -> [t2])
             in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____790,ts) ->
          FStar_List.collect
            (fun uu____811  ->
               match uu____811 with | (t1,uu____819) -> free_type_vars env t1)
            ts
      | FStar_Parser_AST.Op (uu____820,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____828) ->
          let uu____829 = free_type_vars env t1  in
          let uu____832 = free_type_vars env t2  in
          FStar_List.append uu____829 uu____832
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____837 = free_type_vars_b env b  in
          (match uu____837 with
           | (env1,f) ->
               let uu____852 = free_type_vars env1 t1  in
               FStar_List.append f uu____852)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____869 =
            FStar_List.fold_left
              (fun uu____893  ->
                 fun bt  ->
                   match uu____893 with
                   | (env1,free) ->
                       let uu____917 =
                         match bt with
                         | FStar_Util.Inl binder ->
                             free_type_vars_b env1 binder
                         | FStar_Util.Inr t1 ->
                             let uu____932 = free_type_vars env1 body  in
                             (env1, uu____932)
                          in
                       (match uu____917 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____869 with
           | (env1,free) ->
               let uu____961 = free_type_vars env1 body  in
               FStar_List.append free uu____961)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____970 =
            FStar_List.fold_left
              (fun uu____990  ->
                 fun binder  ->
                   match uu____990 with
                   | (env1,free) ->
                       let uu____1010 = free_type_vars_b env1 binder  in
                       (match uu____1010 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____970 with
           | (env1,free) ->
               let uu____1041 = free_type_vars env1 body  in
               FStar_List.append free uu____1041)
      | FStar_Parser_AST.Project (t1,uu____1045) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.Abs uu____1049 -> []
      | FStar_Parser_AST.Let uu____1056 -> []
      | FStar_Parser_AST.LetOpen uu____1077 -> []
      | FStar_Parser_AST.If uu____1082 -> []
      | FStar_Parser_AST.QForall uu____1089 -> []
      | FStar_Parser_AST.QExists uu____1102 -> []
      | FStar_Parser_AST.Record uu____1115 -> []
      | FStar_Parser_AST.Match uu____1128 -> []
      | FStar_Parser_AST.TryWith uu____1143 -> []
      | FStar_Parser_AST.Bind uu____1158 -> []
      | FStar_Parser_AST.Quote uu____1165 -> []
      | FStar_Parser_AST.VQuote uu____1170 -> []
      | FStar_Parser_AST.Antiquote uu____1171 -> []
      | FStar_Parser_AST.Seq uu____1172 -> []

let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term,(FStar_Parser_AST.term,FStar_Parser_AST.imp)
                             FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let rec aux args t1 =
      let uu____1226 =
        let uu____1227 = unparen t1  in uu____1227.FStar_Parser_AST.tm  in
      match uu____1226 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____1269 -> (t1, args)  in
    aux [] t
  
let (close :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____1294 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1294  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1316 =
                     let uu____1317 =
                       let uu____1322 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____1322)  in
                     FStar_Parser_AST.TAnnotated uu____1317  in
                   FStar_Parser_AST.mk_binder uu____1316
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
        let uu____1340 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1340  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1362 =
                     let uu____1363 =
                       let uu____1368 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____1368)  in
                     FStar_Parser_AST.TAnnotated uu____1363  in
                   FStar_Parser_AST.mk_binder uu____1362
                     x.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____1370 =
             let uu____1371 = unparen t  in uu____1371.FStar_Parser_AST.tm
              in
           match uu____1370 with
           | FStar_Parser_AST.Product uu____1372 -> t
           | uu____1379 ->
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
      | uu____1416 -> (bs, t)
  
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild uu____1427 -> true
    | FStar_Parser_AST.PatTvar (uu____1431,uu____1432) -> true
    | FStar_Parser_AST.PatVar (uu____1438,uu____1439) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____1446) -> is_var_pattern p1
    | uu____1459 -> false
  
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____1470) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____1483;
           FStar_Parser_AST.prange = uu____1484;_},uu____1485)
        -> true
    | uu____1497 -> false
  
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
    | uu____1513 -> p
  
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
            let uu____1586 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____1586 with
             | (name,args,uu____1629) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1679);
               FStar_Parser_AST.prange = uu____1680;_},args)
            when is_top_level1 ->
            let uu____1690 =
              let uu____1695 = FStar_Syntax_DsEnv.qualify env id1  in
              FStar_Util.Inr uu____1695  in
            (uu____1690, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1717);
               FStar_Parser_AST.prange = uu____1718;_},args)
            -> ((FStar_Util.Inl id1), args, FStar_Pervasives_Native.None)
        | uu____1748 -> failwith "Not an app pattern"
  
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
        | FStar_Parser_AST.PatWild uu____1807 -> acc
        | FStar_Parser_AST.PatName uu____1810 -> acc
        | FStar_Parser_AST.PatOp uu____1811 -> acc
        | FStar_Parser_AST.PatConst uu____1812 ->
            if fail_on_patconst
            then
              FStar_Errors.raise_error
                (FStar_Errors.Error_CannotRedefineConst,
                  "Constants cannot be redefined") p.FStar_Parser_AST.prange
            else acc
        | FStar_Parser_AST.PatApp (phead,pats) ->
            gather_pattern_bound_vars_from_list (phead :: pats)
        | FStar_Parser_AST.PatTvar (x,uu____1829) -> FStar_Util.set_add x acc
        | FStar_Parser_AST.PatVar (x,uu____1835) -> FStar_Util.set_add x acc
        | FStar_Parser_AST.PatList pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatTuple (pats,uu____1844) ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatOr pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatRecord guarded_pats ->
            let uu____1861 =
              FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
            gather_pattern_bound_vars_from_list uu____1861
        | FStar_Parser_AST.PatAscribed (pat,uu____1869) ->
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
    match projectee with | LocalBinder _0 -> true | uu____1951 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____1993 -> false
  
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
  fun uu___249_2042  ->
    match uu___249_2042 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____2049 -> failwith "Impossible"
  
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
  fun uu____2084  ->
    match uu____2084 with
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
      let uu____2166 =
        let uu____2183 =
          let uu____2186 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____2186  in
        let uu____2187 =
          let uu____2198 =
            let uu____2207 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2207)  in
          [uu____2198]  in
        (uu____2183, uu____2187)  in
      FStar_Syntax_Syntax.Tm_app uu____2166  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____2256 =
        let uu____2273 =
          let uu____2276 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____2276  in
        let uu____2277 =
          let uu____2288 =
            let uu____2297 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2297)  in
          [uu____2288]  in
        (uu____2273, uu____2277)  in
      FStar_Syntax_Syntax.Tm_app uu____2256  in
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
          let uu____2360 =
            let uu____2377 =
              let uu____2380 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____2380  in
            let uu____2381 =
              let uu____2392 =
                let uu____2401 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____2401)  in
              let uu____2409 =
                let uu____2420 =
                  let uu____2429 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____2429)  in
                [uu____2420]  in
              uu____2392 :: uu____2409  in
            (uu____2377, uu____2381)  in
          FStar_Syntax_Syntax.Tm_app uu____2360  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let (generalize_annotated_univs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun s  ->
    let bs_univnames bs =
      let uu____2489 =
        let uu____2504 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____2523  ->
               match uu____2523 with
               | ({ FStar_Syntax_Syntax.ppname = uu____2534;
                    FStar_Syntax_Syntax.index = uu____2535;
                    FStar_Syntax_Syntax.sort = t;_},uu____2537)
                   ->
                   let uu____2545 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____2545) uu____2504
         in
      FStar_All.pipe_right bs uu____2489  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____2561 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____2579 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____2607 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____2628,uu____2629,bs,t,uu____2632,uu____2633)
                            ->
                            let uu____2642 = bs_univnames bs  in
                            let uu____2645 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____2642 uu____2645
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____2648,uu____2649,t,uu____2651,uu____2652,uu____2653)
                            -> FStar_Syntax_Free.univnames t
                        | uu____2660 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____2607 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___277_2669 = s  in
        let uu____2670 =
          let uu____2671 =
            let uu____2680 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____2698,bs,t,lids1,lids2) ->
                          let uu___278_2711 = se  in
                          let uu____2712 =
                            let uu____2713 =
                              let uu____2730 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____2731 =
                                let uu____2732 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____2732 t  in
                              (lid, uvs, uu____2730, uu____2731, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____2713
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____2712;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___278_2711.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___278_2711.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___278_2711.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___278_2711.FStar_Syntax_Syntax.sigattrs)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____2746,t,tlid,n1,lids1) ->
                          let uu___279_2757 = se  in
                          let uu____2758 =
                            let uu____2759 =
                              let uu____2775 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____2775, tlid, n1, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____2759  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____2758;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___279_2757.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___279_2757.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___279_2757.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___279_2757.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____2779 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____2680, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____2671  in
        {
          FStar_Syntax_Syntax.sigel = uu____2670;
          FStar_Syntax_Syntax.sigrng =
            (uu___277_2669.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___277_2669.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___277_2669.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___277_2669.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2786,t) ->
        let uvs =
          let uu____2789 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____2789 FStar_Util.set_elements  in
        let uu___280_2794 = s  in
        let uu____2795 =
          let uu____2796 =
            let uu____2803 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____2803)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____2796  in
        {
          FStar_Syntax_Syntax.sigel = uu____2795;
          FStar_Syntax_Syntax.sigrng =
            (uu___280_2794.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___280_2794.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___280_2794.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___280_2794.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____2827 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____2830 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____2837) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____2870,(FStar_Util.Inl t,uu____2872),uu____2873)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____2920,(FStar_Util.Inr c,uu____2922),uu____2923)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____2970 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____2971,(FStar_Util.Inl t,uu____2973),uu____2974) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____3021,(FStar_Util.Inr c,uu____3023),uu____3024) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____3071 -> empty_set  in
          FStar_Util.set_union uu____2827 uu____2830  in
        let all_lb_univs =
          let uu____3075 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____3091 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____3091) empty_set)
             in
          FStar_All.pipe_right uu____3075 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___281_3101 = s  in
        let uu____3102 =
          let uu____3103 =
            let uu____3110 =
              let uu____3111 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___282_3123 = lb  in
                        let uu____3124 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____3127 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___282_3123.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____3124;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___282_3123.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____3127;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___282_3123.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___282_3123.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____3111)  in
            (uu____3110, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____3103  in
        {
          FStar_Syntax_Syntax.sigel = uu____3102;
          FStar_Syntax_Syntax.sigrng =
            (uu___281_3101.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___281_3101.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___281_3101.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___281_3101.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____3136,fml) ->
        let uvs =
          let uu____3139 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____3139 FStar_Util.set_elements  in
        let uu___283_3144 = s  in
        let uu____3145 =
          let uu____3146 =
            let uu____3153 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____3153)  in
          FStar_Syntax_Syntax.Sig_assume uu____3146  in
        {
          FStar_Syntax_Syntax.sigel = uu____3145;
          FStar_Syntax_Syntax.sigrng =
            (uu___283_3144.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___283_3144.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___283_3144.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___283_3144.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____3155,bs,c,flags1) ->
        let uvs =
          let uu____3164 =
            let uu____3167 = bs_univnames bs  in
            let uu____3170 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____3167 uu____3170  in
          FStar_All.pipe_right uu____3164 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___284_3178 = s  in
        let uu____3179 =
          let uu____3180 =
            let uu____3193 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____3194 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____3193, uu____3194, flags1)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____3180  in
        {
          FStar_Syntax_Syntax.sigel = uu____3179;
          FStar_Syntax_Syntax.sigrng =
            (uu___284_3178.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___284_3178.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___284_3178.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___284_3178.FStar_Syntax_Syntax.sigattrs)
        }
    | uu____3197 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___250_3205  ->
    match uu___250_3205 with
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
    | uu____3256 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____3277 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____3277)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____3303 =
      let uu____3304 = unparen t  in uu____3304.FStar_Parser_AST.tm  in
    match uu____3303 with
    | FStar_Parser_AST.Wild  ->
        let uu____3310 =
          let uu____3311 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____3311  in
        FStar_Util.Inr uu____3310
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____3324)) ->
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
             let uu____3415 = sum_to_universe u n1  in
             FStar_Util.Inr uu____3415
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____3432 = sum_to_universe u n1  in
             FStar_Util.Inr uu____3432
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____3448 =
               let uu____3454 =
                 let uu____3456 = FStar_Parser_AST.term_to_string t  in
                 Prims.strcat
                   "This universe might contain a sum of two universe variables "
                   uu____3456
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____3454)
                in
             FStar_Errors.raise_error uu____3448 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____3465 ->
        let rec aux t1 univargs =
          let uu____3502 =
            let uu____3503 = unparen t1  in uu____3503.FStar_Parser_AST.tm
             in
          match uu____3502 with
          | FStar_Parser_AST.App (t2,targ,uu____3511) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___251_3538  ->
                     match uu___251_3538 with
                     | FStar_Util.Inr uu____3545 -> true
                     | uu____3548 -> false) univargs
              then
                let uu____3556 =
                  let uu____3557 =
                    FStar_List.map
                      (fun uu___252_3567  ->
                         match uu___252_3567 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____3557  in
                FStar_Util.Inr uu____3556
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___253_3593  ->
                        match uu___253_3593 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____3603 -> failwith "impossible")
                     univargs
                    in
                 let uu____3607 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____3607)
          | uu____3623 ->
              let uu____3624 =
                let uu____3630 =
                  let uu____3632 =
                    let uu____3634 = FStar_Parser_AST.term_to_string t1  in
                    Prims.strcat uu____3634 " in universe context"  in
                  Prims.strcat "Unexpected term " uu____3632  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3630)  in
              FStar_Errors.raise_error uu____3624 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____3649 ->
        let uu____3650 =
          let uu____3656 =
            let uu____3658 =
              let uu____3660 = FStar_Parser_AST.term_to_string t  in
              Prims.strcat uu____3660 " in universe context"  in
            Prims.strcat "Unexpected term " uu____3658  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3656)  in
        FStar_Errors.raise_error uu____3650 t.FStar_Parser_AST.range
  
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
                   FStar_Syntax_Syntax.antiquotes = uu____3701;_});
            FStar_Syntax_Syntax.pos = uu____3702;
            FStar_Syntax_Syntax.vars = uu____3703;_})::uu____3704
        ->
        let uu____3735 =
          let uu____3741 =
            let uu____3743 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____3743
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____3741)  in
        FStar_Errors.raise_error uu____3735 e.FStar_Syntax_Syntax.pos
    | (bv,e)::uu____3749 ->
        let uu____3768 =
          let uu____3774 =
            let uu____3776 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____3776
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____3774)  in
        FStar_Errors.raise_error uu____3768 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'Auu____3789 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident,'Auu____3789) FStar_Pervasives_Native.tuple2
        Prims.list -> FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____3817 = FStar_List.hd fields  in
        match uu____3817 with
        | (f,uu____3827) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____3839 =
                match uu____3839 with
                | (f',uu____3845) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____3847 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____3847
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
              (let uu____3857 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____3857);
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
          | FStar_Syntax_Syntax.Pat_dot_term uu____4249 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_wild uu____4256 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_constant uu____4257 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_var x ->
              FStar_Util.set_add x FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_cons (uu____4259,pats1) ->
              let aux out uu____4300 =
                match uu____4300 with
                | (p2,uu____4313) ->
                    let intersection =
                      let uu____4323 = pat_vars p2  in
                      FStar_Util.set_intersect uu____4323 out  in
                    let uu____4326 = FStar_Util.set_is_empty intersection  in
                    if uu____4326
                    then
                      let uu____4331 = pat_vars p2  in
                      FStar_Util.set_union out uu____4331
                    else
                      (let duplicate_bv =
                         let uu____4337 =
                           FStar_Util.set_elements intersection  in
                         FStar_List.hd uu____4337  in
                       let uu____4340 =
                         let uu____4346 =
                           FStar_Util.format1
                             "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                             (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                            in
                         (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                           uu____4346)
                          in
                       FStar_Errors.raise_error uu____4340 r)
                 in
              FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
           in
        match pats with
        | [] -> ()
        | p1::[] ->
            let uu____4370 = pat_vars p1  in
            FStar_All.pipe_right uu____4370 (fun a1  -> ())
        | p1::ps ->
            let pvars = pat_vars p1  in
            let aux p2 =
              let uu____4398 =
                let uu____4400 = pat_vars p2  in
                FStar_Util.set_eq pvars uu____4400  in
              if uu____4398
              then ()
              else
                (let nonlinear_vars =
                   let uu____4409 = pat_vars p2  in
                   FStar_Util.set_symmetric_difference pvars uu____4409  in
                 let first_nonlinear_var =
                   let uu____4413 = FStar_Util.set_elements nonlinear_vars
                      in
                   FStar_List.hd uu____4413  in
                 let uu____4416 =
                   let uu____4422 =
                     FStar_Util.format1
                       "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                       (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                      in
                   (FStar_Errors.Fatal_IncoherentPatterns, uu____4422)  in
                 FStar_Errors.raise_error uu____4416 r)
               in
            FStar_List.iter aux ps
         in
      let resolvex l e x =
        let uu____4450 =
          FStar_All.pipe_right l
            (FStar_Util.find_opt
               (fun y  ->
                  (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                    x.FStar_Ident.idText))
           in
        match uu____4450 with
        | FStar_Pervasives_Native.Some y -> (l, e, y)
        | uu____4467 ->
            let uu____4470 = FStar_Syntax_DsEnv.push_bv e x  in
            (match uu____4470 with | (e1,x1) -> ((x1 :: l), e1, x1))
         in
      let rec aux' top loc env1 p1 =
        let pos q = FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange
           in
        let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
        let orig = p1  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr uu____4621 -> failwith "impossible"
        | FStar_Parser_AST.PatOp op ->
            let uu____4645 =
              let uu____4646 =
                let uu____4647 =
                  let uu____4654 =
                    let uu____4655 =
                      let uu____4661 =
                        FStar_Parser_AST.compile_op (Prims.parse_int "0")
                          op.FStar_Ident.idText op.FStar_Ident.idRange
                         in
                      (uu____4661, (op.FStar_Ident.idRange))  in
                    FStar_Ident.mk_ident uu____4655  in
                  (uu____4654, FStar_Pervasives_Native.None)  in
                FStar_Parser_AST.PatVar uu____4647  in
              {
                FStar_Parser_AST.pat = uu____4646;
                FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
              }  in
            aux loc env1 uu____4645
        | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
            ((match tacopt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some uu____4681 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                      "Type ascriptions within patterns cannot be associated with a tactic")
                    orig.FStar_Parser_AST.prange);
             (let uu____4684 = aux loc env1 p2  in
              match uu____4684 with
              | (loc1,env',binder,p3,annots,imp) ->
                  let annot_pat_var p4 t1 =
                    match p4.FStar_Syntax_Syntax.v with
                    | FStar_Syntax_Syntax.Pat_var x ->
                        let uu___285_4773 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_var
                               (let uu___286_4778 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___286_4778.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___286_4778.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___285_4773.FStar_Syntax_Syntax.p)
                        }
                    | FStar_Syntax_Syntax.Pat_wild x ->
                        let uu___287_4780 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_wild
                               (let uu___288_4785 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___288_4785.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___288_4785.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___287_4780.FStar_Syntax_Syntax.p)
                        }
                    | uu____4786 when top -> p4
                    | uu____4787 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                            "Type ascriptions within patterns are only allowed on variables")
                          orig.FStar_Parser_AST.prange
                     in
                  let uu____4792 =
                    match binder with
                    | LetBinder uu____4813 -> failwith "impossible"
                    | LocalBinder (x,aq) ->
                        let t1 =
                          let uu____4838 = close_fun env1 t  in
                          desugar_term env1 uu____4838  in
                        let x1 =
                          let uu___289_4840 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___289_4840.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___289_4840.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t1
                          }  in
                        ([(x1, t1)], (LocalBinder (x1, aq)))
                     in
                  (match uu____4792 with
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
            let uu____4908 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
            (loc, env1, (LocalBinder (x, aq1)), uu____4908, [], imp)
        | FStar_Parser_AST.PatConst c ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                FStar_Syntax_Syntax.tun
               in
            let uu____4922 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____4922, [], false)
        | FStar_Parser_AST.PatTvar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____4946 = resolvex loc env1 x  in
            (match uu____4946 with
             | (loc1,env2,xbv) ->
                 let uu____4975 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____4975, [], imp))
        | FStar_Parser_AST.PatVar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____4998 = resolvex loc env1 x  in
            (match uu____4998 with
             | (loc1,env2,xbv) ->
                 let uu____5027 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____5027, [], imp))
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
            let uu____5042 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (l1, []))
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____5042, [], false)
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
               FStar_Parser_AST.prange = uu____5072;_},args)
            ->
            let uu____5078 =
              FStar_List.fold_right
                (fun arg  ->
                   fun uu____5139  ->
                     match uu____5139 with
                     | (loc1,env2,annots,args1) ->
                         let uu____5220 = aux loc1 env2 arg  in
                         (match uu____5220 with
                          | (loc2,env3,uu____5267,arg1,ans,imp) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((arg1, imp) :: args1)))) args
                (loc, env1, [], [])
               in
            (match uu____5078 with
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
                 let uu____5399 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____5399, annots, false))
        | FStar_Parser_AST.PatApp uu____5417 ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
              p1.FStar_Parser_AST.prange
        | FStar_Parser_AST.PatList pats ->
            let uu____5448 =
              FStar_List.fold_right
                (fun pat  ->
                   fun uu____5499  ->
                     match uu____5499 with
                     | (loc1,env2,annots,pats1) ->
                         let uu____5560 = aux loc1 env2 pat  in
                         (match uu____5560 with
                          | (loc2,env3,uu____5602,pat1,ans,uu____5605) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                (pat1 :: pats1)))) pats (loc, env1, [], [])
               in
            (match uu____5448 with
             | (loc1,env2,annots,pats1) ->
                 let pat =
                   let uu____5702 =
                     let uu____5705 =
                       let uu____5712 =
                         FStar_Range.end_range p1.FStar_Parser_AST.prange  in
                       pos_r uu____5712  in
                     let uu____5713 =
                       let uu____5714 =
                         let uu____5728 =
                           FStar_Syntax_Syntax.lid_as_fv
                             FStar_Parser_Const.nil_lid
                             FStar_Syntax_Syntax.delta_constant
                             (FStar_Pervasives_Native.Some
                                FStar_Syntax_Syntax.Data_ctor)
                            in
                         (uu____5728, [])  in
                       FStar_Syntax_Syntax.Pat_cons uu____5714  in
                     FStar_All.pipe_left uu____5705 uu____5713  in
                   FStar_List.fold_right
                     (fun hd1  ->
                        fun tl1  ->
                          let r =
                            FStar_Range.union_ranges
                              hd1.FStar_Syntax_Syntax.p
                              tl1.FStar_Syntax_Syntax.p
                             in
                          let uu____5762 =
                            let uu____5763 =
                              let uu____5777 =
                                FStar_Syntax_Syntax.lid_as_fv
                                  FStar_Parser_Const.cons_lid
                                  FStar_Syntax_Syntax.delta_constant
                                  (FStar_Pervasives_Native.Some
                                     FStar_Syntax_Syntax.Data_ctor)
                                 in
                              (uu____5777, [(hd1, false); (tl1, false)])  in
                            FStar_Syntax_Syntax.Pat_cons uu____5763  in
                          FStar_All.pipe_left (pos_r r) uu____5762) pats1
                     uu____5702
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
            let uu____5835 =
              FStar_List.fold_left
                (fun uu____5895  ->
                   fun p2  ->
                     match uu____5895 with
                     | (loc1,env2,annots,pats) ->
                         let uu____5977 = aux loc1 env2 p2  in
                         (match uu____5977 with
                          | (loc2,env3,uu____6024,pat,ans,uu____6027) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((pat, false) :: pats)))) (loc, env1, [], [])
                args
               in
            (match uu____5835 with
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
                   | uu____6193 -> failwith "impossible"  in
                 let x =
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some
                        (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun
                    in
                 let uu____6196 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____6196, annots, false))
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
                   (fun uu____6277  ->
                      match uu____6277 with
                      | (f,p2) -> ((f.FStar_Ident.ident), p2)))
               in
            let args =
              FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                (FStar_List.map
                   (fun uu____6307  ->
                      match uu____6307 with
                      | (f,uu____6313) ->
                          let uu____6314 =
                            FStar_All.pipe_right fields1
                              (FStar_List.tryFind
                                 (fun uu____6340  ->
                                    match uu____6340 with
                                    | (g,uu____6347) ->
                                        f.FStar_Ident.idText =
                                          g.FStar_Ident.idText))
                             in
                          (match uu____6314 with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatWild
                                    FStar_Pervasives_Native.None)
                                 p1.FStar_Parser_AST.prange
                           | FStar_Pervasives_Native.Some (uu____6353,p2) ->
                               p2)))
               in
            let app =
              let uu____6360 =
                let uu____6361 =
                  let uu____6368 =
                    let uu____6369 =
                      let uu____6370 =
                        FStar_Ident.lid_of_ids
                          (FStar_List.append
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                             [record.FStar_Syntax_DsEnv.constrname])
                         in
                      FStar_Parser_AST.PatName uu____6370  in
                    FStar_Parser_AST.mk_pattern uu____6369
                      p1.FStar_Parser_AST.prange
                     in
                  (uu____6368, args)  in
                FStar_Parser_AST.PatApp uu____6361  in
              FStar_Parser_AST.mk_pattern uu____6360
                p1.FStar_Parser_AST.prange
               in
            let uu____6373 = aux loc env1 app  in
            (match uu____6373 with
             | (env2,e,b,p2,annots,uu____6419) ->
                 let p3 =
                   match p2.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                       let uu____6459 =
                         let uu____6460 =
                           let uu____6474 =
                             let uu___290_6475 = fv  in
                             let uu____6476 =
                               let uu____6479 =
                                 let uu____6480 =
                                   let uu____6487 =
                                     FStar_All.pipe_right
                                       record.FStar_Syntax_DsEnv.fields
                                       (FStar_List.map
                                          FStar_Pervasives_Native.fst)
                                      in
                                   ((record.FStar_Syntax_DsEnv.typename),
                                     uu____6487)
                                    in
                                 FStar_Syntax_Syntax.Record_ctor uu____6480
                                  in
                               FStar_Pervasives_Native.Some uu____6479  in
                             {
                               FStar_Syntax_Syntax.fv_name =
                                 (uu___290_6475.FStar_Syntax_Syntax.fv_name);
                               FStar_Syntax_Syntax.fv_delta =
                                 (uu___290_6475.FStar_Syntax_Syntax.fv_delta);
                               FStar_Syntax_Syntax.fv_qual = uu____6476
                             }  in
                           (uu____6474, args1)  in
                         FStar_Syntax_Syntax.Pat_cons uu____6460  in
                       FStar_All.pipe_left pos uu____6459
                   | uu____6513 -> p2  in
                 (env2, e, b, p3, annots, false))
      
      and aux loc env1 p1 = aux' false loc env1 p1
       in
      let aux_maybe_or env1 p1 =
        let loc = []  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr [] -> failwith "impossible"
        | FStar_Parser_AST.PatOr (p2::ps) ->
            let uu____6599 = aux' true loc env1 p2  in
            (match uu____6599 with
             | (loc1,env2,var,p3,ans,uu____6643) ->
                 let uu____6658 =
                   FStar_List.fold_left
                     (fun uu____6707  ->
                        fun p4  ->
                          match uu____6707 with
                          | (loc2,env3,ps1) ->
                              let uu____6772 = aux' true loc2 env3 p4  in
                              (match uu____6772 with
                               | (loc3,env4,uu____6813,p5,ans1,uu____6816) ->
                                   (loc3, env4, ((p5, ans1) :: ps1))))
                     (loc1, env2, []) ps
                    in
                 (match uu____6658 with
                  | (loc2,env3,ps1) ->
                      let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                      (env3, var, pats)))
        | uu____6977 ->
            let uu____6978 = aux' true loc env1 p1  in
            (match uu____6978 with
             | (loc1,env2,vars,pat,ans,b) -> (env2, vars, [(pat, ans)]))
         in
      let uu____7075 = aux_maybe_or env p  in
      match uu____7075 with
      | (env1,b,pats) ->
          ((let uu____7130 = FStar_List.map FStar_Pervasives_Native.fst pats
               in
            check_linear_pattern_variables uu____7130
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
          let uu____7203 =
            let uu____7204 =
              let uu____7215 = FStar_Syntax_DsEnv.qualify env x  in
              (uu____7215, (ty, tacopt))  in
            LetBinder uu____7204  in
          (env, uu____7203, [])  in
        let op_to_ident x =
          let uu____7232 =
            let uu____7238 =
              FStar_Parser_AST.compile_op (Prims.parse_int "0")
                x.FStar_Ident.idText x.FStar_Ident.idRange
               in
            (uu____7238, (x.FStar_Ident.idRange))  in
          FStar_Ident.mk_ident uu____7232  in
        if top
        then
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu____7260 = op_to_ident x  in
              mklet uu____7260 FStar_Syntax_Syntax.tun
                FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x,uu____7262) ->
              mklet x FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu____7268;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7284 = op_to_ident x  in
              let uu____7285 = desugar_term env t  in
              mklet uu____7284 uu____7285 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____7287);
                 FStar_Parser_AST.prange = uu____7288;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7308 = desugar_term env t  in
              mklet x uu____7308 tacopt1
          | uu____7309 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu____7322 = desugar_data_pat env p  in
           match uu____7322 with
           | (env1,binder,p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu____7351;
                      FStar_Syntax_Syntax.p = uu____7352;_},uu____7353)::[]
                     -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu____7366;
                      FStar_Syntax_Syntax.p = uu____7367;_},uu____7368)::[]
                     -> []
                 | uu____7381 -> p1  in
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
  fun uu____7389  ->
    fun env  ->
      fun pat  ->
        let uu____7393 = desugar_data_pat env pat  in
        match uu____7393 with | (env1,uu____7409,pat1) -> (env1, pat1)

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
      let uu____7431 = desugar_term_aq env e  in
      match uu____7431 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____7450 = desugar_typ_aq env e  in
      match uu____7450 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness,FStar_Const.width)
        FStar_Pervasives_Native.tuple2 ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____7460  ->
        fun range  ->
          match uu____7460 with
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
              ((let uu____7482 =
                  let uu____7484 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____7484  in
                if uu____7482
                then
                  let uu____7487 =
                    let uu____7493 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____7493)  in
                  FStar_Errors.log_issue range uu____7487
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
                  let uu____7514 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____7514 range  in
                let lid1 =
                  let uu____7518 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____7518 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____7528 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____7528 range  in
                           let private_fv =
                             let uu____7530 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____7530 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___291_7531 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___291_7531.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___291_7531.FStar_Syntax_Syntax.vars)
                           }
                       | uu____7532 ->
                           failwith
                             (Prims.strcat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____7536 =
                        let uu____7542 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____7542)
                         in
                      FStar_Errors.raise_error uu____7536 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____7562 =
                  let uu____7569 =
                    let uu____7570 =
                      let uu____7587 =
                        let uu____7598 =
                          let uu____7607 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____7607)  in
                        [uu____7598]  in
                      (lid1, uu____7587)  in
                    FStar_Syntax_Syntax.Tm_app uu____7570  in
                  FStar_Syntax_Syntax.mk uu____7569  in
                uu____7562 FStar_Pervasives_Native.None range))

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
            let uu____7658 =
              let uu____7665 =
                (if resolve
                 then FStar_Syntax_DsEnv.try_lookup_lid_with_attributes
                 else
                   FStar_Syntax_DsEnv.try_lookup_lid_with_attributes_no_resolve)
                  env
                 in
              FStar_Syntax_DsEnv.fail_or env uu____7665 l  in
            match uu____7658 with
            | (tm,attrs) ->
                let warn_if_deprecated attrs1 =
                  FStar_List.iter
                    (fun a  ->
                       match a.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_app
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____7717;
                              FStar_Syntax_Syntax.vars = uu____7718;_},args)
                           when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____7746 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____7746 " is deprecated"  in
                           let msg1 =
                             if
                               (FStar_List.length args) >
                                 (Prims.parse_int "0")
                             then
                               let uu____7762 =
                                 let uu____7763 =
                                   let uu____7766 = FStar_List.hd args  in
                                   FStar_Pervasives_Native.fst uu____7766  in
                                 uu____7763.FStar_Syntax_Syntax.n  in
                               match uu____7762 with
                               | FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_string (s,uu____7789))
                                   when
                                   Prims.op_Negation
                                     ((FStar_Util.trim_string s) = "")
                                   ->
                                   Prims.strcat msg
                                     (Prims.strcat ", use "
                                        (Prims.strcat s " instead"))
                               | uu____7796 -> msg
                             else msg  in
                           let uu____7799 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____7799
                             (FStar_Errors.Warning_DeprecatedDefinition,
                               msg1)
                       | FStar_Syntax_Syntax.Tm_fvar fv when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____7804 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____7804 " is deprecated"  in
                           let uu____7807 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____7807
                             (FStar_Errors.Warning_DeprecatedDefinition, msg)
                       | uu____7809 -> ()) attrs1
                   in
                (warn_if_deprecated attrs; (let tm1 = setpos tm  in tm1))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____7824 =
          let uu____7825 = unparen t  in uu____7825.FStar_Parser_AST.tm  in
        match uu____7824 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____7826; FStar_Ident.ident = uu____7827;
              FStar_Ident.nsstr = uu____7828; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____7833 ->
            let uu____7834 =
              let uu____7840 =
                let uu____7842 = FStar_Parser_AST.term_to_string t  in
                Prims.strcat "Unknown attribute " uu____7842  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____7840)  in
            FStar_Errors.raise_error uu____7834 t.FStar_Parser_AST.range
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
          let uu___292_7929 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___292_7929.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___292_7929.FStar_Syntax_Syntax.vars)
          }  in
        let uu____7932 =
          let uu____7933 = unparen top  in uu____7933.FStar_Parser_AST.tm  in
        match uu____7932 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____7938 ->
            let uu____7947 = desugar_formula env top  in (uu____7947, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____7956 = desugar_formula env t  in (uu____7956, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____7965 = desugar_formula env t  in (uu____7965, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____7992 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____7992, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____7994 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____7994, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____8003 =
                let uu____8004 =
                  let uu____8011 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____8011, args)  in
                FStar_Parser_AST.Op uu____8004  in
              FStar_Parser_AST.mk_term uu____8003 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____8016 =
              let uu____8017 =
                let uu____8018 =
                  let uu____8025 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____8025, [e])  in
                FStar_Parser_AST.Op uu____8018  in
              FStar_Parser_AST.mk_term uu____8017 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____8016
        | FStar_Parser_AST.Op (op_star,lhs::rhs::[]) when
            (let uu____8037 = FStar_Ident.text_of_id op_star  in
             uu____8037 = "*") &&
              (let uu____8042 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____8042 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____8059;_},t1::t2::[])
                  when
                  let uu____8065 =
                    op_as_term env (Prims.parse_int "2")
                      top.FStar_Parser_AST.range op_star
                     in
                  FStar_All.pipe_right uu____8065 FStar_Option.isNone ->
                  let uu____8072 = flatten1 t1  in
                  FStar_List.append uu____8072 [t2]
              | uu____8075 -> [t]  in
            let terms = flatten1 lhs  in
            let t =
              let uu___293_8080 = top  in
              let uu____8081 =
                let uu____8082 =
                  let uu____8093 =
                    FStar_List.map (fun _0_1  -> FStar_Util.Inr _0_1) terms
                     in
                  (uu____8093, rhs)  in
                FStar_Parser_AST.Sum uu____8082  in
              {
                FStar_Parser_AST.tm = uu____8081;
                FStar_Parser_AST.range =
                  (uu___293_8080.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___293_8080.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env t
        | FStar_Parser_AST.Tvar a ->
            let uu____8111 =
              let uu____8112 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_All.pipe_left setpos uu____8112  in
            (uu____8111, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____8118 =
              let uu____8124 =
                let uu____8126 =
                  let uu____8128 = FStar_Ident.text_of_id u  in
                  Prims.strcat uu____8128 " in non-universe context"  in
                Prims.strcat "Unexpected universe variable " uu____8126  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____8124)  in
            FStar_Errors.raise_error uu____8118 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____8143 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____8143 with
             | FStar_Pervasives_Native.None  ->
                 let uu____8150 =
                   let uu____8156 =
                     let uu____8158 = FStar_Ident.text_of_id s  in
                     Prims.strcat "Unexpected or unbound operator: "
                       uu____8158
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____8156)
                    in
                 FStar_Errors.raise_error uu____8150
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let uu____8173 =
                     let uu____8198 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____8260 = desugar_term_aq env t  in
                               match uu____8260 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____8198 FStar_List.unzip  in
                   (match uu____8173 with
                    | (args1,aqs) ->
                        let uu____8393 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____8393, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____8410)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____8427 =
              let uu___294_8428 = top  in
              let uu____8429 =
                let uu____8430 =
                  let uu____8437 =
                    let uu___295_8438 = top  in
                    let uu____8439 =
                      let uu____8440 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8440  in
                    {
                      FStar_Parser_AST.tm = uu____8439;
                      FStar_Parser_AST.range =
                        (uu___295_8438.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___295_8438.FStar_Parser_AST.level)
                    }  in
                  (uu____8437, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8430  in
              {
                FStar_Parser_AST.tm = uu____8429;
                FStar_Parser_AST.range =
                  (uu___294_8428.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___294_8428.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8427
        | FStar_Parser_AST.Construct (n1,(a,uu____8448)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____8468 =
                let uu___296_8469 = top  in
                let uu____8470 =
                  let uu____8471 =
                    let uu____8478 =
                      let uu___297_8479 = top  in
                      let uu____8480 =
                        let uu____8481 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____8481  in
                      {
                        FStar_Parser_AST.tm = uu____8480;
                        FStar_Parser_AST.range =
                          (uu___297_8479.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___297_8479.FStar_Parser_AST.level)
                      }  in
                    (uu____8478, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____8471  in
                {
                  FStar_Parser_AST.tm = uu____8470;
                  FStar_Parser_AST.range =
                    (uu___296_8469.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___296_8469.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____8468))
        | FStar_Parser_AST.Construct (n1,(a,uu____8489)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____8506 =
              let uu___298_8507 = top  in
              let uu____8508 =
                let uu____8509 =
                  let uu____8516 =
                    let uu___299_8517 = top  in
                    let uu____8518 =
                      let uu____8519 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8519  in
                    {
                      FStar_Parser_AST.tm = uu____8518;
                      FStar_Parser_AST.range =
                        (uu___299_8517.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___299_8517.FStar_Parser_AST.level)
                    }  in
                  (uu____8516, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8509  in
              {
                FStar_Parser_AST.tm = uu____8508;
                FStar_Parser_AST.range =
                  (uu___298_8507.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___298_8507.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8506
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8525; FStar_Ident.ident = uu____8526;
              FStar_Ident.nsstr = uu____8527; FStar_Ident.str = "Type0";_}
            ->
            let uu____8532 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____8532, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8533; FStar_Ident.ident = uu____8534;
              FStar_Ident.nsstr = uu____8535; FStar_Ident.str = "Type";_}
            ->
            let uu____8540 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____8540, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____8541; FStar_Ident.ident = uu____8542;
               FStar_Ident.nsstr = uu____8543; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____8563 =
              let uu____8564 =
                let uu____8565 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____8565  in
              mk1 uu____8564  in
            (uu____8563, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8566; FStar_Ident.ident = uu____8567;
              FStar_Ident.nsstr = uu____8568; FStar_Ident.str = "Effect";_}
            ->
            let uu____8573 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____8573, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8574; FStar_Ident.ident = uu____8575;
              FStar_Ident.nsstr = uu____8576; FStar_Ident.str = "True";_}
            ->
            let uu____8581 =
              let uu____8582 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8582
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8581, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8583; FStar_Ident.ident = uu____8584;
              FStar_Ident.nsstr = uu____8585; FStar_Ident.str = "False";_}
            ->
            let uu____8590 =
              let uu____8591 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8591
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8590, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____8594;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____8597 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____8597 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____8606 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_constant_at_level
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None
                     in
                  (uu____8606, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____8608 =
                    let uu____8610 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____8610 txt
                     in
                  failwith uu____8608))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8619 = desugar_name mk1 setpos env true l  in
              (uu____8619, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8623 = desugar_name mk1 setpos env true l  in
              (uu____8623, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____8636 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____8636 with
                | FStar_Pervasives_Native.Some uu____8646 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____8654 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____8654 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____8672 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____8693 =
                    let uu____8694 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____8694  in
                  (uu____8693, noaqs)
              | uu____8695 ->
                  let uu____8703 =
                    let uu____8709 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____8709)  in
                  FStar_Errors.raise_error uu____8703
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____8719 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____8719 with
              | FStar_Pervasives_Native.None  ->
                  let uu____8726 =
                    let uu____8732 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____8732)
                     in
                  FStar_Errors.raise_error uu____8726
                    top.FStar_Parser_AST.range
              | uu____8740 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____8744 = desugar_name mk1 setpos env true lid'  in
                  (uu____8744, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8761 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____8761 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____8780 ->
                       let uu____8787 =
                         FStar_Util.take
                           (fun uu____8811  ->
                              match uu____8811 with
                              | (uu____8817,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____8787 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____8862 =
                              let uu____8887 =
                                FStar_List.map
                                  (fun uu____8930  ->
                                     match uu____8930 with
                                     | (t,imp) ->
                                         let uu____8947 =
                                           desugar_term_aq env t  in
                                         (match uu____8947 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____8887
                                FStar_List.unzip
                               in
                            (match uu____8862 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____9090 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____9090, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____9109 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____9109 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.strcat "Constructor "
                             (Prims.strcat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____9120 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.strcat "Effect "
                             (Prims.strcat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) when
            FStar_Util.for_all
              (fun uu___254_9148  ->
                 match uu___254_9148 with
                 | FStar_Util.Inr uu____9154 -> true
                 | uu____9156 -> false) binders
            ->
            let terms =
              let uu____9165 =
                FStar_All.pipe_right binders
                  (FStar_List.map
                     (fun uu___255_9182  ->
                        match uu___255_9182 with
                        | FStar_Util.Inr x -> x
                        | FStar_Util.Inl uu____9188 -> failwith "Impossible"))
                 in
              FStar_List.append uu____9165 [t]  in
            let uu____9190 =
              let uu____9215 =
                FStar_All.pipe_right terms
                  (FStar_List.map
                     (fun t1  ->
                        let uu____9272 = desugar_typ_aq env t1  in
                        match uu____9272 with
                        | (t',aq) ->
                            let uu____9283 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____9283, aq)))
                 in
              FStar_All.pipe_right uu____9215 FStar_List.unzip  in
            (match uu____9190 with
             | (targs,aqs) ->
                 let tup =
                   let uu____9393 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____9393
                    in
                 let uu____9402 =
                   mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                 (uu____9402, (join_aqs aqs)))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____9429 =
              let uu____9446 =
                let uu____9453 =
                  let uu____9460 =
                    FStar_All.pipe_left (fun _0_2  -> FStar_Util.Inl _0_2)
                      (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                         FStar_Pervasives_Native.None)
                     in
                  [uu____9460]  in
                FStar_List.append binders uu____9453  in
              FStar_List.fold_left
                (fun uu____9513  ->
                   fun b  ->
                     match uu____9513 with
                     | (env1,tparams,typs) ->
                         let uu____9574 =
                           match b with
                           | FStar_Util.Inl b1 -> desugar_binder env1 b1
                           | FStar_Util.Inr t1 ->
                               let uu____9589 = desugar_typ env1 t1  in
                               (FStar_Pervasives_Native.None, uu____9589)
                            in
                         (match uu____9574 with
                          | (xopt,t1) ->
                              let uu____9614 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____9623 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____9623)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____9614 with
                               | (env2,x) ->
                                   let uu____9643 =
                                     let uu____9646 =
                                       let uu____9649 =
                                         let uu____9650 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____9650
                                          in
                                       [uu____9649]  in
                                     FStar_List.append typs uu____9646  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___300_9676 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___300_9676.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___300_9676.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____9643)))) (env, [], []) uu____9446
               in
            (match uu____9429 with
             | (env1,uu____9704,targs) ->
                 let tup =
                   let uu____9727 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____9727
                    in
                 let uu____9728 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_app (tup, targs))
                    in
                 (uu____9728, noaqs))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____9747 = uncurry binders t  in
            (match uu____9747 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___256_9791 =
                   match uu___256_9791 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range true env1 t1
                          in
                       let uu____9808 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____9808
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____9832 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____9832 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____9865 = aux env [] bs  in (uu____9865, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____9874 = desugar_binder env b  in
            (match uu____9874 with
             | (FStar_Pervasives_Native.None ,uu____9885) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____9900 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____9900 with
                  | ((x,uu____9916),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____9929 =
                        let uu____9930 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____9930  in
                      (uu____9929, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let bvss =
              FStar_List.map (gather_pattern_bound_vars false) binders  in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set1::sets2 ->
                    let i = FStar_Util.set_intersect acc set1  in
                    let uu____10009 = FStar_Util.set_is_empty i  in
                    if uu____10009
                    then
                      let uu____10014 = FStar_Util.set_union acc set1  in
                      aux uu____10014 sets2
                    else
                      (let uu____10019 =
                         let uu____10020 = FStar_Util.set_elements i  in
                         FStar_List.hd uu____10020  in
                       FStar_Pervasives_Native.Some uu____10019)
                 in
              let uu____10023 = FStar_Syntax_Syntax.new_id_set ()  in
              aux uu____10023 sets  in
            ((let uu____10027 = check_disjoint bvss  in
              match uu____10027 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some id1 ->
                  let uu____10031 =
                    let uu____10037 =
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        id1.FStar_Ident.idText
                       in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____10037)
                     in
                  let uu____10041 = FStar_Ident.range_of_id id1  in
                  FStar_Errors.raise_error uu____10031 uu____10041);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern)
                 in
              let uu____10049 =
                FStar_List.fold_left
                  (fun uu____10069  ->
                     fun pat  ->
                       match uu____10069 with
                       | (env1,ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____10095,(t,FStar_Pervasives_Native.None
                                              ))
                                ->
                                let uu____10105 =
                                  let uu____10108 = free_type_vars env1 t  in
                                  FStar_List.append uu____10108 ftvs  in
                                (env1, uu____10105)
                            | FStar_Parser_AST.PatAscribed
                                (uu____10113,(t,FStar_Pervasives_Native.Some
                                              tac))
                                ->
                                let uu____10124 =
                                  let uu____10127 = free_type_vars env1 t  in
                                  let uu____10130 =
                                    let uu____10133 = free_type_vars env1 tac
                                       in
                                    FStar_List.append uu____10133 ftvs  in
                                  FStar_List.append uu____10127 uu____10130
                                   in
                                (env1, uu____10124)
                            | uu____10138 -> (env1, ftvs))) (env, [])
                  binders1
                 in
              match uu____10049 with
              | (uu____10147,ftv) ->
                  let ftv1 = sort_ftv ftv  in
                  let binders2 =
                    let uu____10159 =
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
                    FStar_List.append uu____10159 binders1  in
                  let rec aux env1 bs sc_pat_opt uu___257_10216 =
                    match uu___257_10216 with
                    | [] ->
                        let uu____10243 = desugar_term_aq env1 body  in
                        (match uu____10243 with
                         | (body1,aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc,pat) ->
                                   let body2 =
                                     let uu____10280 =
                                       let uu____10281 =
                                         FStar_Syntax_Syntax.pat_bvs pat  in
                                       FStar_All.pipe_right uu____10281
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder)
                                        in
                                     FStar_Syntax_Subst.close uu____10280
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
                             let uu____10350 =
                               let uu____10353 =
                                 no_annot_abs (FStar_List.rev bs) body2  in
                               setpos uu____10353  in
                             (uu____10350, aq))
                    | p::rest ->
                        let uu____10368 = desugar_binding_pat env1 p  in
                        (match uu____10368 with
                         | (env2,b,pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1,uu____10402)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____10417 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange
                                in
                             let uu____10426 =
                               match b with
                               | LetBinder uu____10467 ->
                                   failwith "Impossible"
                               | LocalBinder (x,aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None
                                        ,uu____10536) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.None ) ->
                                         let uu____10590 =
                                           let uu____10599 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____10599, p1)  in
                                         FStar_Pervasives_Native.Some
                                           uu____10590
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.Some
                                        (sc,p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____10661,uu____10662) ->
                                              let tup2 =
                                                let uu____10664 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.parse_int "2")
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10664
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10669 =
                                                  let uu____10676 =
                                                    let uu____10677 =
                                                      let uu____10694 =
                                                        mk1
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let uu____10697 =
                                                        let uu____10708 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let uu____10717 =
                                                          let uu____10728 =
                                                            let uu____10737 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____10737
                                                             in
                                                          [uu____10728]  in
                                                        uu____10708 ::
                                                          uu____10717
                                                         in
                                                      (uu____10694,
                                                        uu____10697)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____10677
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____10676
                                                   in
                                                uu____10669
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range
                                                 in
                                              let p2 =
                                                let uu____10788 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____10788
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____10839,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____10841,pats)) ->
                                              let tupn =
                                                let uu____10886 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    ((Prims.parse_int "1") +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10886
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10899 =
                                                  let uu____10900 =
                                                    let uu____10917 =
                                                      mk1
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____10920 =
                                                      let uu____10931 =
                                                        let uu____10942 =
                                                          let uu____10951 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____10951
                                                           in
                                                        [uu____10942]  in
                                                      FStar_List.append args
                                                        uu____10931
                                                       in
                                                    (uu____10917,
                                                      uu____10920)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____10900
                                                   in
                                                mk1 uu____10899  in
                                              let p2 =
                                                let uu____10999 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats [(p1, false)])))
                                                  uu____10999
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____11046 ->
                                              failwith "Impossible")
                                      in
                                   ((x, aq), sc_pat_opt1)
                                in
                             (match uu____10426 with
                              | (b1,sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest))
                     in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____11140,uu____11141,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____11163 =
                let uu____11164 = unparen e  in
                uu____11164.FStar_Parser_AST.tm  in
              match uu____11163 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____11174 ->
                  let uu____11175 = desugar_term_aq env e  in
                  (match uu____11175 with
                   | (head1,aq) ->
                       let uu____11188 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____11188, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____11195 ->
            let rec aux args aqs e =
              let uu____11272 =
                let uu____11273 = unparen e  in
                uu____11273.FStar_Parser_AST.tm  in
              match uu____11272 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____11291 = desugar_term_aq env t  in
                  (match uu____11291 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____11339 ->
                  let uu____11340 = desugar_term_aq env e  in
                  (match uu____11340 with
                   | (head1,aq) ->
                       let uu____11361 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____11361, (join_aqs (aq :: aqs))))
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
            let uu____11424 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____11424
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
            let uu____11476 = desugar_term_aq env t  in
            (match uu____11476 with
             | (tm,s) ->
                 let uu____11487 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____11487, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____11493 =
              let uu____11506 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____11506 then desugar_typ_aq else desugar_term_aq  in
            uu____11493 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____11565 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____11708  ->
                        match uu____11708 with
                        | (attr_opt,(p,def)) ->
                            let uu____11766 = is_app_pattern p  in
                            if uu____11766
                            then
                              let uu____11799 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____11799, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____11882 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____11882, def1)
                               | uu____11927 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____11965);
                                           FStar_Parser_AST.prange =
                                             uu____11966;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____12015 =
                                            let uu____12036 =
                                              let uu____12041 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____12041  in
                                            (uu____12036, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____12015, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____12133) ->
                                        if top_level
                                        then
                                          let uu____12169 =
                                            let uu____12190 =
                                              let uu____12195 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____12195  in
                                            (uu____12190, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____12169, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____12286 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____12319 =
                FStar_List.fold_left
                  (fun uu____12392  ->
                     fun uu____12393  ->
                       match (uu____12392, uu____12393) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____12501,uu____12502),uu____12503))
                           ->
                           let uu____12620 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____12646 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____12646 with
                                  | (env2,xx) ->
                                      let uu____12665 =
                                        let uu____12668 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____12668 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____12665))
                             | FStar_Util.Inr l ->
                                 let uu____12676 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (uu____12676, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____12620 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____12319 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____12824 =
                    match uu____12824 with
                    | (attrs_opt,(uu____12860,args,result_t),def) ->
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
                                let uu____12948 = is_comp_type env1 t  in
                                if uu____12948
                                then
                                  ((let uu____12952 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____12962 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____12962))
                                       in
                                    match uu____12952 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____12969 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____12972 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____12972))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____12969
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
                          | uu____12983 ->
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
                              let uu____12998 =
                                let uu____12999 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____12999
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____12998
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
                  let uu____13080 = desugar_term_aq env' body  in
                  (match uu____13080 with
                   | (body1,aq) ->
                       let uu____13093 =
                         let uu____13096 =
                           let uu____13097 =
                             let uu____13111 =
                               FStar_Syntax_Subst.close rec_bindings1 body1
                                in
                             ((is_rec, lbs1), uu____13111)  in
                           FStar_Syntax_Syntax.Tm_let uu____13097  in
                         FStar_All.pipe_left mk1 uu____13096  in
                       (uu____13093, aq))
               in
            let ds_non_rec attrs_opt pat t1 t2 =
              let attrs =
                match attrs_opt with
                | FStar_Pervasives_Native.None  -> []
                | FStar_Pervasives_Native.Some l ->
                    FStar_List.map (desugar_term env) l
                 in
              let t11 = desugar_term env t1  in
              let uu____13186 =
                desugar_binding_pat_maybe_top top_level env pat  in
              match uu____13186 with
              | (env1,binder,pat1) ->
                  let uu____13208 =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let uu____13234 = desugar_term_aq env1 t2  in
                        (match uu____13234 with
                         | (body1,aq) ->
                             let fv =
                               let uu____13248 =
                                 FStar_Syntax_Util.incr_delta_qualifier t11
                                  in
                               FStar_Syntax_Syntax.lid_as_fv l uu____13248
                                 FStar_Pervasives_Native.None
                                in
                             let uu____13249 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t11,
                                            (t11.FStar_Syntax_Syntax.pos))]),
                                      body1))
                                in
                             (uu____13249, aq))
                    | LocalBinder (x,uu____13282) ->
                        let uu____13283 = desugar_term_aq env1 t2  in
                        (match uu____13283 with
                         | (body1,aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | ({
                                    FStar_Syntax_Syntax.v =
                                      FStar_Syntax_Syntax.Pat_wild
                                      uu____13297;
                                    FStar_Syntax_Syntax.p = uu____13298;_},uu____13299)::[]
                                   -> body1
                               | uu____13312 ->
                                   let uu____13315 =
                                     let uu____13322 =
                                       let uu____13323 =
                                         let uu____13346 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         let uu____13349 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1
                                            in
                                         (uu____13346, uu____13349)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____13323
                                        in
                                     FStar_Syntax_Syntax.mk uu____13322  in
                                   uu____13315 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range
                                in
                             let uu____13389 =
                               let uu____13392 =
                                 let uu____13393 =
                                   let uu____13407 =
                                     let uu____13410 =
                                       let uu____13411 =
                                         FStar_Syntax_Syntax.mk_binder x  in
                                       [uu____13411]  in
                                     FStar_Syntax_Subst.close uu____13410
                                       body2
                                      in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t11,
                                           (t11.FStar_Syntax_Syntax.pos))]),
                                     uu____13407)
                                    in
                                 FStar_Syntax_Syntax.Tm_let uu____13393  in
                               FStar_All.pipe_left mk1 uu____13392  in
                             (uu____13389, aq))
                     in
                  (match uu____13208 with | (tm,aq) -> (tm, aq))
               in
            let uu____13473 = FStar_List.hd lbs  in
            (match uu____13473 with
             | (attrs,(head_pat,defn)) ->
                 let uu____13517 = is_rec || (is_app_pattern head_pat)  in
                 if uu____13517
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____13533 =
                let uu____13534 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____13534  in
              mk1 uu____13533  in
            let uu____13535 = desugar_term_aq env t1  in
            (match uu____13535 with
             | (t1',aq1) ->
                 let uu____13546 = desugar_term_aq env t2  in
                 (match uu____13546 with
                  | (t2',aq2) ->
                      let uu____13557 = desugar_term_aq env t3  in
                      (match uu____13557 with
                       | (t3',aq3) ->
                           let uu____13568 =
                             let uu____13569 =
                               let uu____13570 =
                                 let uu____13593 =
                                   let uu____13610 =
                                     let uu____13625 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t2.FStar_Parser_AST.range
                                        in
                                     (uu____13625,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____13639 =
                                     let uu____13656 =
                                       let uu____13671 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t3.FStar_Parser_AST.range
                                          in
                                       (uu____13671,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____13656]  in
                                   uu____13610 :: uu____13639  in
                                 (t1', uu____13593)  in
                               FStar_Syntax_Syntax.Tm_match uu____13570  in
                             mk1 uu____13569  in
                           (uu____13568, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____13867 =
              match uu____13867 with
              | (pat,wopt,b) ->
                  let uu____13889 = desugar_match_pat env pat  in
                  (match uu____13889 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____13920 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____13920
                          in
                       let uu____13925 = desugar_term_aq env1 b  in
                       (match uu____13925 with
                        | (b1,aq) ->
                            let uu____13938 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____13938, aq)))
               in
            let uu____13943 = desugar_term_aq env e  in
            (match uu____13943 with
             | (e1,aq) ->
                 let uu____13954 =
                   let uu____13985 =
                     let uu____14018 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____14018 FStar_List.unzip  in
                   FStar_All.pipe_right uu____13985
                     (fun uu____14148  ->
                        match uu____14148 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____13954 with
                  | (brs,aqs) ->
                      let uu____14367 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____14367, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____14401 =
              let uu____14422 = is_comp_type env t  in
              if uu____14422
              then
                let comp = desugar_comp t.FStar_Parser_AST.range true env t
                   in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____14477 = desugar_term_aq env t  in
                 match uu____14477 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____14401 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____14569 = desugar_term_aq env e  in
                 (match uu____14569 with
                  | (e1,aq) ->
                      let uu____14580 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____14580, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____14619,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____14662 = FStar_List.hd fields  in
              match uu____14662 with | (f,uu____14674) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____14720  ->
                        match uu____14720 with
                        | (g,uu____14727) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____14734,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____14748 =
                         let uu____14754 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____14754)
                          in
                       FStar_Errors.raise_error uu____14748
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
                  let uu____14765 =
                    let uu____14776 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____14807  ->
                              match uu____14807 with
                              | (f,uu____14817) ->
                                  let uu____14818 =
                                    let uu____14819 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____14819
                                     in
                                  (uu____14818, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____14776)  in
                  FStar_Parser_AST.Construct uu____14765
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____14837 =
                      let uu____14838 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____14838  in
                    FStar_Parser_AST.mk_term uu____14837
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____14840 =
                      let uu____14853 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____14883  ->
                                match uu____14883 with
                                | (f,uu____14893) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____14853)  in
                    FStar_Parser_AST.Record uu____14840  in
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
            let uu____14953 = desugar_term_aq env recterm1  in
            (match uu____14953 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____14969;
                         FStar_Syntax_Syntax.vars = uu____14970;_},args)
                      ->
                      let uu____14996 =
                        let uu____14997 =
                          let uu____14998 =
                            let uu____15015 =
                              let uu____15018 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____15019 =
                                let uu____15022 =
                                  let uu____15023 =
                                    let uu____15030 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____15030)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____15023
                                   in
                                FStar_Pervasives_Native.Some uu____15022  in
                              FStar_Syntax_Syntax.fvar uu____15018
                                FStar_Syntax_Syntax.delta_constant
                                uu____15019
                               in
                            (uu____15015, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____14998  in
                        FStar_All.pipe_left mk1 uu____14997  in
                      (uu____14996, s)
                  | uu____15059 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____15063 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____15063 with
              | (constrname,is_rec) ->
                  let uu____15082 = desugar_term_aq env e  in
                  (match uu____15082 with
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
                       let uu____15102 =
                         let uu____15103 =
                           let uu____15104 =
                             let uu____15121 =
                               let uu____15124 =
                                 let uu____15125 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____15125
                                  in
                               FStar_Syntax_Syntax.fvar uu____15124
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1")) qual
                                in
                             let uu____15127 =
                               let uu____15138 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____15138]  in
                             (uu____15121, uu____15127)  in
                           FStar_Syntax_Syntax.Tm_app uu____15104  in
                         FStar_All.pipe_left mk1 uu____15103  in
                       (uu____15102, s))))
        | FStar_Parser_AST.NamedTyp (uu____15175,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____15185 =
              let uu____15186 = FStar_Syntax_Subst.compress tm  in
              uu____15186.FStar_Syntax_Syntax.n  in
            (match uu____15185 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____15194 =
                   let uu___301_15195 =
                     let uu____15196 =
                       let uu____15198 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____15198  in
                     FStar_Syntax_Util.exp_string uu____15196  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___301_15195.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___301_15195.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____15194, noaqs)
             | uu____15199 ->
                 let uu____15200 =
                   let uu____15206 =
                     let uu____15208 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.strcat "VQuote, expected an fvar, got: "
                       uu____15208
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____15206)  in
                 FStar_Errors.raise_error uu____15200
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____15217 = desugar_term_aq env e  in
            (match uu____15217 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____15229 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____15229, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____15234 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____15235 =
              let uu____15236 =
                let uu____15243 = desugar_term env e  in (bv, uu____15243)
                 in
              [uu____15236]  in
            (uu____15234, uu____15235)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____15268 =
              let uu____15269 =
                let uu____15270 =
                  let uu____15277 = desugar_term env e  in (uu____15277, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____15270  in
              FStar_All.pipe_left mk1 uu____15269  in
            (uu____15268, noaqs)
        | uu____15282 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____15283 = desugar_formula env top  in
            (uu____15283, noaqs)
        | uu____15284 ->
            let uu____15285 =
              let uu____15291 =
                let uu____15293 = FStar_Parser_AST.term_to_string top  in
                Prims.strcat "Unexpected term: " uu____15293  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____15291)  in
            FStar_Errors.raise_error uu____15285 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____15303 -> false
    | uu____15313 -> true

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
           (fun uu____15351  ->
              match uu____15351 with
              | (a,imp) ->
                  let uu____15364 = desugar_term env a  in
                  arg_withimp_e imp uu____15364))

and (desugar_comp :
  FStar_Range.range ->
    Prims.bool ->
      FStar_Syntax_DsEnv.env ->
        FStar_Parser_AST.term ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun r  ->
    fun allow_type_promotion  ->
      fun env  ->
        fun t  ->
          let fail1 err = FStar_Errors.raise_error err r  in
          let is_requires uu____15401 =
            match uu____15401 with
            | (t1,uu____15408) ->
                let uu____15409 =
                  let uu____15410 = unparen t1  in
                  uu____15410.FStar_Parser_AST.tm  in
                (match uu____15409 with
                 | FStar_Parser_AST.Requires uu____15412 -> true
                 | uu____15421 -> false)
             in
          let is_ensures uu____15433 =
            match uu____15433 with
            | (t1,uu____15440) ->
                let uu____15441 =
                  let uu____15442 = unparen t1  in
                  uu____15442.FStar_Parser_AST.tm  in
                (match uu____15441 with
                 | FStar_Parser_AST.Ensures uu____15444 -> true
                 | uu____15453 -> false)
             in
          let is_app head1 uu____15471 =
            match uu____15471 with
            | (t1,uu____15479) ->
                let uu____15480 =
                  let uu____15481 = unparen t1  in
                  uu____15481.FStar_Parser_AST.tm  in
                (match uu____15480 with
                 | FStar_Parser_AST.App
                     ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                        FStar_Parser_AST.range = uu____15484;
                        FStar_Parser_AST.level = uu____15485;_},uu____15486,uu____15487)
                     -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
                 | uu____15489 -> false)
             in
          let is_smt_pat uu____15501 =
            match uu____15501 with
            | (t1,uu____15508) ->
                let uu____15509 =
                  let uu____15510 = unparen t1  in
                  uu____15510.FStar_Parser_AST.tm  in
                (match uu____15509 with
                 | FStar_Parser_AST.Construct
                     (cons1,({
                               FStar_Parser_AST.tm =
                                 FStar_Parser_AST.Construct
                                 (smtpat,uu____15514);
                               FStar_Parser_AST.range = uu____15515;
                               FStar_Parser_AST.level = uu____15516;_},uu____15517)::uu____15518::[])
                     ->
                     (FStar_Ident.lid_equals cons1
                        FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  -> smtpat.FStar_Ident.str = s)
                          ["SMTPat"; "SMTPatT"; "SMTPatOr"])
                 | FStar_Parser_AST.Construct
                     (cons1,({
                               FStar_Parser_AST.tm = FStar_Parser_AST.Var
                                 smtpat;
                               FStar_Parser_AST.range = uu____15567;
                               FStar_Parser_AST.level = uu____15568;_},uu____15569)::uu____15570::[])
                     ->
                     (FStar_Ident.lid_equals cons1
                        FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  -> smtpat.FStar_Ident.str = s)
                          ["smt_pat"; "smt_pat_or"])
                 | uu____15603 -> false)
             in
          let is_decreases = is_app "decreases"  in
          let pre_process_comp_typ t1 =
            let uu____15638 = head_and_args t1  in
            match uu____15638 with
            | (head1,args) ->
                (match head1.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Name lemma when
                     (lemma.FStar_Ident.ident).FStar_Ident.idText = "Lemma"
                     ->
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
                       ((FStar_Parser_AST.mk_term req
                           t1.FStar_Parser_AST.range
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
                     let thunk_ens uu____15740 =
                       match uu____15740 with
                       | (e,i) ->
                           let uu____15751 = thunk_ens_ e  in
                           (uu____15751, i)
                        in
                     let fail_lemma uu____15763 =
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
                       let msg = FStar_String.concat "\n\t" expected_one_of
                          in
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
                           let uu____15869 =
                             let uu____15876 =
                               let uu____15883 = thunk_ens ens  in
                               [uu____15883; nil_pat]  in
                             req_true :: uu____15876  in
                           unit_tm :: uu____15869
                       | req::ens::[] when
                           (is_requires req) && (is_ensures ens) ->
                           let uu____15930 =
                             let uu____15937 =
                               let uu____15944 = thunk_ens ens  in
                               [uu____15944; nil_pat]  in
                             req :: uu____15937  in
                           unit_tm :: uu____15930
                       | ens::smtpat::[] when
                           (((let uu____15993 = is_requires ens  in
                              Prims.op_Negation uu____15993) &&
                               (let uu____15996 = is_smt_pat ens  in
                                Prims.op_Negation uu____15996))
                              &&
                              (let uu____15999 = is_decreases ens  in
                               Prims.op_Negation uu____15999))
                             && (is_smt_pat smtpat)
                           ->
                           let uu____16001 =
                             let uu____16008 =
                               let uu____16015 = thunk_ens ens  in
                               [uu____16015; smtpat]  in
                             req_true :: uu____16008  in
                           unit_tm :: uu____16001
                       | ens::dec::[] when
                           (is_ensures ens) && (is_decreases dec) ->
                           let uu____16062 =
                             let uu____16069 =
                               let uu____16076 = thunk_ens ens  in
                               [uu____16076; nil_pat; dec]  in
                             req_true :: uu____16069  in
                           unit_tm :: uu____16062
                       | ens::dec::smtpat::[] when
                           ((is_ensures ens) && (is_decreases dec)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____16136 =
                             let uu____16143 =
                               let uu____16150 = thunk_ens ens  in
                               [uu____16150; smtpat; dec]  in
                             req_true :: uu____16143  in
                           unit_tm :: uu____16136
                       | req::ens::dec::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_decreases dec)
                           ->
                           let uu____16210 =
                             let uu____16217 =
                               let uu____16224 = thunk_ens ens  in
                               [uu____16224; nil_pat; dec]  in
                             req :: uu____16217  in
                           unit_tm :: uu____16210
                       | req::ens::smtpat::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____16284 =
                             let uu____16291 =
                               let uu____16298 = thunk_ens ens  in
                               [uu____16298; smtpat]  in
                             req :: uu____16291  in
                           unit_tm :: uu____16284
                       | req::ens::dec::smtpat::[] when
                           (((is_requires req) && (is_ensures ens)) &&
                              (is_smt_pat smtpat))
                             && (is_decreases dec)
                           ->
                           let uu____16363 =
                             let uu____16370 =
                               let uu____16377 = thunk_ens ens  in
                               [uu____16377; dec; smtpat]  in
                             req :: uu____16370  in
                           unit_tm :: uu____16363
                       | _other -> fail_lemma ()  in
                     let head_and_attributes =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) lemma
                        in
                     (head_and_attributes, args1)
                 | FStar_Parser_AST.Name l when
                     FStar_Syntax_DsEnv.is_effect_name env l ->
                     let uu____16439 =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) l
                        in
                     (uu____16439, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____16467 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____16467
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                     ->
                     let uu____16470 =
                       let uu____16477 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____16477, [])  in
                     (uu____16470, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____16495 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____16495
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                     ->
                     let uu____16498 =
                       let uu____16505 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_GTot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____16505, [])  in
                     (uu____16498, args)
                 | FStar_Parser_AST.Name l when
                     (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                        ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                       ||
                       ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                     ->
                     let uu____16527 =
                       let uu____16534 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____16534, [])  in
                     (uu____16527, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____16557 when allow_type_promotion ->
                     let default_effect =
                       let uu____16559 = FStar_Options.ml_ish ()  in
                       if uu____16559
                       then FStar_Parser_Const.effect_ML_lid
                       else
                         ((let uu____16565 =
                             FStar_Options.warn_default_effects ()  in
                           if uu____16565
                           then
                             FStar_Errors.log_issue
                               head1.FStar_Parser_AST.range
                               (FStar_Errors.Warning_UseDefaultEffect,
                                 "Using default effect Tot")
                           else ());
                          FStar_Parser_Const.effect_Tot_lid)
                        in
                     let uu____16572 =
                       let uu____16579 =
                         FStar_Ident.set_lid_range default_effect
                           head1.FStar_Parser_AST.range
                          in
                       (uu____16579, [])  in
                     (uu____16572, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____16602 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_EffectNotFound,
                         "Expected an effect constructor")
                       t1.FStar_Parser_AST.range)
             in
          let uu____16621 = pre_process_comp_typ t  in
          match uu____16621 with
          | ((eff,cattributes),args) ->
              (if (FStar_List.length args) = (Prims.parse_int "0")
               then
                 (let uu____16673 =
                    let uu____16679 =
                      let uu____16681 = FStar_Syntax_Print.lid_to_string eff
                         in
                      FStar_Util.format1 "Not enough args to effect %s"
                        uu____16681
                       in
                    (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____16679)
                     in
                  fail1 uu____16673)
               else ();
               (let is_universe uu____16697 =
                  match uu____16697 with
                  | (uu____16703,imp) -> imp = FStar_Parser_AST.UnivApp  in
                let uu____16705 = FStar_Util.take is_universe args  in
                match uu____16705 with
                | (universes,args1) ->
                    let universes1 =
                      FStar_List.map
                        (fun uu____16764  ->
                           match uu____16764 with
                           | (u,imp) -> desugar_universe u) universes
                       in
                    let uu____16771 =
                      let uu____16786 = FStar_List.hd args1  in
                      let uu____16795 = FStar_List.tl args1  in
                      (uu____16786, uu____16795)  in
                    (match uu____16771 with
                     | (result_arg,rest) ->
                         let result_typ =
                           desugar_typ env
                             (FStar_Pervasives_Native.fst result_arg)
                            in
                         let rest1 = desugar_args env rest  in
                         let uu____16850 =
                           let is_decrease uu____16889 =
                             match uu____16889 with
                             | (t1,uu____16900) ->
                                 (match t1.FStar_Syntax_Syntax.n with
                                  | FStar_Syntax_Syntax.Tm_app
                                      ({
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_fvar fv;
                                         FStar_Syntax_Syntax.pos =
                                           uu____16911;
                                         FStar_Syntax_Syntax.vars =
                                           uu____16912;_},uu____16913::[])
                                      ->
                                      FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Parser_Const.decreases_lid
                                  | uu____16952 -> false)
                              in
                           FStar_All.pipe_right rest1
                             (FStar_List.partition is_decrease)
                            in
                         (match uu____16850 with
                          | (dec,rest2) ->
                              let decreases_clause =
                                FStar_All.pipe_right dec
                                  (FStar_List.map
                                     (fun uu____17069  ->
                                        match uu____17069 with
                                        | (t1,uu____17079) ->
                                            (match t1.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____17088,(arg,uu____17090)::[])
                                                 ->
                                                 FStar_Syntax_Syntax.DECREASES
                                                   arg
                                             | uu____17129 ->
                                                 failwith "impos")))
                                 in
                              let no_additional_args =
                                let is_empty l =
                                  match l with
                                  | [] -> true
                                  | uu____17150 -> false  in
                                (((is_empty decreases_clause) &&
                                    (is_empty rest2))
                                   && (is_empty cattributes))
                                  && (is_empty universes1)
                                 in
                              let uu____17162 =
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_Tot_lid)
                                 in
                              if uu____17162
                              then FStar_Syntax_Syntax.mk_Total result_typ
                              else
                                (let uu____17169 =
                                   no_additional_args &&
                                     (FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_GTot_lid)
                                    in
                                 if uu____17169
                                 then
                                   FStar_Syntax_Syntax.mk_GTotal result_typ
                                 else
                                   (let flags1 =
                                      let uu____17179 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____17179
                                      then [FStar_Syntax_Syntax.LEMMA]
                                      else
                                        (let uu____17186 =
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_Tot_lid
                                            in
                                         if uu____17186
                                         then [FStar_Syntax_Syntax.TOTAL]
                                         else
                                           (let uu____17193 =
                                              FStar_Ident.lid_equals eff
                                                FStar_Parser_Const.effect_ML_lid
                                               in
                                            if uu____17193
                                            then
                                              [FStar_Syntax_Syntax.MLEFFECT]
                                            else
                                              (let uu____17200 =
                                                 FStar_Ident.lid_equals eff
                                                   FStar_Parser_Const.effect_GTot_lid
                                                  in
                                               if uu____17200
                                               then
                                                 [FStar_Syntax_Syntax.SOMETRIVIAL]
                                               else [])))
                                       in
                                    let flags2 =
                                      FStar_List.append flags1 cattributes
                                       in
                                    let rest3 =
                                      let uu____17221 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____17221
                                      then
                                        match rest2 with
                                        | req::ens::(pat,aq)::[] ->
                                            let pat1 =
                                              match pat.FStar_Syntax_Syntax.n
                                              with
                                              | FStar_Syntax_Syntax.Tm_fvar
                                                  fv when
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
                                                    let uu____17312 =
                                                      FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.fvar
                                                      uu____17312
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
                                              | uu____17333 -> pat  in
                                            let uu____17334 =
                                              let uu____17345 =
                                                let uu____17356 =
                                                  let uu____17365 =
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (pat1,
                                                           (FStar_Syntax_Syntax.Meta_desugared
                                                              FStar_Syntax_Syntax.Meta_smt_pat)))
                                                      FStar_Pervasives_Native.None
                                                      pat1.FStar_Syntax_Syntax.pos
                                                     in
                                                  (uu____17365, aq)  in
                                                [uu____17356]  in
                                              ens :: uu____17345  in
                                            req :: uu____17334
                                        | uu____17406 -> rest2
                                      else rest2  in
                                    FStar_Syntax_Syntax.mk_Comp
                                      {
                                        FStar_Syntax_Syntax.comp_univs =
                                          universes1;
                                        FStar_Syntax_Syntax.effect_name = eff;
                                        FStar_Syntax_Syntax.result_typ =
                                          result_typ;
                                        FStar_Syntax_Syntax.effect_args =
                                          rest3;
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
        | uu____17438 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___302_17460 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___302_17460.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___302_17460.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___303_17502 = b  in
             {
               FStar_Parser_AST.b = (uu___303_17502.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___303_17502.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___303_17502.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____17565 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____17565)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____17578 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____17578 with
             | (env1,a1) ->
                 let a2 =
                   let uu___304_17588 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___304_17588.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___304_17588.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____17614 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____17628 =
                     let uu____17631 =
                       let uu____17632 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____17632]  in
                     no_annot_abs uu____17631 body2  in
                   FStar_All.pipe_left setpos uu____17628  in
                 let uu____17653 =
                   let uu____17654 =
                     let uu____17671 =
                       let uu____17674 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____17674
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____17676 =
                       let uu____17687 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____17687]  in
                     (uu____17671, uu____17676)  in
                   FStar_Syntax_Syntax.Tm_app uu____17654  in
                 FStar_All.pipe_left mk1 uu____17653)
        | uu____17726 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____17807 = q (rest, pats, body)  in
              let uu____17814 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____17807 uu____17814
                FStar_Parser_AST.Formula
               in
            let uu____17815 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____17815 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____17824 -> failwith "impossible"  in
      let uu____17828 =
        let uu____17829 = unparen f  in uu____17829.FStar_Parser_AST.tm  in
      match uu____17828 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____17842,uu____17843) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____17855,uu____17856) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____17888 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____17888
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____17924 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____17924
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____17968 -> desugar_term env f

and (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env,(FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
                                FStar_Pervasives_Native.tuple2 Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bs  ->
      let uu____17973 =
        FStar_List.fold_left
          (fun uu____18006  ->
             fun b  ->
               match uu____18006 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___305_18050 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___305_18050.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___305_18050.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___305_18050.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____18065 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____18065 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___306_18083 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___306_18083.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___306_18083.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____18084 =
                               let uu____18091 =
                                 let uu____18096 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____18096)  in
                               uu____18091 :: out  in
                             (env2, uu____18084))
                    | uu____18107 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____17973 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

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
          let uu____18180 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____18180)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____18185 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____18185)
      | FStar_Parser_AST.TVariable x ->
          let uu____18189 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____18189)
      | FStar_Parser_AST.NoName t ->
          let uu____18193 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____18193)
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
      fun uu___258_18201  ->
        match uu___258_18201 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____18223 = FStar_Syntax_Syntax.null_binder k  in
            (uu____18223, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____18240 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____18240 with
             | (env1,a1) ->
                 let uu____18257 =
                   let uu____18264 = trans_aqual env1 imp  in
                   ((let uu___307_18270 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___307_18270.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___307_18270.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____18264)
                    in
                 (uu____18257, env1))

and (trans_aqual :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___259_18278  ->
      match uu___259_18278 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____18282 =
            let uu____18283 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____18283  in
          FStar_Pervasives_Native.Some uu____18282
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None

let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b  ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x,uu____18299) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x,uu____18301) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu____18304 -> FStar_Pervasives_Native.None
  
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs  ->
    FStar_List.collect
      (fun b  ->
         let uu____18322 = binder_ident b  in
         FStar_Common.list_of_option uu____18322) bs
  
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
               (fun uu___260_18359  ->
                  match uu___260_18359 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____18364 -> false))
           in
        let quals2 q =
          let uu____18378 =
            (let uu____18382 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____18382) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____18378
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____18399 = FStar_Ident.range_of_lid disc_name  in
                let uu____18400 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____18399;
                  FStar_Syntax_Syntax.sigquals = uu____18400;
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
            let uu____18440 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____18478  ->
                        match uu____18478 with
                        | (x,uu____18489) ->
                            let uu____18494 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____18494 with
                             | (field_name,uu____18502) ->
                                 let only_decl =
                                   ((let uu____18507 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____18507)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____18509 =
                                        let uu____18511 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____18511.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____18509)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____18529 =
                                       FStar_List.filter
                                         (fun uu___261_18533  ->
                                            match uu___261_18533 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____18536 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____18529
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___262_18551  ->
                                             match uu___262_18551 with
                                             | FStar_Syntax_Syntax.NoExtract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____18556 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____18559 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____18559;
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____18566 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____18566
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          (FStar_Syntax_Syntax.Delta_equational_at_level
                                             (Prims.parse_int "1"))
                                      else
                                        FStar_Syntax_Syntax.Delta_equational_at_level
                                          (Prims.parse_int "1")
                                       in
                                    let lb =
                                      let uu____18577 =
                                        let uu____18582 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____18582  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____18577;
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
                                      let uu____18586 =
                                        let uu____18587 =
                                          let uu____18594 =
                                            let uu____18597 =
                                              let uu____18598 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____18598
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____18597]  in
                                          ((false, [lb]), uu____18594)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____18587
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____18586;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____18440 FStar_List.flatten
  
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
            (lid,uu____18647,t,uu____18649,n1,uu____18651) when
            let uu____18658 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____18658 ->
            let uu____18660 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____18660 with
             | (formals,uu____18678) ->
                 (match formals with
                  | [] -> []
                  | uu____18707 ->
                      let filter_records uu___263_18723 =
                        match uu___263_18723 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____18726,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____18738 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____18740 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____18740 with
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
                      let uu____18752 = FStar_Util.first_N n1 formals  in
                      (match uu____18752 with
                       | (uu____18781,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____18815 -> []
  
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
                    let uu____18894 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____18894
                    then
                      let uu____18900 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____18900
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____18904 =
                      let uu____18909 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____18909  in
                    let uu____18910 =
                      if FStar_Util.is_some kopt
                      then
                        let uu____18916 =
                          let uu____18919 =
                            FStar_All.pipe_right kopt FStar_Util.must  in
                          FStar_Syntax_Syntax.mk_Total uu____18919  in
                        FStar_Syntax_Util.arrow typars uu____18916
                      else FStar_Syntax_Syntax.tun  in
                    let uu____18924 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____18904;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____18910;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____18924;
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
          let tycon_id uu___264_18978 =
            match uu___264_18978 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____18980,uu____18981) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____18991,uu____18992,uu____18993) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____19003,uu____19004,uu____19005) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____19035,uu____19036,uu____19037) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____19083) ->
                let uu____19084 =
                  let uu____19085 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____19085  in
                FStar_Parser_AST.mk_term uu____19084 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____19087 =
                  let uu____19088 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____19088  in
                FStar_Parser_AST.mk_term uu____19087 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____19090) ->
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
              | uu____19121 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____19129 =
                     let uu____19130 =
                       let uu____19137 = binder_to_term b  in
                       (out, uu____19137, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____19130  in
                   FStar_Parser_AST.mk_term uu____19129
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___265_19149 =
            match uu___265_19149 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____19206  ->
                       match uu____19206 with
                       | (x,t,uu____19217) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated (x, t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____19223 =
                    let uu____19224 =
                      let uu____19225 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____19225  in
                    FStar_Parser_AST.mk_term uu____19224
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____19223 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let names1 =
                  let uu____19232 = binder_idents parms  in id1 ::
                    uu____19232
                   in
                (FStar_List.iter
                   (fun uu____19250  ->
                      match uu____19250 with
                      | (f,uu____19260,uu____19261) ->
                          let uu____19266 =
                            FStar_Util.for_some
                              (fun i  -> FStar_Ident.ident_equals f i) names1
                             in
                          if uu____19266
                          then
                            let uu____19271 =
                              let uu____19277 =
                                let uu____19279 =
                                  FStar_Ident.string_of_ident f  in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu____19279
                                 in
                              (FStar_Errors.Error_FieldShadow, uu____19277)
                               in
                            FStar_Errors.raise_error uu____19271
                              f.FStar_Ident.idRange
                          else ()) fields;
                 (let uu____19285 =
                    FStar_All.pipe_right fields
                      (FStar_List.map
                         (fun uu____19312  ->
                            match uu____19312 with
                            | (x,uu____19322,uu____19323) -> x))
                     in
                  ((FStar_Parser_AST.TyconVariant
                      (id1, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp),
                           FStar_Pervasives_Native.None, false)])),
                    uu____19285)))
            | uu____19381 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___266_19421 =
            match uu___266_19421 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____19445 = typars_of_binders _env binders  in
                (match uu____19445 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____19481 =
                         let uu____19482 =
                           let uu____19483 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____19483  in
                         FStar_Parser_AST.mk_term uu____19482
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____19481 binders  in
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
            | uu____19494 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____19537 =
              FStar_List.fold_left
                (fun uu____19571  ->
                   fun uu____19572  ->
                     match (uu____19571, uu____19572) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____19641 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____19641 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____19537 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____19732 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____19732
                | uu____19733 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____19741 = desugar_abstract_tc quals env [] tc  in
              (match uu____19741 with
               | (uu____19754,uu____19755,se,uu____19757) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____19760,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____19779 =
                                 let uu____19781 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____19781  in
                               if uu____19779
                               then
                                 let uu____19784 =
                                   let uu____19790 =
                                     let uu____19792 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____19792
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____19790)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____19784
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
                           | uu____19805 ->
                               let uu____19806 =
                                 let uu____19813 =
                                   let uu____19814 =
                                     let uu____19829 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____19829)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____19814
                                    in
                                 FStar_Syntax_Syntax.mk uu____19813  in
                               uu____19806 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___308_19845 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___308_19845.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___308_19845.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___308_19845.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____19846 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____19850 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____19850
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____19863 = typars_of_binders env binders  in
              (match uu____19863 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____19897 =
                           FStar_Util.for_some
                             (fun uu___267_19900  ->
                                match uu___267_19900 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____19903 -> false) quals
                            in
                         if uu____19897
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____19911 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____19911
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____19916 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___268_19922  ->
                               match uu___268_19922 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____19925 -> false))
                        in
                     if uu____19916
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____19939 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____19939
                     then
                       let uu____19945 =
                         let uu____19952 =
                           let uu____19953 = unparen t  in
                           uu____19953.FStar_Parser_AST.tm  in
                         match uu____19952 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____19974 =
                               match FStar_List.rev args with
                               | (last_arg,uu____20004)::args_rev ->
                                   let uu____20016 =
                                     let uu____20017 = unparen last_arg  in
                                     uu____20017.FStar_Parser_AST.tm  in
                                   (match uu____20016 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____20045 -> ([], args))
                               | uu____20054 -> ([], args)  in
                             (match uu____19974 with
                              | (cattributes,args1) ->
                                  let uu____20093 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____20093))
                         | uu____20104 -> (t, [])  in
                       match uu____19945 with
                       | (t1,cattributes) ->
                           let c =
                             desugar_comp t1.FStar_Parser_AST.range false
                               env' t1
                              in
                           let typars1 =
                             FStar_Syntax_Subst.close_binders typars  in
                           let c1 = FStar_Syntax_Subst.close_comp typars1 c
                              in
                           let quals2 =
                             FStar_All.pipe_right quals1
                               (FStar_List.filter
                                  (fun uu___269_20127  ->
                                     match uu___269_20127 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____20130 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____20139)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____20163 = tycon_record_as_variant trec  in
              (match uu____20163 with
               | (t,fs) ->
                   let uu____20180 =
                     let uu____20183 =
                       let uu____20184 =
                         let uu____20193 =
                           let uu____20196 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____20196  in
                         (uu____20193, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____20184  in
                     uu____20183 :: quals  in
                   desugar_tycon env d uu____20180 [t])
          | uu____20201::uu____20202 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____20372 = et  in
                match uu____20372 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____20602 ->
                         let trec = tc  in
                         let uu____20626 = tycon_record_as_variant trec  in
                         (match uu____20626 with
                          | (t,fs) ->
                              let uu____20686 =
                                let uu____20689 =
                                  let uu____20690 =
                                    let uu____20699 =
                                      let uu____20702 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____20702  in
                                    (uu____20699, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____20690
                                   in
                                uu____20689 :: quals1  in
                              collect_tcs uu____20686 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____20792 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____20792 with
                          | (env2,uu____20853,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____21006 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____21006 with
                          | (env2,uu____21067,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____21195 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____21245 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____21245 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___271_21760  ->
                             match uu___271_21760 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____21826,uu____21827);
                                    FStar_Syntax_Syntax.sigrng = uu____21828;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____21829;
                                    FStar_Syntax_Syntax.sigmeta = uu____21830;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____21831;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____21895 =
                                     typars_of_binders env1 binders  in
                                   match uu____21895 with
                                   | (env2,tpars1) ->
                                       let uu____21922 =
                                         push_tparams env2 tpars1  in
                                       (match uu____21922 with
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
                                 let uu____21951 =
                                   let uu____21970 =
                                     mk_typ_abbrev id1 uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____21970)
                                    in
                                 [uu____21951]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____22030);
                                    FStar_Syntax_Syntax.sigrng = uu____22031;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____22033;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____22034;_},constrs,tconstr,quals1)
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
                                 let uu____22135 = push_tparams env1 tpars
                                    in
                                 (match uu____22135 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____22202  ->
                                             match uu____22202 with
                                             | (x,uu____22214) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____22219 =
                                        let uu____22246 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____22356  ->
                                                  match uu____22356 with
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
                                                        let uu____22416 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____22416
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
                                                                uu___270_22427
                                                                 ->
                                                                match uu___270_22427
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____22439
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____22447 =
                                                        let uu____22466 =
                                                          let uu____22467 =
                                                            let uu____22468 =
                                                              let uu____22484
                                                                =
                                                                let uu____22485
                                                                  =
                                                                  let uu____22488
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____22488
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____22485
                                                                 in
                                                              (name, univs1,
                                                                uu____22484,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____22468
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____22467;
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
                                                          uu____22466)
                                                         in
                                                      (name, uu____22447)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____22246
                                         in
                                      (match uu____22219 with
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
                             | uu____22704 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____22832  ->
                             match uu____22832 with
                             | (name_doc,uu____22858,uu____22859) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____22931  ->
                             match uu____22931 with
                             | (uu____22950,uu____22951,se) -> se))
                      in
                   let uu____22977 =
                     let uu____22984 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____22984 rng
                      in
                   (match uu____22977 with
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
                               (fun uu____23046  ->
                                  match uu____23046 with
                                  | (uu____23067,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____23114,tps,k,uu____23117,constrs)
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
                                  | uu____23139 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____23156  ->
                                 match uu____23156 with
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
      let uu____23201 =
        FStar_List.fold_left
          (fun uu____23236  ->
             fun b  ->
               match uu____23236 with
               | (env1,binders1) ->
                   let uu____23280 = desugar_binder env1 b  in
                   (match uu____23280 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____23303 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____23303 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____23356 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____23201 with
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
          let uu____23460 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___272_23467  ->
                    match uu___272_23467 with
                    | FStar_Syntax_Syntax.Reflectable uu____23469 -> true
                    | uu____23471 -> false))
             in
          if uu____23460
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____23476 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____23476
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
      let uu____23517 = FStar_Syntax_Util.head_and_args at1  in
      match uu____23517 with
      | (hd1,args) ->
          let uu____23570 =
            let uu____23585 =
              let uu____23586 = FStar_Syntax_Subst.compress hd1  in
              uu____23586.FStar_Syntax_Syntax.n  in
            (uu____23585, args)  in
          (match uu____23570 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(a1,uu____23611)::[]) when
               (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr)
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.fail_lax_attr)
               ->
               let uu____23646 =
                 let uu____23651 =
                   let uu____23660 =
                     FStar_Syntax_Embeddings.e_list
                       FStar_Syntax_Embeddings.e_int
                      in
                   FStar_Syntax_Embeddings.unembed uu____23660 a1  in
                 uu____23651 true FStar_Syntax_Embeddings.id_norm_cb  in
               (match uu____23646 with
                | FStar_Pervasives_Native.Some es when
                    (FStar_List.length es) > (Prims.parse_int "0") ->
                    let b =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.fail_lax_attr
                       in
                    let uu____23690 =
                      let uu____23699 =
                        FStar_List.map FStar_BigInt.to_int_fs es  in
                      (uu____23699, b)  in
                    FStar_Pervasives_Native.Some uu____23690
                | uu____23716 ->
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
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____23770) when
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
           | uu____23805 -> FStar_Pervasives_Native.None)
  
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
                  let uu____23977 = desugar_binders monad_env eff_binders  in
                  match uu____23977 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let for_free =
                        let uu____24017 =
                          let uu____24019 =
                            let uu____24028 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____24028  in
                          FStar_List.length uu____24019  in
                        uu____24017 = (Prims.parse_int "1")  in
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
                            (uu____24112,uu____24113,(FStar_Parser_AST.TyconAbbrev
                                                      (name,uu____24115,uu____24116,uu____24117),uu____24118)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____24155 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____24158 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____24170 = name_of_eff_decl decl  in
                             FStar_List.mem uu____24170 mandatory_members)
                          eff_decls
                         in
                      (match uu____24158 with
                       | (mandatory_members_decls,actions) ->
                           let uu____24189 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____24218  ->
                                     fun decl  ->
                                       match uu____24218 with
                                       | (env2,out) ->
                                           let uu____24238 =
                                             desugar_decl env2 decl  in
                                           (match uu____24238 with
                                            | (env3,ses) ->
                                                let uu____24251 =
                                                  let uu____24254 =
                                                    FStar_List.hd ses  in
                                                  uu____24254 :: out  in
                                                (env3, uu____24251)))
                                  (env1, []))
                              in
                           (match uu____24189 with
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
                                              (uu____24323,uu____24324,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____24327,
                                                 {
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.Construct
                                                     (uu____24328,(def,uu____24330)::
                                                      (cps_type,uu____24332)::[]);
                                                   FStar_Parser_AST.range =
                                                     uu____24333;
                                                   FStar_Parser_AST.level =
                                                     uu____24334;_}),doc1)::[])
                                              when Prims.op_Negation for_free
                                              ->
                                              let uu____24390 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____24390 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____24428 =
                                                     let uu____24429 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____24430 =
                                                       let uu____24431 =
                                                         desugar_term env3
                                                           def
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____24431
                                                        in
                                                     let uu____24438 =
                                                       let uu____24439 =
                                                         desugar_typ env3
                                                           cps_type
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____24439
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____24429;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____24430;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____24438
                                                     }  in
                                                   (uu____24428, doc1))
                                          | FStar_Parser_AST.Tycon
                                              (uu____24448,uu____24449,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____24452,defn),doc1)::[])
                                              when for_free ->
                                              let uu____24491 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____24491 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____24529 =
                                                     let uu____24530 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____24531 =
                                                       let uu____24532 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____24532
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____24530;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____24531;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____24529, doc1))
                                          | uu____24541 ->
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
                                    let uu____24577 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____24577
                                     in
                                  let uu____24579 =
                                    let uu____24580 =
                                      FStar_Syntax_DsEnv.fail_or env2
                                        (FStar_Syntax_DsEnv.try_lookup_definition
                                           env2) l
                                       in
                                    FStar_All.pipe_left
                                      (FStar_Syntax_Subst.close binders1)
                                      uu____24580
                                     in
                                  ([], uu____24579)  in
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
                                      let uu____24598 =
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      ([], uu____24598)  in
                                    let uu____24605 =
                                      let uu____24606 =
                                        let uu____24607 =
                                          let uu____24608 = lookup1 "repr"
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____24608
                                           in
                                        let uu____24618 = lookup1 "return"
                                           in
                                        let uu____24620 = lookup1 "bind"  in
                                        let uu____24622 =
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
                                            uu____24607;
                                          FStar_Syntax_Syntax.return_repr =
                                            uu____24618;
                                          FStar_Syntax_Syntax.bind_repr =
                                            uu____24620;
                                          FStar_Syntax_Syntax.actions =
                                            actions1;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            uu____24622
                                        }  in
                                      FStar_Syntax_Syntax.Sig_new_effect_for_free
                                        uu____24606
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____24605;
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
                                         (fun uu___273_24630  ->
                                            match uu___273_24630 with
                                            | FStar_Syntax_Syntax.Reifiable 
                                                -> true
                                            | FStar_Syntax_Syntax.Reflectable
                                                uu____24633 -> true
                                            | uu____24635 -> false)
                                         qualifiers
                                        in
                                     let un_ts =
                                       ([], FStar_Syntax_Syntax.tun)  in
                                     let uu____24650 =
                                       let uu____24651 =
                                         let uu____24652 =
                                           lookup1 "return_wp"  in
                                         let uu____24654 = lookup1 "bind_wp"
                                            in
                                         let uu____24656 =
                                           lookup1 "if_then_else"  in
                                         let uu____24658 = lookup1 "ite_wp"
                                            in
                                         let uu____24660 = lookup1 "stronger"
                                            in
                                         let uu____24662 = lookup1 "close_wp"
                                            in
                                         let uu____24664 = lookup1 "assert_p"
                                            in
                                         let uu____24666 = lookup1 "assume_p"
                                            in
                                         let uu____24668 = lookup1 "null_wp"
                                            in
                                         let uu____24670 = lookup1 "trivial"
                                            in
                                         let uu____24672 =
                                           if rr
                                           then
                                             let uu____24674 = lookup1 "repr"
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.snd
                                               uu____24674
                                           else FStar_Syntax_Syntax.tun  in
                                         let uu____24692 =
                                           if rr
                                           then lookup1 "return"
                                           else un_ts  in
                                         let uu____24697 =
                                           if rr
                                           then lookup1 "bind"
                                           else un_ts  in
                                         let uu____24702 =
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
                                             uu____24652;
                                           FStar_Syntax_Syntax.bind_wp =
                                             uu____24654;
                                           FStar_Syntax_Syntax.if_then_else =
                                             uu____24656;
                                           FStar_Syntax_Syntax.ite_wp =
                                             uu____24658;
                                           FStar_Syntax_Syntax.stronger =
                                             uu____24660;
                                           FStar_Syntax_Syntax.close_wp =
                                             uu____24662;
                                           FStar_Syntax_Syntax.assert_p =
                                             uu____24664;
                                           FStar_Syntax_Syntax.assume_p =
                                             uu____24666;
                                           FStar_Syntax_Syntax.null_wp =
                                             uu____24668;
                                           FStar_Syntax_Syntax.trivial =
                                             uu____24670;
                                           FStar_Syntax_Syntax.repr =
                                             uu____24672;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____24692;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____24697;
                                           FStar_Syntax_Syntax.actions =
                                             actions1;
                                           FStar_Syntax_Syntax.eff_attrs =
                                             uu____24702
                                         }  in
                                       FStar_Syntax_Syntax.Sig_new_effect
                                         uu____24651
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         uu____24650;
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
                                          fun uu____24728  ->
                                            match uu____24728 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____24742 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____24742
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
                let uu____24766 = desugar_binders env1 eff_binders  in
                match uu____24766 with
                | (env2,binders) ->
                    let uu____24803 =
                      let uu____24814 = head_and_args defn  in
                      match uu____24814 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____24851 ->
                                let uu____24852 =
                                  let uu____24858 =
                                    let uu____24860 =
                                      let uu____24862 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.strcat uu____24862 " not found"
                                       in
                                    Prims.strcat "Effect " uu____24860  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____24858)
                                   in
                                FStar_Errors.raise_error uu____24852
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____24868 =
                            match FStar_List.rev args with
                            | (last_arg,uu____24898)::args_rev ->
                                let uu____24910 =
                                  let uu____24911 = unparen last_arg  in
                                  uu____24911.FStar_Parser_AST.tm  in
                                (match uu____24910 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____24939 -> ([], args))
                            | uu____24948 -> ([], args)  in
                          (match uu____24868 with
                           | (cattributes,args1) ->
                               let uu____24991 = desugar_args env2 args1  in
                               let uu____24992 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____24991, uu____24992))
                       in
                    (match uu____24803 with
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
                          (let uu____25032 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____25032 with
                           | (ed_binders,uu____25046,ed_binders_opening) ->
                               let sub1 uu____25059 =
                                 match uu____25059 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____25073 =
                                         FStar_Syntax_Subst.shift_subst
                                           (FStar_List.length us)
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____25073 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____25077 =
                                       let uu____25078 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____25078)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____25077
                                  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____25087 =
                                   let uu____25088 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____25088
                                    in
                                 let uu____25103 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____25104 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____25105 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____25106 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____25107 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____25108 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____25109 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____25110 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____25111 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____25112 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____25113 =
                                   let uu____25114 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____25114
                                    in
                                 let uu____25129 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____25130 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____25131 =
                                   FStar_List.map
                                     (fun action  ->
                                        let uu____25139 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____25140 =
                                          let uu____25141 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____25141
                                           in
                                        let uu____25156 =
                                          let uu____25157 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____25157
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____25139;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____25140;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____25156
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
                                     uu____25087;
                                   FStar_Syntax_Syntax.ret_wp = uu____25103;
                                   FStar_Syntax_Syntax.bind_wp = uu____25104;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____25105;
                                   FStar_Syntax_Syntax.ite_wp = uu____25106;
                                   FStar_Syntax_Syntax.stronger = uu____25107;
                                   FStar_Syntax_Syntax.close_wp = uu____25108;
                                   FStar_Syntax_Syntax.assert_p = uu____25109;
                                   FStar_Syntax_Syntax.assume_p = uu____25110;
                                   FStar_Syntax_Syntax.null_wp = uu____25111;
                                   FStar_Syntax_Syntax.trivial = uu____25112;
                                   FStar_Syntax_Syntax.repr = uu____25113;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____25129;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____25130;
                                   FStar_Syntax_Syntax.actions = uu____25131;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____25175 =
                                     let uu____25177 =
                                       let uu____25186 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____25186
                                        in
                                     FStar_List.length uu____25177  in
                                   uu____25175 = (Prims.parse_int "1")  in
                                 let uu____25219 =
                                   let uu____25222 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____25222 quals  in
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
                                   FStar_Syntax_Syntax.sigquals = uu____25219;
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
                                             let uu____25246 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____25246
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____25248 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____25248
                                 then
                                   let reflect_lid =
                                     let uu____25255 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____25255
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
    let uu____25267 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____25267 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.strcat "  " (Prims.strcat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____25352 ->
              let uu____25355 =
                let uu____25357 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____25357
                 in
              Prims.strcat "\n  " uu____25355
          | uu____25360 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____25379  ->
               match uu____25379 with
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
          let uu____25424 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____25424
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____25427 =
          let uu____25438 = FStar_Syntax_Syntax.as_arg arg  in [uu____25438]
           in
        FStar_Syntax_Util.mk_app fv uu____25427

and (desugar_decl_aux :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      let uu____25469 = desugar_decl_noattrs env d  in
      match uu____25469 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____25487 = mk_comment_attr d  in uu____25487 :: attrs1  in
          let uu____25488 =
            FStar_List.mapi
              (fun i  ->
                 fun sigelt  ->
                   if i = (Prims.parse_int "0")
                   then
                     let uu___309_25498 = sigelt  in
                     {
                       FStar_Syntax_Syntax.sigel =
                         (uu___309_25498.FStar_Syntax_Syntax.sigel);
                       FStar_Syntax_Syntax.sigrng =
                         (uu___309_25498.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___309_25498.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___309_25498.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs = attrs2
                     }
                   else
                     (let uu___310_25501 = sigelt  in
                      let uu____25502 =
                        FStar_List.filter
                          (fun at1  ->
                             let uu____25508 = get_fail_attr false at1  in
                             FStar_Option.isNone uu____25508) attrs2
                         in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___310_25501.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___310_25501.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___310_25501.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___310_25501.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs = uu____25502
                      })) sigelts
             in
          (env1, uu____25488)

and (desugar_decl :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      let uu____25534 = desugar_decl_aux env d  in
      match uu____25534 with
      | (env1,ses) ->
          let uu____25545 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____25545)

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
      | FStar_Parser_AST.Fsdoc uu____25573 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Friend lid ->
          let uu____25578 = FStar_Syntax_DsEnv.iface env  in
          if uu____25578
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____25593 =
               let uu____25595 =
                 let uu____25597 = FStar_Syntax_DsEnv.dep_graph env  in
                 let uu____25598 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Parser_Dep.module_has_interface uu____25597
                   uu____25598
                  in
               Prims.op_Negation uu____25595  in
             if uu____25593
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____25612 =
                  let uu____25614 =
                    let uu____25616 = FStar_Syntax_DsEnv.dep_graph env  in
                    FStar_Parser_Dep.module_has_interface uu____25616 lid  in
                  Prims.op_Negation uu____25614  in
                if uu____25612
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____25630 =
                     let uu____25632 =
                       let uu____25634 = FStar_Syntax_DsEnv.dep_graph env  in
                       FStar_Parser_Dep.deps_has_implementation uu____25634
                         lid
                        in
                     Prims.op_Negation uu____25632  in
                   if uu____25630
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____25652 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____25652, [])
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
              | (FStar_Parser_AST.TyconRecord uu____25693,uu____25694)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu____25733 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1  in
          let tcs1 =
            FStar_List.map
              (fun uu____25760  ->
                 match uu____25760 with | (x,uu____25768) -> x) tcs
             in
          let uu____25773 =
            let uu____25778 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____25778 tcs1  in
          (match uu____25773 with
           | (env1,ses) ->
               let mkclass lid =
                 let uu____25795 =
                   let uu____25796 =
                     let uu____25803 =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun
                        in
                     FStar_Syntax_Syntax.mk_binder uu____25803  in
                   [uu____25796]  in
                 let uu____25816 =
                   let uu____25819 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____25822 =
                     let uu____25833 =
                       let uu____25842 =
                         let uu____25843 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____25843  in
                       FStar_Syntax_Syntax.as_arg uu____25842  in
                     [uu____25833]  in
                   FStar_Syntax_Util.mk_app uu____25819 uu____25822  in
                 FStar_Syntax_Util.abs uu____25795 uu____25816
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____25883,id1))::uu____25885 ->
                       FStar_Pervasives_Native.Some id1
                   | uu____25888::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____25892 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____25892 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id1 ->
                     let uu____25898 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     [uu____25898]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____25919) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____25929,uu____25930,uu____25931,uu____25932,uu____25933)
                     ->
                     let uu____25942 =
                       let uu____25943 =
                         let uu____25944 =
                           let uu____25951 = mkclass lid  in
                           (meths, uu____25951)  in
                         FStar_Syntax_Syntax.Sig_splice uu____25944  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____25943;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = []
                       }  in
                     [uu____25942]
                 | uu____25954 -> []  in
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
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____25988;
                    FStar_Parser_AST.prange = uu____25989;_},uu____25990)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____26000;
                    FStar_Parser_AST.prange = uu____26001;_},uu____26002)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____26018;
                         FStar_Parser_AST.prange = uu____26019;_},uu____26020);
                    FStar_Parser_AST.prange = uu____26021;_},uu____26022)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____26044;
                         FStar_Parser_AST.prange = uu____26045;_},uu____26046);
                    FStar_Parser_AST.prange = uu____26047;_},uu____26048)::[]
                   -> false
               | (p,uu____26077)::[] ->
                   let uu____26086 = is_app_pattern p  in
                   Prims.op_Negation uu____26086
               | uu____26088 -> false)
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
            let uu____26163 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____26163 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____26176 =
                     let uu____26177 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____26177.FStar_Syntax_Syntax.n  in
                   match uu____26176 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____26187) ->
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
                         | uu____26223::uu____26224 ->
                             FStar_List.map
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____26227 ->
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.collect
                                  (fun uu___274_26243  ->
                                     match uu___274_26243 with
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inl uu____26246;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____26247;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____26248;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____26249;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____26250;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____26251;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____26252;_}
                                         -> []
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____26264;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____26265;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____26266;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____26267;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____26268;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____26269;_}
                                         ->
                                         FStar_Syntax_DsEnv.lookup_letbinding_quals
                                           env
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                          in
                       let quals2 =
                         let uu____26283 =
                           FStar_All.pipe_right lets1
                             (FStar_Util.for_some
                                (fun uu____26316  ->
                                   match uu____26316 with
                                   | (uu____26330,(uu____26331,t)) ->
                                       t.FStar_Parser_AST.level =
                                         FStar_Parser_AST.Formula))
                            in
                         if uu____26283
                         then FStar_Syntax_Syntax.Logic :: quals1
                         else quals1  in
                       let lbs1 =
                         let uu____26351 =
                           FStar_All.pipe_right quals2
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract)
                            in
                         if uu____26351
                         then
                           let uu____26357 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu___311_26372 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___312_26374 = fv  in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___312_26374.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___312_26374.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___311_26372.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___311_26372.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___311_26372.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___311_26372.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___311_26372.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___311_26372.FStar_Syntax_Syntax.lbpos)
                                     }))
                              in
                           ((FStar_Pervasives_Native.fst lbs), uu____26357)
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
                   | uu____26404 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____26412 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____26431 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____26412 with
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
                       let uu___313_26468 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___313_26468.FStar_Parser_AST.prange)
                       }
                   | uu____26475 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___314_26482 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___314_26482.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___314_26482.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___314_26482.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____26518 id1 =
                   match uu____26518 with
                   | (env1,ses) ->
                       let main =
                         let uu____26539 =
                           let uu____26540 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____26540  in
                         FStar_Parser_AST.mk_term uu____26539
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
                       let uu____26590 = desugar_decl env1 id_decl  in
                       (match uu____26590 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____26608 = gather_pattern_bound_vars true pat  in
                   FStar_All.pipe_right uu____26608 FStar_Util.set_elements
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
            let uu____26632 = close_fun env t  in
            desugar_term env uu____26632  in
          let quals1 =
            let uu____26636 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____26636
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let se =
            let uu____26645 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____26645;
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
                let uu____26659 =
                  let uu____26668 = FStar_Syntax_Syntax.null_binder t  in
                  [uu____26668]  in
                let uu____26687 =
                  let uu____26690 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total
                    uu____26690
                   in
                FStar_Syntax_Util.arrow uu____26659 uu____26687
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
            let uu____26745 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____26745 with
            | FStar_Pervasives_Native.None  ->
                let uu____26748 =
                  let uu____26754 =
                    let uu____26756 =
                      let uu____26758 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.strcat uu____26758 " not found"  in
                    Prims.strcat "Effect name " uu____26756  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____26754)  in
                FStar_Errors.raise_error uu____26748
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____26766 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____26784 =
                  let uu____26787 =
                    let uu____26788 = desugar_term env t  in
                    ([], uu____26788)  in
                  FStar_Pervasives_Native.Some uu____26787  in
                (uu____26784, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____26801 =
                  let uu____26804 =
                    let uu____26805 = desugar_term env wp  in
                    ([], uu____26805)  in
                  FStar_Pervasives_Native.Some uu____26804  in
                let uu____26812 =
                  let uu____26815 =
                    let uu____26816 = desugar_term env t  in
                    ([], uu____26816)  in
                  FStar_Pervasives_Native.Some uu____26815  in
                (uu____26801, uu____26812)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____26828 =
                  let uu____26831 =
                    let uu____26832 = desugar_term env t  in
                    ([], uu____26832)  in
                  FStar_Pervasives_Native.Some uu____26831  in
                (FStar_Pervasives_Native.None, uu____26828)
             in
          (match uu____26766 with
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
            let uu____26866 =
              let uu____26867 =
                let uu____26874 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____26874, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____26867  in
            {
              FStar_Syntax_Syntax.sigel = uu____26866;
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
      let uu____26901 =
        FStar_List.fold_left
          (fun uu____26921  ->
             fun d  ->
               match uu____26921 with
               | (env1,sigelts) ->
                   let uu____26941 = desugar_decl env1 d  in
                   (match uu____26941 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____26901 with
      | (env1,sigelts) ->
          let rec forward acc uu___276_26986 =
            match uu___276_26986 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____27000,FStar_Syntax_Syntax.Sig_let uu____27001) ->
                     let uu____27014 =
                       let uu____27017 =
                         let uu___315_27018 = se2  in
                         let uu____27019 =
                           let uu____27022 =
                             FStar_List.filter
                               (fun uu___275_27036  ->
                                  match uu___275_27036 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____27041;
                                           FStar_Syntax_Syntax.vars =
                                             uu____27042;_},uu____27043);
                                      FStar_Syntax_Syntax.pos = uu____27044;
                                      FStar_Syntax_Syntax.vars = uu____27045;_}
                                      when
                                      let uu____27072 =
                                        let uu____27074 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____27074
                                         in
                                      uu____27072 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____27078 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____27022
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___315_27018.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___315_27018.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___315_27018.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___315_27018.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____27019
                         }  in
                       uu____27017 :: se1 :: acc  in
                     forward uu____27014 sigelts1
                 | uu____27084 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____27092 = forward [] sigelts  in (env1, uu____27092)
  
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
          | (FStar_Pervasives_Native.None ,uu____27157) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____27161;
               FStar_Syntax_Syntax.exports = uu____27162;
               FStar_Syntax_Syntax.is_interface = uu____27163;_},FStar_Parser_AST.Module
             (current_lid,uu____27165)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____27174) ->
              let uu____27177 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____27177
           in
        let uu____27182 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____27224 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____27224, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____27246 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____27246, mname, decls, false)
           in
        match uu____27182 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____27288 = desugar_decls env2 decls  in
            (match uu____27288 with
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
          let uu____27356 =
            (FStar_Options.interactive ()) &&
              (let uu____27359 =
                 let uu____27361 =
                   let uu____27363 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____27363  in
                 FStar_Util.get_file_extension uu____27361  in
               FStar_List.mem uu____27359 ["fsti"; "fsi"])
             in
          if uu____27356 then as_interface m else m  in
        let uu____27377 = desugar_modul_common curmod env m1  in
        match uu____27377 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____27399 = FStar_Syntax_DsEnv.pop ()  in
              (uu____27399, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul ->
      (env_t,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun m  ->
      let uu____27421 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____27421 with
      | (env1,modul,pop_when_done) ->
          let uu____27438 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____27438 with
           | (env2,modul1) ->
               ((let uu____27450 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____27450
                 then
                   let uu____27453 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____27453
                 else ());
                (let uu____27458 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____27458, modul1))))
  
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
        (fun uu____27512  ->
           let uu____27513 = desugar_modul env modul  in
           match uu____27513 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____27555  ->
           let uu____27556 = desugar_decls env decls  in
           match uu____27556 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____27611  ->
             let uu____27612 = desugar_partial_modul modul env a_modul  in
             match uu____27612 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____27711 ->
                  let t =
                    let uu____27721 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____27721  in
                  let uu____27734 =
                    let uu____27735 = FStar_Syntax_Subst.compress t  in
                    uu____27735.FStar_Syntax_Syntax.n  in
                  (match uu____27734 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____27747,uu____27748)
                       -> bs1
                   | uu____27773 -> failwith "Impossible")
               in
            let uu____27783 =
              let uu____27790 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____27790
                FStar_Syntax_Syntax.t_unit
               in
            match uu____27783 with
            | (binders,uu____27792,binders_opening) ->
                let erase_term t =
                  let uu____27800 =
                    let uu____27801 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____27801  in
                  FStar_Syntax_Subst.close binders uu____27800  in
                let erase_tscheme uu____27819 =
                  match uu____27819 with
                  | (us,t) ->
                      let t1 =
                        let uu____27839 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____27839 t  in
                      let uu____27842 =
                        let uu____27843 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____27843  in
                      ([], uu____27842)
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
                    | uu____27866 ->
                        let bs =
                          let uu____27876 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____27876  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____27916 =
                          let uu____27917 =
                            let uu____27920 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____27920  in
                          uu____27917.FStar_Syntax_Syntax.n  in
                        (match uu____27916 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____27922,uu____27923) -> bs1
                         | uu____27948 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____27956 =
                      let uu____27957 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____27957  in
                    FStar_Syntax_Subst.close binders uu____27956  in
                  let uu___316_27958 = action  in
                  let uu____27959 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____27960 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___316_27958.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___316_27958.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____27959;
                    FStar_Syntax_Syntax.action_typ = uu____27960
                  }  in
                let uu___317_27961 = ed  in
                let uu____27962 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____27963 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____27964 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____27965 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____27966 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____27967 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____27968 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____27969 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____27970 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____27971 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____27972 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____27973 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____27974 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____27975 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____27976 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____27977 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___317_27961.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___317_27961.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____27962;
                  FStar_Syntax_Syntax.signature = uu____27963;
                  FStar_Syntax_Syntax.ret_wp = uu____27964;
                  FStar_Syntax_Syntax.bind_wp = uu____27965;
                  FStar_Syntax_Syntax.if_then_else = uu____27966;
                  FStar_Syntax_Syntax.ite_wp = uu____27967;
                  FStar_Syntax_Syntax.stronger = uu____27968;
                  FStar_Syntax_Syntax.close_wp = uu____27969;
                  FStar_Syntax_Syntax.assert_p = uu____27970;
                  FStar_Syntax_Syntax.assume_p = uu____27971;
                  FStar_Syntax_Syntax.null_wp = uu____27972;
                  FStar_Syntax_Syntax.trivial = uu____27973;
                  FStar_Syntax_Syntax.repr = uu____27974;
                  FStar_Syntax_Syntax.return_repr = uu____27975;
                  FStar_Syntax_Syntax.bind_repr = uu____27976;
                  FStar_Syntax_Syntax.actions = uu____27977;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___317_27961.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___318_27993 = se  in
                  let uu____27994 =
                    let uu____27995 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____27995  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____27994;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___318_27993.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___318_27993.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___318_27993.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___318_27993.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___319_27999 = se  in
                  let uu____28000 =
                    let uu____28001 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____28001
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____28000;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___319_27999.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___319_27999.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___319_27999.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___319_27999.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____28003 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____28004 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____28004 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____28021 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____28021
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____28023 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____28023)
  