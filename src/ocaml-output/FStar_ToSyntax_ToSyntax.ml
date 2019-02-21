open Prims
type annotated_pat =
  (FStar_Syntax_Syntax.pat * (FStar_Syntax_Syntax.bv *
    FStar_Syntax_Syntax.typ) Prims.list)
let (desugar_disjunctive_pattern :
  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list) Prims.list ->
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
      fun uu___1_241  ->
        match uu___1_241 with
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
  fun uu___2_261  ->
    match uu___2_261 with
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
  fun uu___3_279  ->
    match uu___3_279 with
    | FStar_Parser_AST.Hash  ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | uu____282 -> FStar_Pervasives_Native.None
  
let arg_withimp_e :
  'Auu____290 .
    FStar_Parser_AST.imp ->
      'Auu____290 ->
        ('Auu____290 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  = fun imp  -> fun t  -> (t, (as_imp imp)) 
let arg_withimp_t :
  'Auu____316 .
    FStar_Parser_AST.imp ->
      'Auu____316 ->
        ('Auu____316 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
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
            | uu____595 -> FStar_Pervasives_Native.None  in
          let uu____597 =
            let uu____600 =
              compile_op_lid arity op.FStar_Ident.idText
                op.FStar_Ident.idRange
               in
            FStar_Syntax_DsEnv.try_lookup_lid env uu____600  in
          match uu____597 with
          | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
          | uu____604 -> fallback ()
  
let (sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list)
  =
  fun ftv  ->
    let uu____619 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv
       in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____619
  
let rec (free_type_vars_b :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Syntax_DsEnv.env * FStar_Ident.ident Prims.list))
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____668 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____672 = FStar_Syntax_DsEnv.push_bv env x  in
          (match uu____672 with | (env1,uu____684) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____687,term) ->
          let uu____689 = free_type_vars env term  in (env, uu____689)
      | FStar_Parser_AST.TAnnotated (id1,uu____695) ->
          let uu____696 = FStar_Syntax_DsEnv.push_bv env id1  in
          (match uu____696 with | (env1,uu____708) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____712 = free_type_vars env t  in (env, uu____712)

and (free_type_vars :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun t  ->
      let uu____719 =
        let uu____720 = unparen t  in uu____720.FStar_Parser_AST.tm  in
      match uu____719 with
      | FStar_Parser_AST.Labeled uu____723 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____736 = FStar_Syntax_DsEnv.try_lookup_id env a  in
          (match uu____736 with
           | FStar_Pervasives_Native.None  -> [a]
           | uu____741 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____744 -> []
      | FStar_Parser_AST.Uvar uu____745 -> []
      | FStar_Parser_AST.Var uu____746 -> []
      | FStar_Parser_AST.Projector uu____747 -> []
      | FStar_Parser_AST.Discrim uu____752 -> []
      | FStar_Parser_AST.Name uu____753 -> []
      | FStar_Parser_AST.Requires (t1,uu____755) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____763) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____770,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None  -> []
             | FStar_Pervasives_Native.Some t2 -> [t2])
             in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____789,ts) ->
          FStar_List.collect
            (fun uu____810  ->
               match uu____810 with | (t1,uu____818) -> free_type_vars env t1)
            ts
      | FStar_Parser_AST.Op (uu____819,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____827) ->
          let uu____828 = free_type_vars env t1  in
          let uu____831 = free_type_vars env t2  in
          FStar_List.append uu____828 uu____831
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____836 = free_type_vars_b env b  in
          (match uu____836 with
           | (env1,f) ->
               let uu____851 = free_type_vars env1 t1  in
               FStar_List.append f uu____851)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____868 =
            FStar_List.fold_left
              (fun uu____892  ->
                 fun bt  ->
                   match uu____892 with
                   | (env1,free) ->
                       let uu____916 =
                         match bt with
                         | FStar_Util.Inl binder ->
                             free_type_vars_b env1 binder
                         | FStar_Util.Inr t1 ->
                             let uu____931 = free_type_vars env1 body  in
                             (env1, uu____931)
                          in
                       (match uu____916 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____868 with
           | (env1,free) ->
               let uu____960 = free_type_vars env1 body  in
               FStar_List.append free uu____960)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____969 =
            FStar_List.fold_left
              (fun uu____989  ->
                 fun binder  ->
                   match uu____989 with
                   | (env1,free) ->
                       let uu____1009 = free_type_vars_b env1 binder  in
                       (match uu____1009 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____969 with
           | (env1,free) ->
               let uu____1040 = free_type_vars env1 body  in
               FStar_List.append free uu____1040)
      | FStar_Parser_AST.Project (t1,uu____1044) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
          let uu____1055 = free_type_vars env rel  in
          let uu____1058 =
            let uu____1061 = free_type_vars env init1  in
            let uu____1064 =
              FStar_List.collect
                (fun uu____1073  ->
                   match uu____1073 with
                   | FStar_Parser_AST.CalcStep (rel1,just,next) ->
                       let uu____1079 = free_type_vars env rel1  in
                       let uu____1082 =
                         let uu____1085 = free_type_vars env just  in
                         let uu____1088 = free_type_vars env next  in
                         FStar_List.append uu____1085 uu____1088  in
                       FStar_List.append uu____1079 uu____1082) steps
               in
            FStar_List.append uu____1061 uu____1064  in
          FStar_List.append uu____1055 uu____1058
      | FStar_Parser_AST.Abs uu____1091 -> []
      | FStar_Parser_AST.Let uu____1098 -> []
      | FStar_Parser_AST.LetOpen uu____1119 -> []
      | FStar_Parser_AST.If uu____1124 -> []
      | FStar_Parser_AST.QForall uu____1131 -> []
      | FStar_Parser_AST.QExists uu____1144 -> []
      | FStar_Parser_AST.Record uu____1157 -> []
      | FStar_Parser_AST.Match uu____1170 -> []
      | FStar_Parser_AST.TryWith uu____1185 -> []
      | FStar_Parser_AST.Bind uu____1200 -> []
      | FStar_Parser_AST.Quote uu____1207 -> []
      | FStar_Parser_AST.VQuote uu____1212 -> []
      | FStar_Parser_AST.Antiquote uu____1213 -> []
      | FStar_Parser_AST.Seq uu____1214 -> []

let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun t  ->
    let rec aux args t1 =
      let uu____1268 =
        let uu____1269 = unparen t1  in uu____1269.FStar_Parser_AST.tm  in
      match uu____1268 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____1311 -> (t1, args)  in
    aux [] t
  
let (close :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____1336 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1336  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1358 =
                     let uu____1359 =
                       let uu____1364 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____1364)  in
                     FStar_Parser_AST.TAnnotated uu____1359  in
                   FStar_Parser_AST.mk_binder uu____1358
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
        let uu____1382 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1382  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1404 =
                     let uu____1405 =
                       let uu____1410 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____1410)  in
                     FStar_Parser_AST.TAnnotated uu____1405  in
                   FStar_Parser_AST.mk_binder uu____1404
                     x.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____1412 =
             let uu____1413 = unparen t  in uu____1413.FStar_Parser_AST.tm
              in
           match uu____1412 with
           | FStar_Parser_AST.Product uu____1414 -> t
           | uu____1421 ->
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
      (FStar_Parser_AST.binder Prims.list * FStar_Parser_AST.term))
  =
  fun bs  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (binders,t1) ->
          uncurry (FStar_List.append bs binders) t1
      | uu____1458 -> (bs, t)
  
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild uu____1469 -> true
    | FStar_Parser_AST.PatTvar (uu____1473,uu____1474) -> true
    | FStar_Parser_AST.PatVar (uu____1480,uu____1481) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____1488) -> is_var_pattern p1
    | uu____1501 -> false
  
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____1512) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____1525;
           FStar_Parser_AST.prange = uu____1526;_},uu____1527)
        -> true
    | uu____1539 -> false
  
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
    | uu____1555 -> p
  
let rec (destruct_app_pattern :
  FStar_Syntax_DsEnv.env ->
    Prims.bool ->
      FStar_Parser_AST.pattern ->
        ((FStar_Ident.ident,FStar_Ident.lident) FStar_Util.either *
          FStar_Parser_AST.pattern Prims.list * (FStar_Parser_AST.term *
          FStar_Parser_AST.term FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.option))
  =
  fun env  ->
    fun is_top_level1  ->
      fun p  ->
        match p.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatAscribed (p1,t) ->
            let uu____1628 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____1628 with
             | (name,args,uu____1671) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1721);
               FStar_Parser_AST.prange = uu____1722;_},args)
            when is_top_level1 ->
            let uu____1732 =
              let uu____1737 = FStar_Syntax_DsEnv.qualify env id1  in
              FStar_Util.Inr uu____1737  in
            (uu____1732, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1759);
               FStar_Parser_AST.prange = uu____1760;_},args)
            -> ((FStar_Util.Inl id1), args, FStar_Pervasives_Native.None)
        | uu____1790 -> failwith "Not an app pattern"
  
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
        | FStar_Parser_AST.PatWild uu____1849 -> acc
        | FStar_Parser_AST.PatName uu____1852 -> acc
        | FStar_Parser_AST.PatOp uu____1853 -> acc
        | FStar_Parser_AST.PatConst uu____1854 ->
            if fail_on_patconst
            then
              FStar_Errors.raise_error
                (FStar_Errors.Error_CannotRedefineConst,
                  "Constants cannot be redefined") p.FStar_Parser_AST.prange
            else acc
        | FStar_Parser_AST.PatApp (phead,pats) ->
            gather_pattern_bound_vars_from_list (phead :: pats)
        | FStar_Parser_AST.PatTvar (x,uu____1871) -> FStar_Util.set_add x acc
        | FStar_Parser_AST.PatVar (x,uu____1877) -> FStar_Util.set_add x acc
        | FStar_Parser_AST.PatList pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatTuple (pats,uu____1886) ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatOr pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatRecord guarded_pats ->
            let uu____1903 =
              FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
            gather_pattern_bound_vars_from_list uu____1903
        | FStar_Parser_AST.PatAscribed (pat,uu____1911) ->
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
  | LocalBinder of (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) 
  | LetBinder of (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)) 
let (uu___is_LocalBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LocalBinder _0 -> true | uu____1993 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____2035 -> false
  
let (__proj__LetBinder__item___0 :
  bnd ->
    (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)))
  = fun projectee  -> match projectee with | LetBinder _0 -> _0 
let (binder_of_bnd :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun uu___4_2084  ->
    match uu___4_2084 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____2091 -> failwith "Impossible"
  
type env_t = FStar_Syntax_DsEnv.env
type lenv_t = FStar_Syntax_Syntax.bv Prims.list
let (mk_lb :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list *
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Range.range)
    -> FStar_Syntax_Syntax.letbinding)
  =
  fun uu____2126  ->
    match uu____2126 with
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
      let uu____2208 =
        let uu____2225 =
          let uu____2228 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____2228  in
        let uu____2229 =
          let uu____2240 =
            let uu____2249 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2249)  in
          [uu____2240]  in
        (uu____2225, uu____2229)  in
      FStar_Syntax_Syntax.Tm_app uu____2208  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____2298 =
        let uu____2315 =
          let uu____2318 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____2318  in
        let uu____2319 =
          let uu____2330 =
            let uu____2339 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2339)  in
          [uu____2330]  in
        (uu____2315, uu____2319)  in
      FStar_Syntax_Syntax.Tm_app uu____2298  in
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
          let uu____2402 =
            let uu____2419 =
              let uu____2422 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____2422  in
            let uu____2423 =
              let uu____2434 =
                let uu____2443 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____2443)  in
              let uu____2451 =
                let uu____2462 =
                  let uu____2471 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____2471)  in
                [uu____2462]  in
              uu____2434 :: uu____2451  in
            (uu____2419, uu____2423)  in
          FStar_Syntax_Syntax.Tm_app uu____2402  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let (generalize_annotated_univs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun s  ->
    let bs_univnames bs =
      let uu____2531 =
        let uu____2546 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____2565  ->
               match uu____2565 with
               | ({ FStar_Syntax_Syntax.ppname = uu____2576;
                    FStar_Syntax_Syntax.index = uu____2577;
                    FStar_Syntax_Syntax.sort = t;_},uu____2579)
                   ->
                   let uu____2587 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____2587) uu____2546
         in
      FStar_All.pipe_right bs uu____2531  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____2603 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____2621 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____2649 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____2670,uu____2671,bs,t,uu____2674,uu____2675)
                            ->
                            let uu____2684 = bs_univnames bs  in
                            let uu____2687 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____2684 uu____2687
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____2690,uu____2691,t,uu____2693,uu____2694,uu____2695)
                            -> FStar_Syntax_Free.univnames t
                        | uu____2702 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____2649 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___33_2711 = s  in
        let uu____2712 =
          let uu____2713 =
            let uu____2722 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____2740,bs,t,lids1,lids2) ->
                          let uu___34_2753 = se  in
                          let uu____2754 =
                            let uu____2755 =
                              let uu____2772 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____2773 =
                                let uu____2774 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____2774 t  in
                              (lid, uvs, uu____2772, uu____2773, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____2755
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____2754;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___34_2753.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___34_2753.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___34_2753.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___34_2753.FStar_Syntax_Syntax.sigattrs)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____2788,t,tlid,n1,lids1) ->
                          let uu___35_2799 = se  in
                          let uu____2800 =
                            let uu____2801 =
                              let uu____2817 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____2817, tlid, n1, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____2801  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____2800;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___35_2799.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___35_2799.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___35_2799.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___35_2799.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____2821 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____2722, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____2713  in
        {
          FStar_Syntax_Syntax.sigel = uu____2712;
          FStar_Syntax_Syntax.sigrng =
            (uu___33_2711.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___33_2711.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___33_2711.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___33_2711.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2828,t) ->
        let uvs =
          let uu____2831 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____2831 FStar_Util.set_elements  in
        let uu___36_2836 = s  in
        let uu____2837 =
          let uu____2838 =
            let uu____2845 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____2845)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____2838  in
        {
          FStar_Syntax_Syntax.sigel = uu____2837;
          FStar_Syntax_Syntax.sigrng =
            (uu___36_2836.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___36_2836.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___36_2836.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___36_2836.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____2869 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____2872 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____2879) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____2912,(FStar_Util.Inl t,uu____2914),uu____2915)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____2962,(FStar_Util.Inr c,uu____2964),uu____2965)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____3012 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____3013,(FStar_Util.Inl t,uu____3015),uu____3016) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____3063,(FStar_Util.Inr c,uu____3065),uu____3066) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____3113 -> empty_set  in
          FStar_Util.set_union uu____2869 uu____2872  in
        let all_lb_univs =
          let uu____3117 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____3133 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____3133) empty_set)
             in
          FStar_All.pipe_right uu____3117 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___37_3143 = s  in
        let uu____3144 =
          let uu____3145 =
            let uu____3152 =
              let uu____3153 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___38_3165 = lb  in
                        let uu____3166 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____3169 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___38_3165.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____3166;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___38_3165.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____3169;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___38_3165.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___38_3165.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____3153)  in
            (uu____3152, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____3145  in
        {
          FStar_Syntax_Syntax.sigel = uu____3144;
          FStar_Syntax_Syntax.sigrng =
            (uu___37_3143.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___37_3143.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___37_3143.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___37_3143.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____3178,fml) ->
        let uvs =
          let uu____3181 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____3181 FStar_Util.set_elements  in
        let uu___39_3186 = s  in
        let uu____3187 =
          let uu____3188 =
            let uu____3195 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____3195)  in
          FStar_Syntax_Syntax.Sig_assume uu____3188  in
        {
          FStar_Syntax_Syntax.sigel = uu____3187;
          FStar_Syntax_Syntax.sigrng =
            (uu___39_3186.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___39_3186.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___39_3186.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___39_3186.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____3197,bs,c,flags1) ->
        let uvs =
          let uu____3206 =
            let uu____3209 = bs_univnames bs  in
            let uu____3212 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____3209 uu____3212  in
          FStar_All.pipe_right uu____3206 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___40_3220 = s  in
        let uu____3221 =
          let uu____3222 =
            let uu____3235 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____3236 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____3235, uu____3236, flags1)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____3222  in
        {
          FStar_Syntax_Syntax.sigel = uu____3221;
          FStar_Syntax_Syntax.sigrng =
            (uu___40_3220.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___40_3220.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___40_3220.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___40_3220.FStar_Syntax_Syntax.sigattrs)
        }
    | uu____3239 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___5_3247  ->
    match uu___5_3247 with
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
    | uu____3298 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____3319 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____3319)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____3345 =
      let uu____3346 = unparen t  in uu____3346.FStar_Parser_AST.tm  in
    match uu____3345 with
    | FStar_Parser_AST.Wild  ->
        let uu____3352 =
          let uu____3353 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____3353  in
        FStar_Util.Inr uu____3352
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____3366)) ->
        let n1 = FStar_Util.int_of_string repr  in
        (if n1 < (Prims.parse_int "0")
         then
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_NegativeUniverseConstFatal_NotSupported,
               (Prims.op_Hat
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
             let uu____3457 = sum_to_universe u n1  in
             FStar_Util.Inr uu____3457
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____3474 = sum_to_universe u n1  in
             FStar_Util.Inr uu____3474
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____3490 =
               let uu____3496 =
                 let uu____3498 = FStar_Parser_AST.term_to_string t  in
                 Prims.op_Hat
                   "This universe might contain a sum of two universe variables "
                   uu____3498
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____3496)
                in
             FStar_Errors.raise_error uu____3490 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____3507 ->
        let rec aux t1 univargs =
          let uu____3544 =
            let uu____3545 = unparen t1  in uu____3545.FStar_Parser_AST.tm
             in
          match uu____3544 with
          | FStar_Parser_AST.App (t2,targ,uu____3553) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___6_3580  ->
                     match uu___6_3580 with
                     | FStar_Util.Inr uu____3587 -> true
                     | uu____3590 -> false) univargs
              then
                let uu____3598 =
                  let uu____3599 =
                    FStar_List.map
                      (fun uu___7_3609  ->
                         match uu___7_3609 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____3599  in
                FStar_Util.Inr uu____3598
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___8_3635  ->
                        match uu___8_3635 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____3645 -> failwith "impossible")
                     univargs
                    in
                 let uu____3649 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____3649)
          | uu____3665 ->
              let uu____3666 =
                let uu____3672 =
                  let uu____3674 =
                    let uu____3676 = FStar_Parser_AST.term_to_string t1  in
                    Prims.op_Hat uu____3676 " in universe context"  in
                  Prims.op_Hat "Unexpected term " uu____3674  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3672)  in
              FStar_Errors.raise_error uu____3666 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____3691 ->
        let uu____3692 =
          let uu____3698 =
            let uu____3700 =
              let uu____3702 = FStar_Parser_AST.term_to_string t  in
              Prims.op_Hat uu____3702 " in universe context"  in
            Prims.op_Hat "Unexpected term " uu____3700  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3698)  in
        FStar_Errors.raise_error uu____3692 t.FStar_Parser_AST.range
  
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
                   FStar_Syntax_Syntax.antiquotes = uu____3743;_});
            FStar_Syntax_Syntax.pos = uu____3744;
            FStar_Syntax_Syntax.vars = uu____3745;_})::uu____3746
        ->
        let uu____3777 =
          let uu____3783 =
            let uu____3785 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____3785
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____3783)  in
        FStar_Errors.raise_error uu____3777 e.FStar_Syntax_Syntax.pos
    | (bv,e)::uu____3791 ->
        let uu____3810 =
          let uu____3816 =
            let uu____3818 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____3818
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____3816)  in
        FStar_Errors.raise_error uu____3810 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'Auu____3831 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident * 'Auu____3831) Prims.list ->
        FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____3859 = FStar_List.hd fields  in
        match uu____3859 with
        | (f,uu____3869) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____3881 =
                match uu____3881 with
                | (f',uu____3887) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____3889 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____3889
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
              (let uu____3899 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____3899);
              (match () with | () -> record)))
  
let rec (desugar_data_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern -> (env_t * bnd * annotated_pat Prims.list))
  =
  fun env  ->
    fun p  ->
      let check_linear_pattern_variables pats r =
        let rec pat_vars p1 =
          match p1.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_dot_term uu____4291 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_wild uu____4298 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_constant uu____4299 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_var x ->
              FStar_Util.set_add x FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_cons (uu____4301,pats1) ->
              let aux out uu____4342 =
                match uu____4342 with
                | (p2,uu____4355) ->
                    let intersection =
                      let uu____4365 = pat_vars p2  in
                      FStar_Util.set_intersect uu____4365 out  in
                    let uu____4368 = FStar_Util.set_is_empty intersection  in
                    if uu____4368
                    then
                      let uu____4373 = pat_vars p2  in
                      FStar_Util.set_union out uu____4373
                    else
                      (let duplicate_bv =
                         let uu____4379 =
                           FStar_Util.set_elements intersection  in
                         FStar_List.hd uu____4379  in
                       let uu____4382 =
                         let uu____4388 =
                           FStar_Util.format1
                             "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                             (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                            in
                         (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                           uu____4388)
                          in
                       FStar_Errors.raise_error uu____4382 r)
                 in
              FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
           in
        match pats with
        | [] -> ()
        | p1::[] ->
            let uu____4412 = pat_vars p1  in
            FStar_All.pipe_right uu____4412 (fun a1  -> ())
        | p1::ps ->
            let pvars = pat_vars p1  in
            let aux p2 =
              let uu____4440 =
                let uu____4442 = pat_vars p2  in
                FStar_Util.set_eq pvars uu____4442  in
              if uu____4440
              then ()
              else
                (let nonlinear_vars =
                   let uu____4451 = pat_vars p2  in
                   FStar_Util.set_symmetric_difference pvars uu____4451  in
                 let first_nonlinear_var =
                   let uu____4455 = FStar_Util.set_elements nonlinear_vars
                      in
                   FStar_List.hd uu____4455  in
                 let uu____4458 =
                   let uu____4464 =
                     FStar_Util.format1
                       "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                       (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                      in
                   (FStar_Errors.Fatal_IncoherentPatterns, uu____4464)  in
                 FStar_Errors.raise_error uu____4458 r)
               in
            FStar_List.iter aux ps
         in
      let resolvex l e x =
        let uu____4492 =
          FStar_All.pipe_right l
            (FStar_Util.find_opt
               (fun y  ->
                  (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                    x.FStar_Ident.idText))
           in
        match uu____4492 with
        | FStar_Pervasives_Native.Some y -> (l, e, y)
        | uu____4509 ->
            let uu____4512 = FStar_Syntax_DsEnv.push_bv e x  in
            (match uu____4512 with | (e1,x1) -> ((x1 :: l), e1, x1))
         in
      let rec aux' top loc env1 p1 =
        let pos q = FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange
           in
        let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
        let orig = p1  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr uu____4663 -> failwith "impossible"
        | FStar_Parser_AST.PatOp op ->
            let uu____4687 =
              let uu____4688 =
                let uu____4689 =
                  let uu____4696 =
                    let uu____4697 =
                      let uu____4703 =
                        FStar_Parser_AST.compile_op (Prims.parse_int "0")
                          op.FStar_Ident.idText op.FStar_Ident.idRange
                         in
                      (uu____4703, (op.FStar_Ident.idRange))  in
                    FStar_Ident.mk_ident uu____4697  in
                  (uu____4696, FStar_Pervasives_Native.None)  in
                FStar_Parser_AST.PatVar uu____4689  in
              {
                FStar_Parser_AST.pat = uu____4688;
                FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
              }  in
            aux loc env1 uu____4687
        | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
            ((match tacopt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some uu____4723 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                      "Type ascriptions within patterns cannot be associated with a tactic")
                    orig.FStar_Parser_AST.prange);
             (let uu____4726 = aux loc env1 p2  in
              match uu____4726 with
              | (loc1,env',binder,p3,annots,imp) ->
                  let annot_pat_var p4 t1 =
                    match p4.FStar_Syntax_Syntax.v with
                    | FStar_Syntax_Syntax.Pat_var x ->
                        let uu___41_4815 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_var
                               (let uu___42_4820 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___42_4820.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___42_4820.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___41_4815.FStar_Syntax_Syntax.p)
                        }
                    | FStar_Syntax_Syntax.Pat_wild x ->
                        let uu___43_4822 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_wild
                               (let uu___44_4827 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___44_4827.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___44_4827.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___43_4822.FStar_Syntax_Syntax.p)
                        }
                    | uu____4828 when top -> p4
                    | uu____4829 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                            "Type ascriptions within patterns are only allowed on variables")
                          orig.FStar_Parser_AST.prange
                     in
                  let uu____4834 =
                    match binder with
                    | LetBinder uu____4855 -> failwith "impossible"
                    | LocalBinder (x,aq) ->
                        let t1 =
                          let uu____4880 = close_fun env1 t  in
                          desugar_term env1 uu____4880  in
                        let x1 =
                          let uu___45_4882 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___45_4882.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___45_4882.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t1
                          }  in
                        ([(x1, t1)], (LocalBinder (x1, aq)))
                     in
                  (match uu____4834 with
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
            let uu____4950 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
            (loc, env1, (LocalBinder (x, aq1)), uu____4950, [], imp)
        | FStar_Parser_AST.PatConst c ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                FStar_Syntax_Syntax.tun
               in
            let uu____4964 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____4964, [], false)
        | FStar_Parser_AST.PatTvar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____4988 = resolvex loc env1 x  in
            (match uu____4988 with
             | (loc1,env2,xbv) ->
                 let uu____5017 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____5017, [], imp))
        | FStar_Parser_AST.PatVar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____5040 = resolvex loc env1 x  in
            (match uu____5040 with
             | (loc1,env2,xbv) ->
                 let uu____5069 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____5069, [], imp))
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
            let uu____5084 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (l1, []))
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____5084, [], false)
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
               FStar_Parser_AST.prange = uu____5114;_},args)
            ->
            let uu____5120 =
              FStar_List.fold_right
                (fun arg  ->
                   fun uu____5181  ->
                     match uu____5181 with
                     | (loc1,env2,annots,args1) ->
                         let uu____5262 = aux loc1 env2 arg  in
                         (match uu____5262 with
                          | (loc2,env3,uu____5309,arg1,ans,imp) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((arg1, imp) :: args1)))) args
                (loc, env1, [], [])
               in
            (match uu____5120 with
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
                 let uu____5441 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____5441, annots, false))
        | FStar_Parser_AST.PatApp uu____5459 ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
              p1.FStar_Parser_AST.prange
        | FStar_Parser_AST.PatList pats ->
            let uu____5490 =
              FStar_List.fold_right
                (fun pat  ->
                   fun uu____5541  ->
                     match uu____5541 with
                     | (loc1,env2,annots,pats1) ->
                         let uu____5602 = aux loc1 env2 pat  in
                         (match uu____5602 with
                          | (loc2,env3,uu____5644,pat1,ans,uu____5647) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                (pat1 :: pats1)))) pats (loc, env1, [], [])
               in
            (match uu____5490 with
             | (loc1,env2,annots,pats1) ->
                 let pat =
                   let uu____5744 =
                     let uu____5747 =
                       let uu____5754 =
                         FStar_Range.end_range p1.FStar_Parser_AST.prange  in
                       pos_r uu____5754  in
                     let uu____5755 =
                       let uu____5756 =
                         let uu____5770 =
                           FStar_Syntax_Syntax.lid_as_fv
                             FStar_Parser_Const.nil_lid
                             FStar_Syntax_Syntax.delta_constant
                             (FStar_Pervasives_Native.Some
                                FStar_Syntax_Syntax.Data_ctor)
                            in
                         (uu____5770, [])  in
                       FStar_Syntax_Syntax.Pat_cons uu____5756  in
                     FStar_All.pipe_left uu____5747 uu____5755  in
                   FStar_List.fold_right
                     (fun hd1  ->
                        fun tl1  ->
                          let r =
                            FStar_Range.union_ranges
                              hd1.FStar_Syntax_Syntax.p
                              tl1.FStar_Syntax_Syntax.p
                             in
                          let uu____5804 =
                            let uu____5805 =
                              let uu____5819 =
                                FStar_Syntax_Syntax.lid_as_fv
                                  FStar_Parser_Const.cons_lid
                                  FStar_Syntax_Syntax.delta_constant
                                  (FStar_Pervasives_Native.Some
                                     FStar_Syntax_Syntax.Data_ctor)
                                 in
                              (uu____5819, [(hd1, false); (tl1, false)])  in
                            FStar_Syntax_Syntax.Pat_cons uu____5805  in
                          FStar_All.pipe_left (pos_r r) uu____5804) pats1
                     uu____5744
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
            let uu____5877 =
              FStar_List.fold_left
                (fun uu____5937  ->
                   fun p2  ->
                     match uu____5937 with
                     | (loc1,env2,annots,pats) ->
                         let uu____6019 = aux loc1 env2 p2  in
                         (match uu____6019 with
                          | (loc2,env3,uu____6066,pat,ans,uu____6069) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((pat, false) :: pats)))) (loc, env1, [], [])
                args
               in
            (match uu____5877 with
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
                   | uu____6235 -> failwith "impossible"  in
                 let x =
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some
                        (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun
                    in
                 let uu____6238 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____6238, annots, false))
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
                   (fun uu____6319  ->
                      match uu____6319 with
                      | (f,p2) -> ((f.FStar_Ident.ident), p2)))
               in
            let args =
              FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                (FStar_List.map
                   (fun uu____6349  ->
                      match uu____6349 with
                      | (f,uu____6355) ->
                          let uu____6356 =
                            FStar_All.pipe_right fields1
                              (FStar_List.tryFind
                                 (fun uu____6382  ->
                                    match uu____6382 with
                                    | (g,uu____6389) ->
                                        f.FStar_Ident.idText =
                                          g.FStar_Ident.idText))
                             in
                          (match uu____6356 with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatWild
                                    FStar_Pervasives_Native.None)
                                 p1.FStar_Parser_AST.prange
                           | FStar_Pervasives_Native.Some (uu____6395,p2) ->
                               p2)))
               in
            let app =
              let uu____6402 =
                let uu____6403 =
                  let uu____6410 =
                    let uu____6411 =
                      let uu____6412 =
                        FStar_Ident.lid_of_ids
                          (FStar_List.append
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                             [record.FStar_Syntax_DsEnv.constrname])
                         in
                      FStar_Parser_AST.PatName uu____6412  in
                    FStar_Parser_AST.mk_pattern uu____6411
                      p1.FStar_Parser_AST.prange
                     in
                  (uu____6410, args)  in
                FStar_Parser_AST.PatApp uu____6403  in
              FStar_Parser_AST.mk_pattern uu____6402
                p1.FStar_Parser_AST.prange
               in
            let uu____6415 = aux loc env1 app  in
            (match uu____6415 with
             | (env2,e,b,p2,annots,uu____6461) ->
                 let p3 =
                   match p2.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                       let uu____6501 =
                         let uu____6502 =
                           let uu____6516 =
                             let uu___46_6517 = fv  in
                             let uu____6518 =
                               let uu____6521 =
                                 let uu____6522 =
                                   let uu____6529 =
                                     FStar_All.pipe_right
                                       record.FStar_Syntax_DsEnv.fields
                                       (FStar_List.map
                                          FStar_Pervasives_Native.fst)
                                      in
                                   ((record.FStar_Syntax_DsEnv.typename),
                                     uu____6529)
                                    in
                                 FStar_Syntax_Syntax.Record_ctor uu____6522
                                  in
                               FStar_Pervasives_Native.Some uu____6521  in
                             {
                               FStar_Syntax_Syntax.fv_name =
                                 (uu___46_6517.FStar_Syntax_Syntax.fv_name);
                               FStar_Syntax_Syntax.fv_delta =
                                 (uu___46_6517.FStar_Syntax_Syntax.fv_delta);
                               FStar_Syntax_Syntax.fv_qual = uu____6518
                             }  in
                           (uu____6516, args1)  in
                         FStar_Syntax_Syntax.Pat_cons uu____6502  in
                       FStar_All.pipe_left pos uu____6501
                   | uu____6555 -> p2  in
                 (env2, e, b, p3, annots, false))
      
      and aux loc env1 p1 = aux' false loc env1 p1
       in
      let aux_maybe_or env1 p1 =
        let loc = []  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr [] -> failwith "impossible"
        | FStar_Parser_AST.PatOr (p2::ps) ->
            let uu____6641 = aux' true loc env1 p2  in
            (match uu____6641 with
             | (loc1,env2,var,p3,ans,uu____6685) ->
                 let uu____6700 =
                   FStar_List.fold_left
                     (fun uu____6749  ->
                        fun p4  ->
                          match uu____6749 with
                          | (loc2,env3,ps1) ->
                              let uu____6814 = aux' true loc2 env3 p4  in
                              (match uu____6814 with
                               | (loc3,env4,uu____6855,p5,ans1,uu____6858) ->
                                   (loc3, env4, ((p5, ans1) :: ps1))))
                     (loc1, env2, []) ps
                    in
                 (match uu____6700 with
                  | (loc2,env3,ps1) ->
                      let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                      (env3, var, pats)))
        | uu____7019 ->
            let uu____7020 = aux' true loc env1 p1  in
            (match uu____7020 with
             | (loc1,env2,vars,pat,ans,b) -> (env2, vars, [(pat, ans)]))
         in
      let uu____7117 = aux_maybe_or env p  in
      match uu____7117 with
      | (env1,b,pats) ->
          ((let uu____7172 = FStar_List.map FStar_Pervasives_Native.fst pats
               in
            check_linear_pattern_variables uu____7172
              p.FStar_Parser_AST.prange);
           (env1, b, pats))

and (desugar_binding_pat_maybe_top :
  Prims.bool ->
    FStar_Syntax_DsEnv.env ->
      FStar_Parser_AST.pattern -> (env_t * bnd * annotated_pat Prims.list))
  =
  fun top  ->
    fun env  ->
      fun p  ->
        let mklet x ty tacopt =
          let uu____7245 =
            let uu____7246 =
              let uu____7257 = FStar_Syntax_DsEnv.qualify env x  in
              (uu____7257, (ty, tacopt))  in
            LetBinder uu____7246  in
          (env, uu____7245, [])  in
        let op_to_ident x =
          let uu____7274 =
            let uu____7280 =
              FStar_Parser_AST.compile_op (Prims.parse_int "0")
                x.FStar_Ident.idText x.FStar_Ident.idRange
               in
            (uu____7280, (x.FStar_Ident.idRange))  in
          FStar_Ident.mk_ident uu____7274  in
        if top
        then
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu____7302 = op_to_ident x  in
              mklet uu____7302 FStar_Syntax_Syntax.tun
                FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x,uu____7304) ->
              mklet x FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu____7310;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7326 = op_to_ident x  in
              let uu____7327 = desugar_term env t  in
              mklet uu____7326 uu____7327 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____7329);
                 FStar_Parser_AST.prange = uu____7330;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7350 = desugar_term env t  in
              mklet x uu____7350 tacopt1
          | uu____7351 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu____7364 = desugar_data_pat env p  in
           match uu____7364 with
           | (env1,binder,p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu____7393;
                      FStar_Syntax_Syntax.p = uu____7394;_},uu____7395)::[]
                     -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu____7408;
                      FStar_Syntax_Syntax.p = uu____7409;_},uu____7410)::[]
                     -> []
                 | uu____7423 -> p1  in
               (env1, binder, p2))

and (desugar_binding_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern -> (env_t * bnd * annotated_pat Prims.list))
  = fun env  -> fun p  -> desugar_binding_pat_maybe_top false env p

and (desugar_match_pat_maybe_top :
  Prims.bool ->
    FStar_Syntax_DsEnv.env ->
      FStar_Parser_AST.pattern -> (env_t * annotated_pat Prims.list))
  =
  fun uu____7431  ->
    fun env  ->
      fun pat  ->
        let uu____7435 = desugar_data_pat env pat  in
        match uu____7435 with | (env1,uu____7451,pat1) -> (env1, pat1)

and (desugar_match_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern -> (env_t * annotated_pat Prims.list))
  = fun env  -> fun p  -> desugar_match_pat_maybe_top false env p

and (desugar_term_aq :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.antiquotations))
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
      let uu____7473 = desugar_term_aq env e  in
      match uu____7473 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_typ_aq :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.antiquotations))
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
      let uu____7492 = desugar_typ_aq env e  in
      match uu____7492 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness * FStar_Const.width) ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____7502  ->
        fun range  ->
          match uu____7502 with
          | (signedness,width) ->
              let tnm =
                Prims.op_Hat "FStar."
                  (Prims.op_Hat
                     (match signedness with
                      | FStar_Const.Unsigned  -> "U"
                      | FStar_Const.Signed  -> "")
                     (Prims.op_Hat "Int"
                        (match width with
                         | FStar_Const.Int8  -> "8"
                         | FStar_Const.Int16  -> "16"
                         | FStar_Const.Int32  -> "32"
                         | FStar_Const.Int64  -> "64")))
                 in
              ((let uu____7524 =
                  let uu____7526 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____7526  in
                if uu____7524
                then
                  let uu____7529 =
                    let uu____7535 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____7535)  in
                  FStar_Errors.log_issue range uu____7529
                else ());
               (let private_intro_nm =
                  Prims.op_Hat tnm
                    (Prims.op_Hat ".__"
                       (Prims.op_Hat
                          (match signedness with
                           | FStar_Const.Unsigned  -> "u"
                           | FStar_Const.Signed  -> "") "int_to_t"))
                   in
                let intro_nm =
                  Prims.op_Hat tnm
                    (Prims.op_Hat "."
                       (Prims.op_Hat
                          (match signedness with
                           | FStar_Const.Unsigned  -> "u"
                           | FStar_Const.Signed  -> "") "int_to_t"))
                   in
                let lid =
                  let uu____7556 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____7556 range  in
                let lid1 =
                  let uu____7560 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____7560 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____7570 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____7570 range  in
                           let private_fv =
                             let uu____7572 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____7572 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___47_7573 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___47_7573.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___47_7573.FStar_Syntax_Syntax.vars)
                           }
                       | uu____7574 ->
                           failwith
                             (Prims.op_Hat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____7578 =
                        let uu____7584 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____7584)
                         in
                      FStar_Errors.raise_error uu____7578 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____7604 =
                  let uu____7611 =
                    let uu____7612 =
                      let uu____7629 =
                        let uu____7640 =
                          let uu____7649 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____7649)  in
                        [uu____7640]  in
                      (lid1, uu____7629)  in
                    FStar_Syntax_Syntax.Tm_app uu____7612  in
                  FStar_Syntax_Syntax.mk uu____7611  in
                uu____7604 FStar_Pervasives_Native.None range))

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
            let uu____7700 =
              let uu____7707 =
                (if resolve
                 then FStar_Syntax_DsEnv.try_lookup_lid_with_attributes
                 else
                   FStar_Syntax_DsEnv.try_lookup_lid_with_attributes_no_resolve)
                  env
                 in
              FStar_Syntax_DsEnv.fail_or env uu____7707 l  in
            match uu____7700 with
            | (tm,attrs) ->
                let warn_if_deprecated attrs1 =
                  FStar_List.iter
                    (fun a  ->
                       match a.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_app
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____7759;
                              FStar_Syntax_Syntax.vars = uu____7760;_},args)
                           when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____7788 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.op_Hat uu____7788 " is deprecated"  in
                           let msg1 =
                             if
                               (FStar_List.length args) >
                                 (Prims.parse_int "0")
                             then
                               let uu____7804 =
                                 let uu____7805 =
                                   let uu____7808 = FStar_List.hd args  in
                                   FStar_Pervasives_Native.fst uu____7808  in
                                 uu____7805.FStar_Syntax_Syntax.n  in
                               match uu____7804 with
                               | FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_string (s,uu____7831))
                                   when
                                   Prims.op_Negation
                                     ((FStar_Util.trim_string s) = "")
                                   ->
                                   Prims.op_Hat msg
                                     (Prims.op_Hat ", use "
                                        (Prims.op_Hat s " instead"))
                               | uu____7838 -> msg
                             else msg  in
                           let uu____7841 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____7841
                             (FStar_Errors.Warning_DeprecatedDefinition,
                               msg1)
                       | FStar_Syntax_Syntax.Tm_fvar fv when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____7846 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.op_Hat uu____7846 " is deprecated"  in
                           let uu____7849 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____7849
                             (FStar_Errors.Warning_DeprecatedDefinition, msg)
                       | uu____7851 -> ()) attrs1
                   in
                (warn_if_deprecated attrs; (let tm1 = setpos tm  in tm1))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____7866 =
          let uu____7867 = unparen t  in uu____7867.FStar_Parser_AST.tm  in
        match uu____7866 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____7868; FStar_Ident.ident = uu____7869;
              FStar_Ident.nsstr = uu____7870; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____7875 ->
            let uu____7876 =
              let uu____7882 =
                let uu____7884 = FStar_Parser_AST.term_to_string t  in
                Prims.op_Hat "Unknown attribute " uu____7884  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____7882)  in
            FStar_Errors.raise_error uu____7876 t.FStar_Parser_AST.range
         in
      FStar_List.map desugar_attribute cattributes

and (desugar_term_maybe_top :
  Prims.bool ->
    env_t ->
      FStar_Parser_AST.term ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.antiquotations))
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
          let uu___48_7971 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___48_7971.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___48_7971.FStar_Syntax_Syntax.vars)
          }  in
        let uu____7974 =
          let uu____7975 = unparen top  in uu____7975.FStar_Parser_AST.tm  in
        match uu____7974 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____7980 ->
            let uu____7989 = desugar_formula env top  in (uu____7989, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____7998 = desugar_formula env t  in (uu____7998, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____8007 = desugar_formula env t  in (uu____8007, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____8034 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____8034, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____8036 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____8036, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____8045 =
                let uu____8046 =
                  let uu____8053 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____8053, args)  in
                FStar_Parser_AST.Op uu____8046  in
              FStar_Parser_AST.mk_term uu____8045 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____8058 =
              let uu____8059 =
                let uu____8060 =
                  let uu____8067 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____8067, [e])  in
                FStar_Parser_AST.Op uu____8060  in
              FStar_Parser_AST.mk_term uu____8059 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____8058
        | FStar_Parser_AST.Op (op_star,lhs::rhs::[]) when
            (let uu____8079 = FStar_Ident.text_of_id op_star  in
             uu____8079 = "*") &&
              (let uu____8084 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____8084 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____8101;_},t1::t2::[])
                  when
                  let uu____8107 =
                    op_as_term env (Prims.parse_int "2")
                      top.FStar_Parser_AST.range op_star
                     in
                  FStar_All.pipe_right uu____8107 FStar_Option.isNone ->
                  let uu____8114 = flatten1 t1  in
                  FStar_List.append uu____8114 [t2]
              | uu____8117 -> [t]  in
            let terms = flatten1 lhs  in
            let t =
              let uu___49_8122 = top  in
              let uu____8123 =
                let uu____8124 =
                  let uu____8135 =
                    FStar_List.map (fun _0_1  -> FStar_Util.Inr _0_1) terms
                     in
                  (uu____8135, rhs)  in
                FStar_Parser_AST.Sum uu____8124  in
              {
                FStar_Parser_AST.tm = uu____8123;
                FStar_Parser_AST.range =
                  (uu___49_8122.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___49_8122.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env t
        | FStar_Parser_AST.Tvar a ->
            let uu____8153 =
              let uu____8154 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_All.pipe_left setpos uu____8154  in
            (uu____8153, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____8160 =
              let uu____8166 =
                let uu____8168 =
                  let uu____8170 = FStar_Ident.text_of_id u  in
                  Prims.op_Hat uu____8170 " in non-universe context"  in
                Prims.op_Hat "Unexpected universe variable " uu____8168  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____8166)  in
            FStar_Errors.raise_error uu____8160 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____8185 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____8185 with
             | FStar_Pervasives_Native.None  ->
                 let uu____8192 =
                   let uu____8198 =
                     let uu____8200 = FStar_Ident.text_of_id s  in
                     Prims.op_Hat "Unexpected or unbound operator: "
                       uu____8200
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____8198)
                    in
                 FStar_Errors.raise_error uu____8192
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let uu____8215 =
                     let uu____8240 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____8302 = desugar_term_aq env t  in
                               match uu____8302 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____8240 FStar_List.unzip  in
                   (match uu____8215 with
                    | (args1,aqs) ->
                        let uu____8435 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____8435, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____8452)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____8469 =
              let uu___50_8470 = top  in
              let uu____8471 =
                let uu____8472 =
                  let uu____8479 =
                    let uu___51_8480 = top  in
                    let uu____8481 =
                      let uu____8482 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8482  in
                    {
                      FStar_Parser_AST.tm = uu____8481;
                      FStar_Parser_AST.range =
                        (uu___51_8480.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___51_8480.FStar_Parser_AST.level)
                    }  in
                  (uu____8479, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8472  in
              {
                FStar_Parser_AST.tm = uu____8471;
                FStar_Parser_AST.range =
                  (uu___50_8470.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___50_8470.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8469
        | FStar_Parser_AST.Construct (n1,(a,uu____8490)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____8510 =
                let uu___52_8511 = top  in
                let uu____8512 =
                  let uu____8513 =
                    let uu____8520 =
                      let uu___53_8521 = top  in
                      let uu____8522 =
                        let uu____8523 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____8523  in
                      {
                        FStar_Parser_AST.tm = uu____8522;
                        FStar_Parser_AST.range =
                          (uu___53_8521.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___53_8521.FStar_Parser_AST.level)
                      }  in
                    (uu____8520, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____8513  in
                {
                  FStar_Parser_AST.tm = uu____8512;
                  FStar_Parser_AST.range =
                    (uu___52_8511.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___52_8511.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____8510))
        | FStar_Parser_AST.Construct (n1,(a,uu____8531)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____8548 =
              let uu___54_8549 = top  in
              let uu____8550 =
                let uu____8551 =
                  let uu____8558 =
                    let uu___55_8559 = top  in
                    let uu____8560 =
                      let uu____8561 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8561  in
                    {
                      FStar_Parser_AST.tm = uu____8560;
                      FStar_Parser_AST.range =
                        (uu___55_8559.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___55_8559.FStar_Parser_AST.level)
                    }  in
                  (uu____8558, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8551  in
              {
                FStar_Parser_AST.tm = uu____8550;
                FStar_Parser_AST.range =
                  (uu___54_8549.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___54_8549.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8548
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8567; FStar_Ident.ident = uu____8568;
              FStar_Ident.nsstr = uu____8569; FStar_Ident.str = "Type0";_}
            ->
            let uu____8574 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____8574, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8575; FStar_Ident.ident = uu____8576;
              FStar_Ident.nsstr = uu____8577; FStar_Ident.str = "Type";_}
            ->
            let uu____8582 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____8582, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____8583; FStar_Ident.ident = uu____8584;
               FStar_Ident.nsstr = uu____8585; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____8605 =
              let uu____8606 =
                let uu____8607 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____8607  in
              mk1 uu____8606  in
            (uu____8605, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8608; FStar_Ident.ident = uu____8609;
              FStar_Ident.nsstr = uu____8610; FStar_Ident.str = "Effect";_}
            ->
            let uu____8615 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____8615, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8616; FStar_Ident.ident = uu____8617;
              FStar_Ident.nsstr = uu____8618; FStar_Ident.str = "True";_}
            ->
            let uu____8623 =
              let uu____8624 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8624
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8623, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8625; FStar_Ident.ident = uu____8626;
              FStar_Ident.nsstr = uu____8627; FStar_Ident.str = "False";_}
            ->
            let uu____8632 =
              let uu____8633 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8633
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8632, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____8636;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____8639 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____8639 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____8648 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_constant_at_level
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None
                     in
                  (uu____8648, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____8650 =
                    let uu____8652 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____8652 txt
                     in
                  failwith uu____8650))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8661 = desugar_name mk1 setpos env true l  in
              (uu____8661, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8665 = desugar_name mk1 setpos env true l  in
              (uu____8665, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____8678 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____8678 with
                | FStar_Pervasives_Native.Some uu____8688 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____8696 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____8696 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____8714 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____8735 =
                    let uu____8736 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____8736  in
                  (uu____8735, noaqs)
              | uu____8737 ->
                  let uu____8745 =
                    let uu____8751 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____8751)  in
                  FStar_Errors.raise_error uu____8745
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____8761 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____8761 with
              | FStar_Pervasives_Native.None  ->
                  let uu____8768 =
                    let uu____8774 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____8774)
                     in
                  FStar_Errors.raise_error uu____8768
                    top.FStar_Parser_AST.range
              | uu____8782 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____8786 = desugar_name mk1 setpos env true lid'  in
                  (uu____8786, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8803 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____8803 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____8822 ->
                       let uu____8829 =
                         FStar_Util.take
                           (fun uu____8853  ->
                              match uu____8853 with
                              | (uu____8859,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____8829 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____8904 =
                              let uu____8929 =
                                FStar_List.map
                                  (fun uu____8972  ->
                                     match uu____8972 with
                                     | (t,imp) ->
                                         let uu____8989 =
                                           desugar_term_aq env t  in
                                         (match uu____8989 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____8929
                                FStar_List.unzip
                               in
                            (match uu____8904 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____9132 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____9132, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____9151 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____9151 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.op_Hat "Constructor "
                             (Prims.op_Hat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____9162 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.op_Hat "Effect "
                             (Prims.op_Hat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) when
            FStar_Util.for_all
              (fun uu___9_9190  ->
                 match uu___9_9190 with
                 | FStar_Util.Inr uu____9196 -> true
                 | uu____9198 -> false) binders
            ->
            let terms =
              let uu____9207 =
                FStar_All.pipe_right binders
                  (FStar_List.map
                     (fun uu___10_9224  ->
                        match uu___10_9224 with
                        | FStar_Util.Inr x -> x
                        | FStar_Util.Inl uu____9230 -> failwith "Impossible"))
                 in
              FStar_List.append uu____9207 [t]  in
            let uu____9232 =
              let uu____9257 =
                FStar_All.pipe_right terms
                  (FStar_List.map
                     (fun t1  ->
                        let uu____9314 = desugar_typ_aq env t1  in
                        match uu____9314 with
                        | (t',aq) ->
                            let uu____9325 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____9325, aq)))
                 in
              FStar_All.pipe_right uu____9257 FStar_List.unzip  in
            (match uu____9232 with
             | (targs,aqs) ->
                 let tup =
                   let uu____9435 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____9435
                    in
                 let uu____9444 =
                   mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                 (uu____9444, (join_aqs aqs)))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____9471 =
              let uu____9488 =
                let uu____9495 =
                  let uu____9502 =
                    FStar_All.pipe_left (fun _0_2  -> FStar_Util.Inl _0_2)
                      (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                         FStar_Pervasives_Native.None)
                     in
                  [uu____9502]  in
                FStar_List.append binders uu____9495  in
              FStar_List.fold_left
                (fun uu____9555  ->
                   fun b  ->
                     match uu____9555 with
                     | (env1,tparams,typs) ->
                         let uu____9616 =
                           match b with
                           | FStar_Util.Inl b1 -> desugar_binder env1 b1
                           | FStar_Util.Inr t1 ->
                               let uu____9631 = desugar_typ env1 t1  in
                               (FStar_Pervasives_Native.None, uu____9631)
                            in
                         (match uu____9616 with
                          | (xopt,t1) ->
                              let uu____9656 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____9665 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____9665)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____9656 with
                               | (env2,x) ->
                                   let uu____9685 =
                                     let uu____9688 =
                                       let uu____9691 =
                                         let uu____9692 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____9692
                                          in
                                       [uu____9691]  in
                                     FStar_List.append typs uu____9688  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___56_9718 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___56_9718.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___56_9718.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____9685)))) (env, [], []) uu____9488
               in
            (match uu____9471 with
             | (env1,uu____9746,targs) ->
                 let tup =
                   let uu____9769 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____9769
                    in
                 let uu____9770 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_app (tup, targs))
                    in
                 (uu____9770, noaqs))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____9789 = uncurry binders t  in
            (match uu____9789 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___11_9833 =
                   match uu___11_9833 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range true env1 t1
                          in
                       let uu____9850 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____9850
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____9874 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____9874 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____9907 = aux env [] bs  in (uu____9907, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____9916 = desugar_binder env b  in
            (match uu____9916 with
             | (FStar_Pervasives_Native.None ,uu____9927) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____9942 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____9942 with
                  | ((x,uu____9958),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____9971 =
                        let uu____9972 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____9972  in
                      (uu____9971, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let bvss =
              FStar_List.map (gather_pattern_bound_vars false) binders  in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set1::sets2 ->
                    let i = FStar_Util.set_intersect acc set1  in
                    let uu____10051 = FStar_Util.set_is_empty i  in
                    if uu____10051
                    then
                      let uu____10056 = FStar_Util.set_union acc set1  in
                      aux uu____10056 sets2
                    else
                      (let uu____10061 =
                         let uu____10062 = FStar_Util.set_elements i  in
                         FStar_List.hd uu____10062  in
                       FStar_Pervasives_Native.Some uu____10061)
                 in
              let uu____10065 = FStar_Syntax_Syntax.new_id_set ()  in
              aux uu____10065 sets  in
            ((let uu____10069 = check_disjoint bvss  in
              match uu____10069 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some id1 ->
                  let uu____10073 =
                    let uu____10079 =
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        id1.FStar_Ident.idText
                       in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____10079)
                     in
                  let uu____10083 = FStar_Ident.range_of_id id1  in
                  FStar_Errors.raise_error uu____10073 uu____10083);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern)
                 in
              let uu____10091 =
                FStar_List.fold_left
                  (fun uu____10111  ->
                     fun pat  ->
                       match uu____10111 with
                       | (env1,ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____10137,(t,FStar_Pervasives_Native.None
                                              ))
                                ->
                                let uu____10147 =
                                  let uu____10150 = free_type_vars env1 t  in
                                  FStar_List.append uu____10150 ftvs  in
                                (env1, uu____10147)
                            | FStar_Parser_AST.PatAscribed
                                (uu____10155,(t,FStar_Pervasives_Native.Some
                                              tac))
                                ->
                                let uu____10166 =
                                  let uu____10169 = free_type_vars env1 t  in
                                  let uu____10172 =
                                    let uu____10175 = free_type_vars env1 tac
                                       in
                                    FStar_List.append uu____10175 ftvs  in
                                  FStar_List.append uu____10169 uu____10172
                                   in
                                (env1, uu____10166)
                            | uu____10180 -> (env1, ftvs))) (env, [])
                  binders1
                 in
              match uu____10091 with
              | (uu____10189,ftv) ->
                  let ftv1 = sort_ftv ftv  in
                  let binders2 =
                    let uu____10201 =
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
                    FStar_List.append uu____10201 binders1  in
                  let rec aux env1 bs sc_pat_opt uu___12_10258 =
                    match uu___12_10258 with
                    | [] ->
                        let uu____10285 = desugar_term_aq env1 body  in
                        (match uu____10285 with
                         | (body1,aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc,pat) ->
                                   let body2 =
                                     let uu____10322 =
                                       let uu____10323 =
                                         FStar_Syntax_Syntax.pat_bvs pat  in
                                       FStar_All.pipe_right uu____10323
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder)
                                        in
                                     FStar_Syntax_Subst.close uu____10322
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
                             let uu____10392 =
                               let uu____10395 =
                                 no_annot_abs (FStar_List.rev bs) body2  in
                               setpos uu____10395  in
                             (uu____10392, aq))
                    | p::rest ->
                        let uu____10410 = desugar_binding_pat env1 p  in
                        (match uu____10410 with
                         | (env2,b,pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1,uu____10444)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____10459 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange
                                in
                             let uu____10468 =
                               match b with
                               | LetBinder uu____10509 ->
                                   failwith "Impossible"
                               | LocalBinder (x,aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None
                                        ,uu____10578) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.None ) ->
                                         let uu____10632 =
                                           let uu____10641 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____10641, p1)  in
                                         FStar_Pervasives_Native.Some
                                           uu____10632
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.Some
                                        (sc,p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____10703,uu____10704) ->
                                              let tup2 =
                                                let uu____10706 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.parse_int "2")
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10706
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10711 =
                                                  let uu____10718 =
                                                    let uu____10719 =
                                                      let uu____10736 =
                                                        mk1
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let uu____10739 =
                                                        let uu____10750 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let uu____10759 =
                                                          let uu____10770 =
                                                            let uu____10779 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____10779
                                                             in
                                                          [uu____10770]  in
                                                        uu____10750 ::
                                                          uu____10759
                                                         in
                                                      (uu____10736,
                                                        uu____10739)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____10719
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____10718
                                                   in
                                                uu____10711
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range
                                                 in
                                              let p2 =
                                                let uu____10830 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____10830
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____10881,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____10883,pats)) ->
                                              let tupn =
                                                let uu____10928 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    ((Prims.parse_int "1") +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10928
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10941 =
                                                  let uu____10942 =
                                                    let uu____10959 =
                                                      mk1
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____10962 =
                                                      let uu____10973 =
                                                        let uu____10984 =
                                                          let uu____10993 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____10993
                                                           in
                                                        [uu____10984]  in
                                                      FStar_List.append args
                                                        uu____10973
                                                       in
                                                    (uu____10959,
                                                      uu____10962)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____10942
                                                   in
                                                mk1 uu____10941  in
                                              let p2 =
                                                let uu____11041 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats [(p1, false)])))
                                                  uu____11041
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____11088 ->
                                              failwith "Impossible")
                                      in
                                   ((x, aq), sc_pat_opt1)
                                in
                             (match uu____10468 with
                              | (b1,sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest))
                     in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____11182,uu____11183,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____11205 =
                let uu____11206 = unparen e  in
                uu____11206.FStar_Parser_AST.tm  in
              match uu____11205 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____11216 ->
                  let uu____11217 = desugar_term_aq env e  in
                  (match uu____11217 with
                   | (head1,aq) ->
                       let uu____11230 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____11230, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____11237 ->
            let rec aux args aqs e =
              let uu____11314 =
                let uu____11315 = unparen e  in
                uu____11315.FStar_Parser_AST.tm  in
              match uu____11314 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____11333 = desugar_term_aq env t  in
                  (match uu____11333 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____11381 ->
                  let uu____11382 = desugar_term_aq env e  in
                  (match uu____11382 with
                   | (head1,aq) ->
                       let uu____11403 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____11403, (join_aqs (aq :: aqs))))
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
            let uu____11466 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____11466
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
            let uu____11518 = desugar_term_aq env t  in
            (match uu____11518 with
             | (tm,s) ->
                 let uu____11529 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____11529, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____11535 =
              let uu____11548 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____11548 then desugar_typ_aq else desugar_term_aq  in
            uu____11535 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____11607 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____11750  ->
                        match uu____11750 with
                        | (attr_opt,(p,def)) ->
                            let uu____11808 = is_app_pattern p  in
                            if uu____11808
                            then
                              let uu____11841 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____11841, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____11924 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____11924, def1)
                               | uu____11969 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____12007);
                                           FStar_Parser_AST.prange =
                                             uu____12008;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____12057 =
                                            let uu____12078 =
                                              let uu____12083 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____12083  in
                                            (uu____12078, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____12057, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____12175) ->
                                        if top_level
                                        then
                                          let uu____12211 =
                                            let uu____12232 =
                                              let uu____12237 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____12237  in
                                            (uu____12232, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____12211, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____12328 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____12361 =
                FStar_List.fold_left
                  (fun uu____12434  ->
                     fun uu____12435  ->
                       match (uu____12434, uu____12435) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____12543,uu____12544),uu____12545))
                           ->
                           let uu____12662 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____12688 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____12688 with
                                  | (env2,xx) ->
                                      let uu____12707 =
                                        let uu____12710 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____12710 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____12707))
                             | FStar_Util.Inr l ->
                                 let uu____12718 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (uu____12718, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____12662 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____12361 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____12866 =
                    match uu____12866 with
                    | (attrs_opt,(uu____12902,args,result_t),def) ->
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
                                let uu____12990 = is_comp_type env1 t  in
                                if uu____12990
                                then
                                  ((let uu____12994 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____13004 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____13004))
                                       in
                                    match uu____12994 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____13011 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____13014 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____13014))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____13011
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
                          | uu____13025 ->
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
                              let uu____13040 =
                                let uu____13041 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____13041
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____13040
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
                  let uu____13122 = desugar_term_aq env' body  in
                  (match uu____13122 with
                   | (body1,aq) ->
                       let uu____13135 =
                         let uu____13138 =
                           let uu____13139 =
                             let uu____13153 =
                               FStar_Syntax_Subst.close rec_bindings1 body1
                                in
                             ((is_rec, lbs1), uu____13153)  in
                           FStar_Syntax_Syntax.Tm_let uu____13139  in
                         FStar_All.pipe_left mk1 uu____13138  in
                       (uu____13135, aq))
               in
            let ds_non_rec attrs_opt pat t1 t2 =
              let attrs =
                match attrs_opt with
                | FStar_Pervasives_Native.None  -> []
                | FStar_Pervasives_Native.Some l ->
                    FStar_List.map (desugar_term env) l
                 in
              let t11 = desugar_term env t1  in
              let uu____13228 =
                desugar_binding_pat_maybe_top top_level env pat  in
              match uu____13228 with
              | (env1,binder,pat1) ->
                  let uu____13250 =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let uu____13276 = desugar_term_aq env1 t2  in
                        (match uu____13276 with
                         | (body1,aq) ->
                             let fv =
                               let uu____13290 =
                                 FStar_Syntax_Util.incr_delta_qualifier t11
                                  in
                               FStar_Syntax_Syntax.lid_as_fv l uu____13290
                                 FStar_Pervasives_Native.None
                                in
                             let uu____13291 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t11,
                                            (t11.FStar_Syntax_Syntax.pos))]),
                                      body1))
                                in
                             (uu____13291, aq))
                    | LocalBinder (x,uu____13324) ->
                        let uu____13325 = desugar_term_aq env1 t2  in
                        (match uu____13325 with
                         | (body1,aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | ({
                                    FStar_Syntax_Syntax.v =
                                      FStar_Syntax_Syntax.Pat_wild
                                      uu____13339;
                                    FStar_Syntax_Syntax.p = uu____13340;_},uu____13341)::[]
                                   -> body1
                               | uu____13354 ->
                                   let uu____13357 =
                                     let uu____13364 =
                                       let uu____13365 =
                                         let uu____13388 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         let uu____13391 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1
                                            in
                                         (uu____13388, uu____13391)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____13365
                                        in
                                     FStar_Syntax_Syntax.mk uu____13364  in
                                   uu____13357 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range
                                in
                             let uu____13431 =
                               let uu____13434 =
                                 let uu____13435 =
                                   let uu____13449 =
                                     let uu____13452 =
                                       let uu____13453 =
                                         FStar_Syntax_Syntax.mk_binder x  in
                                       [uu____13453]  in
                                     FStar_Syntax_Subst.close uu____13452
                                       body2
                                      in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t11,
                                           (t11.FStar_Syntax_Syntax.pos))]),
                                     uu____13449)
                                    in
                                 FStar_Syntax_Syntax.Tm_let uu____13435  in
                               FStar_All.pipe_left mk1 uu____13434  in
                             (uu____13431, aq))
                     in
                  (match uu____13250 with | (tm,aq) -> (tm, aq))
               in
            let uu____13515 = FStar_List.hd lbs  in
            (match uu____13515 with
             | (attrs,(head_pat,defn)) ->
                 let uu____13559 = is_rec || (is_app_pattern head_pat)  in
                 if uu____13559
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____13575 =
                let uu____13576 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____13576  in
              mk1 uu____13575  in
            let uu____13577 = desugar_term_aq env t1  in
            (match uu____13577 with
             | (t1',aq1) ->
                 let uu____13588 = desugar_term_aq env t2  in
                 (match uu____13588 with
                  | (t2',aq2) ->
                      let uu____13599 = desugar_term_aq env t3  in
                      (match uu____13599 with
                       | (t3',aq3) ->
                           let uu____13610 =
                             let uu____13611 =
                               let uu____13612 =
                                 let uu____13635 =
                                   let uu____13652 =
                                     let uu____13667 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t2.FStar_Parser_AST.range
                                        in
                                     (uu____13667,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____13681 =
                                     let uu____13698 =
                                       let uu____13713 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t3.FStar_Parser_AST.range
                                          in
                                       (uu____13713,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____13698]  in
                                   uu____13652 :: uu____13681  in
                                 (t1', uu____13635)  in
                               FStar_Syntax_Syntax.Tm_match uu____13612  in
                             mk1 uu____13611  in
                           (uu____13610, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____13909 =
              match uu____13909 with
              | (pat,wopt,b) ->
                  let uu____13931 = desugar_match_pat env pat  in
                  (match uu____13931 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____13962 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____13962
                          in
                       let uu____13967 = desugar_term_aq env1 b  in
                       (match uu____13967 with
                        | (b1,aq) ->
                            let uu____13980 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____13980, aq)))
               in
            let uu____13985 = desugar_term_aq env e  in
            (match uu____13985 with
             | (e1,aq) ->
                 let uu____13996 =
                   let uu____14027 =
                     let uu____14060 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____14060 FStar_List.unzip  in
                   FStar_All.pipe_right uu____14027
                     (fun uu____14278  ->
                        match uu____14278 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____13996 with
                  | (brs,aqs) ->
                      let uu____14497 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____14497, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____14531 =
              let uu____14552 = is_comp_type env t  in
              if uu____14552
              then
                let comp = desugar_comp t.FStar_Parser_AST.range true env t
                   in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____14607 = desugar_term_aq env t  in
                 match uu____14607 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____14531 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____14699 = desugar_term_aq env e  in
                 (match uu____14699 with
                  | (e1,aq) ->
                      let uu____14710 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____14710, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____14749,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____14792 = FStar_List.hd fields  in
              match uu____14792 with | (f,uu____14804) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____14850  ->
                        match uu____14850 with
                        | (g,uu____14857) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____14864,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____14878 =
                         let uu____14884 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____14884)
                          in
                       FStar_Errors.raise_error uu____14878
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
                  let uu____14895 =
                    let uu____14906 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____14937  ->
                              match uu____14937 with
                              | (f,uu____14947) ->
                                  let uu____14948 =
                                    let uu____14949 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____14949
                                     in
                                  (uu____14948, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____14906)  in
                  FStar_Parser_AST.Construct uu____14895
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____14967 =
                      let uu____14968 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____14968  in
                    FStar_Parser_AST.mk_term uu____14967
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____14970 =
                      let uu____14983 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____15013  ->
                                match uu____15013 with
                                | (f,uu____15023) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____14983)  in
                    FStar_Parser_AST.Record uu____14970  in
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
            let uu____15083 = desugar_term_aq env recterm1  in
            (match uu____15083 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____15099;
                         FStar_Syntax_Syntax.vars = uu____15100;_},args)
                      ->
                      let uu____15126 =
                        let uu____15127 =
                          let uu____15128 =
                            let uu____15145 =
                              let uu____15148 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____15149 =
                                let uu____15152 =
                                  let uu____15153 =
                                    let uu____15160 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____15160)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____15153
                                   in
                                FStar_Pervasives_Native.Some uu____15152  in
                              FStar_Syntax_Syntax.fvar uu____15148
                                FStar_Syntax_Syntax.delta_constant
                                uu____15149
                               in
                            (uu____15145, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____15128  in
                        FStar_All.pipe_left mk1 uu____15127  in
                      (uu____15126, s)
                  | uu____15189 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____15193 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____15193 with
              | (constrname,is_rec) ->
                  let uu____15212 = desugar_term_aq env e  in
                  (match uu____15212 with
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
                       let uu____15232 =
                         let uu____15233 =
                           let uu____15234 =
                             let uu____15251 =
                               let uu____15254 =
                                 let uu____15255 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____15255
                                  in
                               FStar_Syntax_Syntax.fvar uu____15254
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1")) qual
                                in
                             let uu____15257 =
                               let uu____15268 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____15268]  in
                             (uu____15251, uu____15257)  in
                           FStar_Syntax_Syntax.Tm_app uu____15234  in
                         FStar_All.pipe_left mk1 uu____15233  in
                       (uu____15232, s))))
        | FStar_Parser_AST.NamedTyp (uu____15305,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____15315 =
              let uu____15316 = FStar_Syntax_Subst.compress tm  in
              uu____15316.FStar_Syntax_Syntax.n  in
            (match uu____15315 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____15324 =
                   let uu___57_15325 =
                     let uu____15326 =
                       let uu____15328 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____15328  in
                     FStar_Syntax_Util.exp_string uu____15326  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___57_15325.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___57_15325.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____15324, noaqs)
             | uu____15329 ->
                 let uu____15330 =
                   let uu____15336 =
                     let uu____15338 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.op_Hat "VQuote, expected an fvar, got: "
                       uu____15338
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____15336)  in
                 FStar_Errors.raise_error uu____15330
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____15347 = desugar_term_aq env e  in
            (match uu____15347 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____15359 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____15359, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____15364 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____15365 =
              let uu____15366 =
                let uu____15373 = desugar_term env e  in (bv, uu____15373)
                 in
              [uu____15366]  in
            (uu____15364, uu____15365)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____15398 =
              let uu____15399 =
                let uu____15400 =
                  let uu____15407 = desugar_term env e  in (uu____15407, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____15400  in
              FStar_All.pipe_left mk1 uu____15399  in
            (uu____15398, noaqs)
        | FStar_Parser_AST.CalcProof (rel,init_expr,steps) ->
            let eta_and_annot rel1 =
              let x = FStar_Ident.gen rel1.FStar_Parser_AST.range  in
              let y = FStar_Ident.gen rel1.FStar_Parser_AST.range  in
              let xt =
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar x)
                  rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                 in
              let yt =
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar y)
                  rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                 in
              let pats =
                [FStar_Parser_AST.mk_pattern
                   (FStar_Parser_AST.PatVar (x, FStar_Pervasives_Native.None))
                   rel1.FStar_Parser_AST.range;
                FStar_Parser_AST.mk_pattern
                  (FStar_Parser_AST.PatVar (y, FStar_Pervasives_Native.None))
                  rel1.FStar_Parser_AST.range]
                 in
              let uu____15436 =
                let uu____15437 =
                  let uu____15444 =
                    let uu____15445 =
                      let uu____15446 =
                        let uu____15455 =
                          FStar_Parser_AST.mkApp rel1
                            [(xt, FStar_Parser_AST.Nothing);
                            (yt, FStar_Parser_AST.Nothing)]
                            rel1.FStar_Parser_AST.range
                           in
                        let uu____15468 =
                          let uu____15469 =
                            let uu____15470 = FStar_Ident.lid_of_str "Type0"
                               in
                            FStar_Parser_AST.Name uu____15470  in
                          FStar_Parser_AST.mk_term uu____15469
                            rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                           in
                        (uu____15455, uu____15468,
                          FStar_Pervasives_Native.None)
                         in
                      FStar_Parser_AST.Ascribed uu____15446  in
                    FStar_Parser_AST.mk_term uu____15445
                      rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                     in
                  (pats, uu____15444)  in
                FStar_Parser_AST.Abs uu____15437  in
              FStar_Parser_AST.mk_term uu____15436
                rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
               in
            let rel1 = eta_and_annot rel  in
            let wild r =
              FStar_Parser_AST.mk_term FStar_Parser_AST.Wild r
                FStar_Parser_AST.Expr
               in
            let init1 =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Var FStar_Parser_Const.calc_init_lid)
                init_expr.FStar_Parser_AST.range FStar_Parser_AST.Expr
               in
            let step r =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Var FStar_Parser_Const.calc_step_lid) r
                FStar_Parser_AST.Expr
               in
            let finish1 =
              FStar_Parser_AST.mkApp
                (FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Var FStar_Parser_Const.calc_finish_lid)
                   top.FStar_Parser_AST.range FStar_Parser_AST.Expr)
                [(rel1, FStar_Parser_AST.Nothing)] top.FStar_Parser_AST.range
               in
            let e =
              FStar_Parser_AST.mkApp init1
                [(init_expr, FStar_Parser_AST.Nothing)]
                init_expr.FStar_Parser_AST.range
               in
            let e1 =
              FStar_List.fold_left
                (fun e1  ->
                   fun uu____15516  ->
                     match uu____15516 with
                     | FStar_Parser_AST.CalcStep (rel2,just,next_expr) ->
                         let uu____15520 =
                           let uu____15527 =
                             let uu____15532 = eta_and_annot rel2  in
                             (uu____15532, FStar_Parser_AST.Nothing)  in
                           let uu____15533 =
                             let uu____15540 =
                               let uu____15547 =
                                 let uu____15552 = FStar_Parser_AST.thunk e1
                                    in
                                 (uu____15552, FStar_Parser_AST.Nothing)  in
                               let uu____15553 =
                                 let uu____15560 =
                                   let uu____15565 =
                                     FStar_Parser_AST.thunk just  in
                                   (uu____15565, FStar_Parser_AST.Nothing)
                                    in
                                 [uu____15560]  in
                               uu____15547 :: uu____15553  in
                             (next_expr, FStar_Parser_AST.Nothing) ::
                               uu____15540
                              in
                           uu____15527 :: uu____15533  in
                         FStar_Parser_AST.mkApp
                           (step rel2.FStar_Parser_AST.range) uu____15520
                           just.FStar_Parser_AST.range) e steps
               in
            let e2 =
              let uu____15587 =
                let uu____15594 =
                  let uu____15599 = FStar_Parser_AST.thunk e1  in
                  (uu____15599, FStar_Parser_AST.Nothing)  in
                [uu____15594]  in
              FStar_Parser_AST.mkApp finish1 uu____15587
                init_expr.FStar_Parser_AST.range
               in
            desugar_term_maybe_top top_level env e2
        | uu____15608 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____15609 = desugar_formula env top  in
            (uu____15609, noaqs)
        | uu____15610 ->
            let uu____15611 =
              let uu____15617 =
                let uu____15619 = FStar_Parser_AST.term_to_string top  in
                Prims.op_Hat "Unexpected term: " uu____15619  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____15617)  in
            FStar_Errors.raise_error uu____15611 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____15629 -> false
    | uu____15639 -> true

and (desugar_args :
  FStar_Syntax_DsEnv.env ->
    (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list)
  =
  fun env  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____15677  ->
              match uu____15677 with
              | (a,imp) ->
                  let uu____15690 = desugar_term env a  in
                  arg_withimp_e imp uu____15690))

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
          let is_requires uu____15727 =
            match uu____15727 with
            | (t1,uu____15734) ->
                let uu____15735 =
                  let uu____15736 = unparen t1  in
                  uu____15736.FStar_Parser_AST.tm  in
                (match uu____15735 with
                 | FStar_Parser_AST.Requires uu____15738 -> true
                 | uu____15747 -> false)
             in
          let is_ensures uu____15759 =
            match uu____15759 with
            | (t1,uu____15766) ->
                let uu____15767 =
                  let uu____15768 = unparen t1  in
                  uu____15768.FStar_Parser_AST.tm  in
                (match uu____15767 with
                 | FStar_Parser_AST.Ensures uu____15770 -> true
                 | uu____15779 -> false)
             in
          let is_app head1 uu____15797 =
            match uu____15797 with
            | (t1,uu____15805) ->
                let uu____15806 =
                  let uu____15807 = unparen t1  in
                  uu____15807.FStar_Parser_AST.tm  in
                (match uu____15806 with
                 | FStar_Parser_AST.App
                     ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                        FStar_Parser_AST.range = uu____15810;
                        FStar_Parser_AST.level = uu____15811;_},uu____15812,uu____15813)
                     -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
                 | uu____15815 -> false)
             in
          let is_smt_pat uu____15827 =
            match uu____15827 with
            | (t1,uu____15834) ->
                let uu____15835 =
                  let uu____15836 = unparen t1  in
                  uu____15836.FStar_Parser_AST.tm  in
                (match uu____15835 with
                 | FStar_Parser_AST.Construct
                     (cons1,({
                               FStar_Parser_AST.tm =
                                 FStar_Parser_AST.Construct
                                 (smtpat,uu____15840);
                               FStar_Parser_AST.range = uu____15841;
                               FStar_Parser_AST.level = uu____15842;_},uu____15843)::uu____15844::[])
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
                               FStar_Parser_AST.range = uu____15893;
                               FStar_Parser_AST.level = uu____15894;_},uu____15895)::uu____15896::[])
                     ->
                     (FStar_Ident.lid_equals cons1
                        FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  -> smtpat.FStar_Ident.str = s)
                          ["smt_pat"; "smt_pat_or"])
                 | uu____15929 -> false)
             in
          let is_decreases = is_app "decreases"  in
          let pre_process_comp_typ t1 =
            let uu____15964 = head_and_args t1  in
            match uu____15964 with
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
                     let thunk_ens uu____16057 =
                       match uu____16057 with
                       | (e,i) ->
                           let uu____16068 = FStar_Parser_AST.thunk e  in
                           (uu____16068, i)
                        in
                     let fail_lemma uu____16080 =
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
                           (Prims.op_Hat
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
                           let uu____16186 =
                             let uu____16193 =
                               let uu____16200 = thunk_ens ens  in
                               [uu____16200; nil_pat]  in
                             req_true :: uu____16193  in
                           unit_tm :: uu____16186
                       | req::ens::[] when
                           (is_requires req) && (is_ensures ens) ->
                           let uu____16247 =
                             let uu____16254 =
                               let uu____16261 = thunk_ens ens  in
                               [uu____16261; nil_pat]  in
                             req :: uu____16254  in
                           unit_tm :: uu____16247
                       | ens::smtpat::[] when
                           (((let uu____16310 = is_requires ens  in
                              Prims.op_Negation uu____16310) &&
                               (let uu____16313 = is_smt_pat ens  in
                                Prims.op_Negation uu____16313))
                              &&
                              (let uu____16316 = is_decreases ens  in
                               Prims.op_Negation uu____16316))
                             && (is_smt_pat smtpat)
                           ->
                           let uu____16318 =
                             let uu____16325 =
                               let uu____16332 = thunk_ens ens  in
                               [uu____16332; smtpat]  in
                             req_true :: uu____16325  in
                           unit_tm :: uu____16318
                       | ens::dec::[] when
                           (is_ensures ens) && (is_decreases dec) ->
                           let uu____16379 =
                             let uu____16386 =
                               let uu____16393 = thunk_ens ens  in
                               [uu____16393; nil_pat; dec]  in
                             req_true :: uu____16386  in
                           unit_tm :: uu____16379
                       | ens::dec::smtpat::[] when
                           ((is_ensures ens) && (is_decreases dec)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____16453 =
                             let uu____16460 =
                               let uu____16467 = thunk_ens ens  in
                               [uu____16467; smtpat; dec]  in
                             req_true :: uu____16460  in
                           unit_tm :: uu____16453
                       | req::ens::dec::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_decreases dec)
                           ->
                           let uu____16527 =
                             let uu____16534 =
                               let uu____16541 = thunk_ens ens  in
                               [uu____16541; nil_pat; dec]  in
                             req :: uu____16534  in
                           unit_tm :: uu____16527
                       | req::ens::smtpat::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____16601 =
                             let uu____16608 =
                               let uu____16615 = thunk_ens ens  in
                               [uu____16615; smtpat]  in
                             req :: uu____16608  in
                           unit_tm :: uu____16601
                       | req::ens::dec::smtpat::[] when
                           (((is_requires req) && (is_ensures ens)) &&
                              (is_smt_pat smtpat))
                             && (is_decreases dec)
                           ->
                           let uu____16680 =
                             let uu____16687 =
                               let uu____16694 = thunk_ens ens  in
                               [uu____16694; dec; smtpat]  in
                             req :: uu____16687  in
                           unit_tm :: uu____16680
                       | _other -> fail_lemma ()  in
                     let head_and_attributes =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) lemma
                        in
                     (head_and_attributes, args1)
                 | FStar_Parser_AST.Name l when
                     FStar_Syntax_DsEnv.is_effect_name env l ->
                     let uu____16756 =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) l
                        in
                     (uu____16756, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____16784 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____16784
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                     ->
                     let uu____16787 =
                       let uu____16794 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____16794, [])  in
                     (uu____16787, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____16812 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____16812
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                     ->
                     let uu____16815 =
                       let uu____16822 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_GTot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____16822, [])  in
                     (uu____16815, args)
                 | FStar_Parser_AST.Name l when
                     (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                        ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                       ||
                       ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                     ->
                     let uu____16844 =
                       let uu____16851 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____16851, [])  in
                     (uu____16844, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____16874 when allow_type_promotion ->
                     let default_effect =
                       let uu____16876 = FStar_Options.ml_ish ()  in
                       if uu____16876
                       then FStar_Parser_Const.effect_ML_lid
                       else
                         ((let uu____16882 =
                             FStar_Options.warn_default_effects ()  in
                           if uu____16882
                           then
                             FStar_Errors.log_issue
                               head1.FStar_Parser_AST.range
                               (FStar_Errors.Warning_UseDefaultEffect,
                                 "Using default effect Tot")
                           else ());
                          FStar_Parser_Const.effect_Tot_lid)
                        in
                     let uu____16889 =
                       let uu____16896 =
                         FStar_Ident.set_lid_range default_effect
                           head1.FStar_Parser_AST.range
                          in
                       (uu____16896, [])  in
                     (uu____16889, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____16919 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_EffectNotFound,
                         "Expected an effect constructor")
                       t1.FStar_Parser_AST.range)
             in
          let uu____16938 = pre_process_comp_typ t  in
          match uu____16938 with
          | ((eff,cattributes),args) ->
              (if (FStar_List.length args) = (Prims.parse_int "0")
               then
                 (let uu____16990 =
                    let uu____16996 =
                      let uu____16998 = FStar_Syntax_Print.lid_to_string eff
                         in
                      FStar_Util.format1 "Not enough args to effect %s"
                        uu____16998
                       in
                    (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____16996)
                     in
                  fail1 uu____16990)
               else ();
               (let is_universe uu____17014 =
                  match uu____17014 with
                  | (uu____17020,imp) -> imp = FStar_Parser_AST.UnivApp  in
                let uu____17022 = FStar_Util.take is_universe args  in
                match uu____17022 with
                | (universes,args1) ->
                    let universes1 =
                      FStar_List.map
                        (fun uu____17081  ->
                           match uu____17081 with
                           | (u,imp) -> desugar_universe u) universes
                       in
                    let uu____17088 =
                      let uu____17103 = FStar_List.hd args1  in
                      let uu____17112 = FStar_List.tl args1  in
                      (uu____17103, uu____17112)  in
                    (match uu____17088 with
                     | (result_arg,rest) ->
                         let result_typ =
                           desugar_typ env
                             (FStar_Pervasives_Native.fst result_arg)
                            in
                         let rest1 = desugar_args env rest  in
                         let uu____17167 =
                           let is_decrease uu____17206 =
                             match uu____17206 with
                             | (t1,uu____17217) ->
                                 (match t1.FStar_Syntax_Syntax.n with
                                  | FStar_Syntax_Syntax.Tm_app
                                      ({
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_fvar fv;
                                         FStar_Syntax_Syntax.pos =
                                           uu____17228;
                                         FStar_Syntax_Syntax.vars =
                                           uu____17229;_},uu____17230::[])
                                      ->
                                      FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Parser_Const.decreases_lid
                                  | uu____17269 -> false)
                              in
                           FStar_All.pipe_right rest1
                             (FStar_List.partition is_decrease)
                            in
                         (match uu____17167 with
                          | (dec,rest2) ->
                              let decreases_clause =
                                FStar_All.pipe_right dec
                                  (FStar_List.map
                                     (fun uu____17386  ->
                                        match uu____17386 with
                                        | (t1,uu____17396) ->
                                            (match t1.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____17405,(arg,uu____17407)::[])
                                                 ->
                                                 FStar_Syntax_Syntax.DECREASES
                                                   arg
                                             | uu____17446 ->
                                                 failwith "impos")))
                                 in
                              let no_additional_args =
                                let is_empty l =
                                  match l with
                                  | [] -> true
                                  | uu____17467 -> false  in
                                (((is_empty decreases_clause) &&
                                    (is_empty rest2))
                                   && (is_empty cattributes))
                                  && (is_empty universes1)
                                 in
                              let uu____17479 =
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_Tot_lid)
                                 in
                              if uu____17479
                              then FStar_Syntax_Syntax.mk_Total result_typ
                              else
                                (let uu____17486 =
                                   no_additional_args &&
                                     (FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_GTot_lid)
                                    in
                                 if uu____17486
                                 then
                                   FStar_Syntax_Syntax.mk_GTotal result_typ
                                 else
                                   (let flags1 =
                                      let uu____17496 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____17496
                                      then [FStar_Syntax_Syntax.LEMMA]
                                      else
                                        (let uu____17503 =
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_Tot_lid
                                            in
                                         if uu____17503
                                         then [FStar_Syntax_Syntax.TOTAL]
                                         else
                                           (let uu____17510 =
                                              FStar_Ident.lid_equals eff
                                                FStar_Parser_Const.effect_ML_lid
                                               in
                                            if uu____17510
                                            then
                                              [FStar_Syntax_Syntax.MLEFFECT]
                                            else
                                              (let uu____17517 =
                                                 FStar_Ident.lid_equals eff
                                                   FStar_Parser_Const.effect_GTot_lid
                                                  in
                                               if uu____17517
                                               then
                                                 [FStar_Syntax_Syntax.SOMETRIVIAL]
                                               else [])))
                                       in
                                    let flags2 =
                                      FStar_List.append flags1 cattributes
                                       in
                                    let rest3 =
                                      let uu____17538 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____17538
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
                                                    let uu____17629 =
                                                      FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.fvar
                                                      uu____17629
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
                                              | uu____17650 -> pat  in
                                            let uu____17651 =
                                              let uu____17662 =
                                                let uu____17673 =
                                                  let uu____17682 =
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (pat1,
                                                           (FStar_Syntax_Syntax.Meta_desugared
                                                              FStar_Syntax_Syntax.Meta_smt_pat)))
                                                      FStar_Pervasives_Native.None
                                                      pat1.FStar_Syntax_Syntax.pos
                                                     in
                                                  (uu____17682, aq)  in
                                                [uu____17673]  in
                                              ens :: uu____17662  in
                                            req :: uu____17651
                                        | uu____17723 -> rest2
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
        | uu____17755 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___58_17777 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___58_17777.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars = (uu___58_17777.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___59_17819 = b  in
             {
               FStar_Parser_AST.b = (uu___59_17819.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___59_17819.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___59_17819.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____17882 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____17882)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____17895 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____17895 with
             | (env1,a1) ->
                 let a2 =
                   let uu___60_17905 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___60_17905.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___60_17905.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____17931 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____17945 =
                     let uu____17948 =
                       let uu____17949 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____17949]  in
                     no_annot_abs uu____17948 body2  in
                   FStar_All.pipe_left setpos uu____17945  in
                 let uu____17970 =
                   let uu____17971 =
                     let uu____17988 =
                       let uu____17991 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____17991
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____17993 =
                       let uu____18004 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____18004]  in
                     (uu____17988, uu____17993)  in
                   FStar_Syntax_Syntax.Tm_app uu____17971  in
                 FStar_All.pipe_left mk1 uu____17970)
        | uu____18043 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____18124 = q (rest, pats, body)  in
              let uu____18131 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____18124 uu____18131
                FStar_Parser_AST.Formula
               in
            let uu____18132 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____18132 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____18141 -> failwith "impossible"  in
      let uu____18145 =
        let uu____18146 = unparen f  in uu____18146.FStar_Parser_AST.tm  in
      match uu____18145 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____18159,uu____18160) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____18172,uu____18173) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____18205 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____18205
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____18241 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____18241
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____18285 -> desugar_term env f

and (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.aqual) Prims.list))
  =
  fun env  ->
    fun bs  ->
      let uu____18290 =
        FStar_List.fold_left
          (fun uu____18323  ->
             fun b  ->
               match uu____18323 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___61_18367 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___61_18367.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___61_18367.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___61_18367.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____18382 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____18382 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___62_18400 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___62_18400.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___62_18400.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____18401 =
                               let uu____18408 =
                                 let uu____18413 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____18413)  in
                               uu____18408 :: out  in
                             (env2, uu____18401))
                    | uu____18424 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____18290 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

and (desugar_binder :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Ident.ident FStar_Pervasives_Native.option *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.TAnnotated (x,t) ->
          let uu____18497 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____18497)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____18502 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____18502)
      | FStar_Parser_AST.TVariable x ->
          let uu____18506 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____18506)
      | FStar_Parser_AST.NoName t ->
          let uu____18510 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____18510)
      | FStar_Parser_AST.Variable x ->
          ((FStar_Pervasives_Native.Some x), FStar_Syntax_Syntax.tun)

and (as_binder :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      (FStar_Ident.ident FStar_Pervasives_Native.option *
        FStar_Syntax_Syntax.term) ->
        ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option) * FStar_Syntax_DsEnv.env))
  =
  fun env  ->
    fun imp  ->
      fun uu___13_18518  ->
        match uu___13_18518 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____18540 = FStar_Syntax_Syntax.null_binder k  in
            (uu____18540, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____18557 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____18557 with
             | (env1,a1) ->
                 let uu____18574 =
                   let uu____18581 = trans_aqual env1 imp  in
                   ((let uu___63_18587 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___63_18587.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___63_18587.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____18581)
                    in
                 (uu____18574, env1))

and (trans_aqual :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___14_18595  ->
      match uu___14_18595 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____18599 =
            let uu____18600 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____18600  in
          FStar_Pervasives_Native.Some uu____18599
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None

let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b  ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x,uu____18616) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x,uu____18618) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu____18621 -> FStar_Pervasives_Native.None
  
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs  ->
    FStar_List.collect
      (fun b  ->
         let uu____18639 = binder_ident b  in
         FStar_Common.list_of_option uu____18639) bs
  
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
               (fun uu___15_18676  ->
                  match uu___15_18676 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____18681 -> false))
           in
        let quals2 q =
          let uu____18695 =
            (let uu____18699 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____18699) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____18695
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____18716 = FStar_Ident.range_of_lid disc_name  in
                let uu____18717 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____18716;
                  FStar_Syntax_Syntax.sigquals = uu____18717;
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
            let uu____18757 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____18795  ->
                        match uu____18795 with
                        | (x,uu____18806) ->
                            let uu____18811 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____18811 with
                             | (field_name,uu____18819) ->
                                 let only_decl =
                                   ((let uu____18824 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____18824)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____18826 =
                                        let uu____18828 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____18828.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____18826)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____18846 =
                                       FStar_List.filter
                                         (fun uu___16_18850  ->
                                            match uu___16_18850 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____18853 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____18846
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___17_18868  ->
                                             match uu___17_18868 with
                                             | FStar_Syntax_Syntax.NoExtract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____18873 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____18876 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____18876;
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____18883 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____18883
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          (FStar_Syntax_Syntax.Delta_equational_at_level
                                             (Prims.parse_int "1"))
                                      else
                                        FStar_Syntax_Syntax.Delta_equational_at_level
                                          (Prims.parse_int "1")
                                       in
                                    let lb =
                                      let uu____18894 =
                                        let uu____18899 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____18899  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____18894;
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
                                      let uu____18903 =
                                        let uu____18904 =
                                          let uu____18911 =
                                            let uu____18914 =
                                              let uu____18915 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____18915
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____18914]  in
                                          ((false, [lb]), uu____18911)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____18904
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____18903;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____18757 FStar_List.flatten
  
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
            (lid,uu____18964,t,uu____18966,n1,uu____18968) when
            let uu____18975 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____18975 ->
            let uu____18977 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____18977 with
             | (formals,uu____18995) ->
                 (match formals with
                  | [] -> []
                  | uu____19024 ->
                      let filter_records uu___18_19040 =
                        match uu___18_19040 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____19043,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____19055 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____19057 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____19057 with
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
                      let uu____19069 = FStar_Util.first_N n1 formals  in
                      (match uu____19069 with
                       | (uu____19098,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____19132 -> []
  
let (mk_typ_abbrev :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
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
                    let uu____19211 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____19211
                    then
                      let uu____19217 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____19217
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____19221 =
                      let uu____19226 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____19226  in
                    let uu____19227 =
                      if FStar_Util.is_some kopt
                      then
                        let uu____19233 =
                          let uu____19236 =
                            FStar_All.pipe_right kopt FStar_Util.must  in
                          FStar_Syntax_Syntax.mk_Total uu____19236  in
                        FStar_Syntax_Util.arrow typars uu____19233
                      else FStar_Syntax_Syntax.tun  in
                    let uu____19241 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____19221;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____19227;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____19241;
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
          (env_t * FStar_Syntax_Syntax.sigelts))
  =
  fun env  ->
    fun d  ->
      fun quals  ->
        fun tcs  ->
          let rng = d.FStar_Parser_AST.drange  in
          let tycon_id uu___19_19295 =
            match uu___19_19295 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____19297,uu____19298) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____19308,uu____19309,uu____19310) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____19320,uu____19321,uu____19322) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____19352,uu____19353,uu____19354) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____19400) ->
                let uu____19401 =
                  let uu____19402 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____19402  in
                FStar_Parser_AST.mk_term uu____19401 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____19404 =
                  let uu____19405 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____19405  in
                FStar_Parser_AST.mk_term uu____19404 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____19407) ->
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
              | uu____19438 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____19446 =
                     let uu____19447 =
                       let uu____19454 = binder_to_term b  in
                       (out, uu____19454, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____19447  in
                   FStar_Parser_AST.mk_term uu____19446
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___20_19466 =
            match uu___20_19466 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.op_Hat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____19523  ->
                       match uu____19523 with
                       | (x,t,uu____19534) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated (x, t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____19540 =
                    let uu____19541 =
                      let uu____19542 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____19542  in
                    FStar_Parser_AST.mk_term uu____19541
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____19540 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let names1 =
                  let uu____19549 = binder_idents parms  in id1 ::
                    uu____19549
                   in
                (FStar_List.iter
                   (fun uu____19567  ->
                      match uu____19567 with
                      | (f,uu____19577,uu____19578) ->
                          let uu____19583 =
                            FStar_Util.for_some
                              (fun i  -> FStar_Ident.ident_equals f i) names1
                             in
                          if uu____19583
                          then
                            let uu____19588 =
                              let uu____19594 =
                                let uu____19596 =
                                  FStar_Ident.string_of_ident f  in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu____19596
                                 in
                              (FStar_Errors.Error_FieldShadow, uu____19594)
                               in
                            FStar_Errors.raise_error uu____19588
                              f.FStar_Ident.idRange
                          else ()) fields;
                 (let uu____19602 =
                    FStar_All.pipe_right fields
                      (FStar_List.map
                         (fun uu____19629  ->
                            match uu____19629 with
                            | (x,uu____19639,uu____19640) -> x))
                     in
                  ((FStar_Parser_AST.TyconVariant
                      (id1, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp),
                           FStar_Pervasives_Native.None, false)])),
                    uu____19602)))
            | uu____19698 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___21_19738 =
            match uu___21_19738 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____19762 = typars_of_binders _env binders  in
                (match uu____19762 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____19798 =
                         let uu____19799 =
                           let uu____19800 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____19800  in
                         FStar_Parser_AST.mk_term uu____19799
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____19798 binders  in
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
            | uu____19811 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____19854 =
              FStar_List.fold_left
                (fun uu____19888  ->
                   fun uu____19889  ->
                     match (uu____19888, uu____19889) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____19958 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____19958 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____19854 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____20049 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____20049
                | uu____20050 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____20058 = desugar_abstract_tc quals env [] tc  in
              (match uu____20058 with
               | (uu____20071,uu____20072,se,uu____20074) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____20077,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____20096 =
                                 let uu____20098 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____20098  in
                               if uu____20096
                               then
                                 let uu____20101 =
                                   let uu____20107 =
                                     let uu____20109 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____20109
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____20107)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____20101
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
                           | uu____20122 ->
                               let uu____20123 =
                                 let uu____20130 =
                                   let uu____20131 =
                                     let uu____20146 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____20146)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____20131
                                    in
                                 FStar_Syntax_Syntax.mk uu____20130  in
                               uu____20123 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___64_20162 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___64_20162.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___64_20162.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___64_20162.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____20163 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____20167 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____20167
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____20180 = typars_of_binders env binders  in
              (match uu____20180 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____20214 =
                           FStar_Util.for_some
                             (fun uu___22_20217  ->
                                match uu___22_20217 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____20220 -> false) quals
                            in
                         if uu____20214
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____20228 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____20228
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____20233 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___23_20239  ->
                               match uu___23_20239 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____20242 -> false))
                        in
                     if uu____20233
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____20256 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____20256
                     then
                       let uu____20262 =
                         let uu____20269 =
                           let uu____20270 = unparen t  in
                           uu____20270.FStar_Parser_AST.tm  in
                         match uu____20269 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____20291 =
                               match FStar_List.rev args with
                               | (last_arg,uu____20321)::args_rev ->
                                   let uu____20333 =
                                     let uu____20334 = unparen last_arg  in
                                     uu____20334.FStar_Parser_AST.tm  in
                                   (match uu____20333 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____20362 -> ([], args))
                               | uu____20371 -> ([], args)  in
                             (match uu____20291 with
                              | (cattributes,args1) ->
                                  let uu____20410 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____20410))
                         | uu____20421 -> (t, [])  in
                       match uu____20262 with
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
                                  (fun uu___24_20444  ->
                                     match uu___24_20444 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____20447 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____20456)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____20480 = tycon_record_as_variant trec  in
              (match uu____20480 with
               | (t,fs) ->
                   let uu____20497 =
                     let uu____20500 =
                       let uu____20501 =
                         let uu____20510 =
                           let uu____20513 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____20513  in
                         (uu____20510, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____20501  in
                     uu____20500 :: quals  in
                   desugar_tycon env d uu____20497 [t])
          | uu____20518::uu____20519 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____20689 = et  in
                match uu____20689 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____20919 ->
                         let trec = tc  in
                         let uu____20943 = tycon_record_as_variant trec  in
                         (match uu____20943 with
                          | (t,fs) ->
                              let uu____21003 =
                                let uu____21006 =
                                  let uu____21007 =
                                    let uu____21016 =
                                      let uu____21019 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____21019  in
                                    (uu____21016, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____21007
                                   in
                                uu____21006 :: quals1  in
                              collect_tcs uu____21003 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____21109 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____21109 with
                          | (env2,uu____21170,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____21323 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____21323 with
                          | (env2,uu____21384,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____21512 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____21562 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____21562 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___26_22077  ->
                             match uu___26_22077 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____22143,uu____22144);
                                    FStar_Syntax_Syntax.sigrng = uu____22145;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____22146;
                                    FStar_Syntax_Syntax.sigmeta = uu____22147;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____22148;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____22212 =
                                     typars_of_binders env1 binders  in
                                   match uu____22212 with
                                   | (env2,tpars1) ->
                                       let uu____22239 =
                                         push_tparams env2 tpars1  in
                                       (match uu____22239 with
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
                                 let uu____22268 =
                                   let uu____22287 =
                                     mk_typ_abbrev id1 uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____22287)
                                    in
                                 [uu____22268]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____22347);
                                    FStar_Syntax_Syntax.sigrng = uu____22348;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____22350;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____22351;_},constrs,tconstr,quals1)
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
                                 let uu____22452 = push_tparams env1 tpars
                                    in
                                 (match uu____22452 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____22519  ->
                                             match uu____22519 with
                                             | (x,uu____22531) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____22536 =
                                        let uu____22563 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____22673  ->
                                                  match uu____22673 with
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
                                                        let uu____22733 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____22733
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
                                                                uu___25_22744
                                                                 ->
                                                                match uu___25_22744
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____22756
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____22764 =
                                                        let uu____22783 =
                                                          let uu____22784 =
                                                            let uu____22785 =
                                                              let uu____22801
                                                                =
                                                                let uu____22802
                                                                  =
                                                                  let uu____22805
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____22805
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____22802
                                                                 in
                                                              (name, univs1,
                                                                uu____22801,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____22785
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____22784;
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
                                                          uu____22783)
                                                         in
                                                      (name, uu____22764)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____22563
                                         in
                                      (match uu____22536 with
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
                             | uu____23021 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____23149  ->
                             match uu____23149 with
                             | (name_doc,uu____23175,uu____23176) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____23248  ->
                             match uu____23248 with
                             | (uu____23267,uu____23268,se) -> se))
                      in
                   let uu____23294 =
                     let uu____23301 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____23301 rng
                      in
                   (match uu____23294 with
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
                               (fun uu____23363  ->
                                  match uu____23363 with
                                  | (uu____23384,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____23432,tps,k,uu____23435,constrs)
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
                                      let uu____23456 =
                                        FStar_All.pipe_right constrs
                                          (FStar_List.filter
                                             (fun data_lid  ->
                                                let data_quals =
                                                  let data_se =
                                                    let uu____23471 =
                                                      FStar_All.pipe_right
                                                        sigelts
                                                        (FStar_List.find
                                                           (fun se1  ->
                                                              match se1.FStar_Syntax_Syntax.sigel
                                                              with
                                                              | FStar_Syntax_Syntax.Sig_datacon
                                                                  (name,uu____23488,uu____23489,uu____23490,uu____23491,uu____23492)
                                                                  ->
                                                                  FStar_Ident.lid_equals
                                                                    name
                                                                    data_lid
                                                              | uu____23499
                                                                  -> false))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____23471
                                                      FStar_Util.must
                                                     in
                                                  data_se.FStar_Syntax_Syntax.sigquals
                                                   in
                                                let uu____23503 =
                                                  FStar_All.pipe_right
                                                    data_quals
                                                    (FStar_List.existsb
                                                       (fun uu___27_23510  ->
                                                          match uu___27_23510
                                                          with
                                                          | FStar_Syntax_Syntax.RecordConstructor
                                                              uu____23512 ->
                                                              true
                                                          | uu____23522 ->
                                                              false))
                                                   in
                                                Prims.op_Negation uu____23503))
                                         in
                                      mk_data_discriminators quals2 env3
                                        uu____23456
                                  | uu____23524 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____23541  ->
                                 match uu____23541 with
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
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
        Prims.list))
  =
  fun env  ->
    fun binders  ->
      let uu____23586 =
        FStar_List.fold_left
          (fun uu____23621  ->
             fun b  ->
               match uu____23621 with
               | (env1,binders1) ->
                   let uu____23665 = desugar_binder env1 b  in
                   (match uu____23665 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____23688 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____23688 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____23741 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____23586 with
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
          let uu____23845 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___28_23852  ->
                    match uu___28_23852 with
                    | FStar_Syntax_Syntax.Reflectable uu____23854 -> true
                    | uu____23856 -> false))
             in
          if uu____23845
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____23861 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____23861
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
      (Prims.int Prims.list * Prims.bool) FStar_Pervasives_Native.option)
  =
  fun warn  ->
    fun at1  ->
      let uu____23902 = FStar_Syntax_Util.head_and_args at1  in
      match uu____23902 with
      | (hd1,args) ->
          let uu____23955 =
            let uu____23970 =
              let uu____23971 = FStar_Syntax_Subst.compress hd1  in
              uu____23971.FStar_Syntax_Syntax.n  in
            (uu____23970, args)  in
          (match uu____23955 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(a1,uu____23996)::[]) when
               (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr)
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.fail_lax_attr)
               ->
               let uu____24031 =
                 let uu____24036 =
                   let uu____24045 =
                     FStar_Syntax_Embeddings.e_list
                       FStar_Syntax_Embeddings.e_int
                      in
                   FStar_Syntax_Embeddings.unembed uu____24045 a1  in
                 uu____24036 true FStar_Syntax_Embeddings.id_norm_cb  in
               (match uu____24031 with
                | FStar_Pervasives_Native.Some es when
                    (FStar_List.length es) > (Prims.parse_int "0") ->
                    let b =
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.fail_lax_attr
                       in
                    let uu____24075 =
                      let uu____24084 =
                        FStar_List.map FStar_BigInt.to_int_fs es  in
                      (uu____24084, b)  in
                    FStar_Pervasives_Native.Some uu____24075
                | uu____24101 ->
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
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____24155) when
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
           | uu____24190 -> FStar_Pervasives_Native.None)
  
let rec (desugar_effect :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.decl ->
      FStar_Parser_AST.qualifiers ->
        FStar_Ident.ident ->
          FStar_Parser_AST.binder Prims.list ->
            FStar_Parser_AST.term ->
              FStar_Parser_AST.decl Prims.list ->
                FStar_Parser_AST.term Prims.list ->
                  (FStar_Syntax_DsEnv.env * FStar_Syntax_Syntax.sigelt
                    Prims.list))
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
                  let uu____24362 = desugar_binders monad_env eff_binders  in
                  match uu____24362 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let for_free =
                        let uu____24402 =
                          let uu____24404 =
                            let uu____24413 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____24413  in
                          FStar_List.length uu____24404  in
                        uu____24402 = (Prims.parse_int "1")  in
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
                            (uu____24497,uu____24498,(FStar_Parser_AST.TyconAbbrev
                                                      (name,uu____24500,uu____24501,uu____24502),uu____24503)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____24540 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____24543 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____24555 = name_of_eff_decl decl  in
                             FStar_List.mem uu____24555 mandatory_members)
                          eff_decls
                         in
                      (match uu____24543 with
                       | (mandatory_members_decls,actions) ->
                           let uu____24574 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____24603  ->
                                     fun decl  ->
                                       match uu____24603 with
                                       | (env2,out) ->
                                           let uu____24623 =
                                             desugar_decl env2 decl  in
                                           (match uu____24623 with
                                            | (env3,ses) ->
                                                let uu____24636 =
                                                  let uu____24639 =
                                                    FStar_List.hd ses  in
                                                  uu____24639 :: out  in
                                                (env3, uu____24636)))
                                  (env1, []))
                              in
                           (match uu____24574 with
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
                                              (uu____24708,uu____24709,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____24712,
                                                 {
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.Construct
                                                     (uu____24713,(def,uu____24715)::
                                                      (cps_type,uu____24717)::[]);
                                                   FStar_Parser_AST.range =
                                                     uu____24718;
                                                   FStar_Parser_AST.level =
                                                     uu____24719;_}),doc1)::[])
                                              when Prims.op_Negation for_free
                                              ->
                                              let uu____24775 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____24775 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____24813 =
                                                     let uu____24814 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____24815 =
                                                       let uu____24816 =
                                                         desugar_term env3
                                                           def
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____24816
                                                        in
                                                     let uu____24823 =
                                                       let uu____24824 =
                                                         desugar_typ env3
                                                           cps_type
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____24824
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____24814;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____24815;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____24823
                                                     }  in
                                                   (uu____24813, doc1))
                                          | FStar_Parser_AST.Tycon
                                              (uu____24833,uu____24834,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____24837,defn),doc1)::[])
                                              when for_free ->
                                              let uu____24876 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____24876 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____24914 =
                                                     let uu____24915 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____24916 =
                                                       let uu____24917 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____24917
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____24915;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____24916;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____24914, doc1))
                                          | uu____24926 ->
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
                                    let uu____24962 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____24962
                                     in
                                  let uu____24964 =
                                    let uu____24965 =
                                      FStar_Syntax_DsEnv.fail_or env2
                                        (FStar_Syntax_DsEnv.try_lookup_definition
                                           env2) l
                                       in
                                    FStar_All.pipe_left
                                      (FStar_Syntax_Subst.close binders1)
                                      uu____24965
                                     in
                                  ([], uu____24964)  in
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
                                      let uu____24983 =
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      ([], uu____24983)  in
                                    let uu____24990 =
                                      let uu____24991 =
                                        let uu____24992 =
                                          let uu____24993 = lookup1 "repr"
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____24993
                                           in
                                        let uu____25003 = lookup1 "return"
                                           in
                                        let uu____25005 = lookup1 "bind"  in
                                        let uu____25007 =
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
                                            uu____24992;
                                          FStar_Syntax_Syntax.return_repr =
                                            uu____25003;
                                          FStar_Syntax_Syntax.bind_repr =
                                            uu____25005;
                                          FStar_Syntax_Syntax.actions =
                                            actions1;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            uu____25007
                                        }  in
                                      FStar_Syntax_Syntax.Sig_new_effect_for_free
                                        uu____24991
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____24990;
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
                                         (fun uu___29_25015  ->
                                            match uu___29_25015 with
                                            | FStar_Syntax_Syntax.Reifiable 
                                                -> true
                                            | FStar_Syntax_Syntax.Reflectable
                                                uu____25018 -> true
                                            | uu____25020 -> false)
                                         qualifiers
                                        in
                                     let un_ts =
                                       ([], FStar_Syntax_Syntax.tun)  in
                                     let uu____25035 =
                                       let uu____25036 =
                                         let uu____25037 =
                                           lookup1 "return_wp"  in
                                         let uu____25039 = lookup1 "bind_wp"
                                            in
                                         let uu____25041 =
                                           lookup1 "if_then_else"  in
                                         let uu____25043 = lookup1 "ite_wp"
                                            in
                                         let uu____25045 = lookup1 "stronger"
                                            in
                                         let uu____25047 = lookup1 "close_wp"
                                            in
                                         let uu____25049 = lookup1 "assert_p"
                                            in
                                         let uu____25051 = lookup1 "assume_p"
                                            in
                                         let uu____25053 = lookup1 "null_wp"
                                            in
                                         let uu____25055 = lookup1 "trivial"
                                            in
                                         let uu____25057 =
                                           if rr
                                           then
                                             let uu____25059 = lookup1 "repr"
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.snd
                                               uu____25059
                                           else FStar_Syntax_Syntax.tun  in
                                         let uu____25077 =
                                           if rr
                                           then lookup1 "return"
                                           else un_ts  in
                                         let uu____25082 =
                                           if rr
                                           then lookup1 "bind"
                                           else un_ts  in
                                         let uu____25087 =
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
                                             uu____25037;
                                           FStar_Syntax_Syntax.bind_wp =
                                             uu____25039;
                                           FStar_Syntax_Syntax.if_then_else =
                                             uu____25041;
                                           FStar_Syntax_Syntax.ite_wp =
                                             uu____25043;
                                           FStar_Syntax_Syntax.stronger =
                                             uu____25045;
                                           FStar_Syntax_Syntax.close_wp =
                                             uu____25047;
                                           FStar_Syntax_Syntax.assert_p =
                                             uu____25049;
                                           FStar_Syntax_Syntax.assume_p =
                                             uu____25051;
                                           FStar_Syntax_Syntax.null_wp =
                                             uu____25053;
                                           FStar_Syntax_Syntax.trivial =
                                             uu____25055;
                                           FStar_Syntax_Syntax.repr =
                                             uu____25057;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____25077;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____25082;
                                           FStar_Syntax_Syntax.actions =
                                             actions1;
                                           FStar_Syntax_Syntax.eff_attrs =
                                             uu____25087
                                         }  in
                                       FStar_Syntax_Syntax.Sig_new_effect
                                         uu____25036
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         uu____25035;
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
                                          fun uu____25113  ->
                                            match uu____25113 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____25127 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____25127
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
                (FStar_Syntax_DsEnv.env * FStar_Syntax_Syntax.sigelt
                  Prims.list))
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
                let uu____25151 = desugar_binders env1 eff_binders  in
                match uu____25151 with
                | (env2,binders) ->
                    let uu____25188 =
                      let uu____25199 = head_and_args defn  in
                      match uu____25199 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____25236 ->
                                let uu____25237 =
                                  let uu____25243 =
                                    let uu____25245 =
                                      let uu____25247 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.op_Hat uu____25247 " not found"
                                       in
                                    Prims.op_Hat "Effect " uu____25245  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____25243)
                                   in
                                FStar_Errors.raise_error uu____25237
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____25253 =
                            match FStar_List.rev args with
                            | (last_arg,uu____25283)::args_rev ->
                                let uu____25295 =
                                  let uu____25296 = unparen last_arg  in
                                  uu____25296.FStar_Parser_AST.tm  in
                                (match uu____25295 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____25324 -> ([], args))
                            | uu____25333 -> ([], args)  in
                          (match uu____25253 with
                           | (cattributes,args1) ->
                               let uu____25376 = desugar_args env2 args1  in
                               let uu____25377 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____25376, uu____25377))
                       in
                    (match uu____25188 with
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
                          (let uu____25417 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____25417 with
                           | (ed_binders,uu____25431,ed_binders_opening) ->
                               let sub' shift_n uu____25450 =
                                 match uu____25450 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____25465 =
                                         FStar_Syntax_Subst.shift_subst
                                           (shift_n + (FStar_List.length us))
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____25465 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____25469 =
                                       let uu____25470 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____25470)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____25469
                                  in
                               let sub1 = sub' (Prims.parse_int "0")  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____25491 =
                                   let uu____25492 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____25492
                                    in
                                 let uu____25507 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____25508 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____25509 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____25510 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____25511 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____25512 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____25513 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____25514 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____25515 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____25516 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____25517 =
                                   let uu____25518 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____25518
                                    in
                                 let uu____25533 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____25534 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____25535 =
                                   FStar_List.map
                                     (fun action  ->
                                        let nparam =
                                          FStar_List.length
                                            action.FStar_Syntax_Syntax.action_params
                                           in
                                        let uu____25551 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____25552 =
                                          let uu____25553 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____25553
                                           in
                                        let uu____25574 =
                                          let uu____25575 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____25575
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____25551;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____25552;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____25574
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
                                     uu____25491;
                                   FStar_Syntax_Syntax.ret_wp = uu____25507;
                                   FStar_Syntax_Syntax.bind_wp = uu____25508;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____25509;
                                   FStar_Syntax_Syntax.ite_wp = uu____25510;
                                   FStar_Syntax_Syntax.stronger = uu____25511;
                                   FStar_Syntax_Syntax.close_wp = uu____25512;
                                   FStar_Syntax_Syntax.assert_p = uu____25513;
                                   FStar_Syntax_Syntax.assume_p = uu____25514;
                                   FStar_Syntax_Syntax.null_wp = uu____25515;
                                   FStar_Syntax_Syntax.trivial = uu____25516;
                                   FStar_Syntax_Syntax.repr = uu____25517;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____25533;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____25534;
                                   FStar_Syntax_Syntax.actions = uu____25535;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____25599 =
                                     let uu____25601 =
                                       let uu____25610 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____25610
                                        in
                                     FStar_List.length uu____25601  in
                                   uu____25599 = (Prims.parse_int "1")  in
                                 let uu____25643 =
                                   let uu____25646 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____25646 quals  in
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
                                   FStar_Syntax_Syntax.sigquals = uu____25643;
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
                                             let uu____25670 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____25670
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____25672 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____25672
                                 then
                                   let reflect_lid =
                                     let uu____25679 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____25679
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
    let uu____25691 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____25691 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.op_Hat "  " (Prims.op_Hat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____25776 ->
              let uu____25779 =
                let uu____25781 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____25781
                 in
              Prims.op_Hat "\n  " uu____25779
          | uu____25784 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____25803  ->
               match uu____25803 with
               | (k,v1) ->
                   if (k <> "summary") && (k <> "type")
                   then
                     FStar_Pervasives_Native.Some
                       (Prims.op_Hat k (Prims.op_Hat ": " v1))
                   else FStar_Pervasives_Native.None) kv
           in
        let other1 =
          if other <> []
          then Prims.op_Hat (FStar_String.concat "\n" other) "\n"
          else ""  in
        let str =
          Prims.op_Hat summary (Prims.op_Hat pp (Prims.op_Hat other1 text))
           in
        let fv =
          let uu____25848 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____25848
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____25851 =
          let uu____25862 = FStar_Syntax_Syntax.as_arg arg  in [uu____25862]
           in
        FStar_Syntax_Util.mk_app fv uu____25851

and (desugar_decl_aux :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____25893 = desugar_decl_noattrs env d  in
      match uu____25893 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____25911 = mk_comment_attr d  in uu____25911 :: attrs1  in
          let uu____25912 =
            FStar_List.mapi
              (fun i  ->
                 fun sigelt  ->
                   if i = (Prims.parse_int "0")
                   then
                     let uu___65_25922 = sigelt  in
                     {
                       FStar_Syntax_Syntax.sigel =
                         (uu___65_25922.FStar_Syntax_Syntax.sigel);
                       FStar_Syntax_Syntax.sigrng =
                         (uu___65_25922.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___65_25922.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___65_25922.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs = attrs2
                     }
                   else
                     (let uu___66_25925 = sigelt  in
                      let uu____25926 =
                        FStar_List.filter
                          (fun at1  ->
                             let uu____25932 = get_fail_attr false at1  in
                             FStar_Option.isNone uu____25932) attrs2
                         in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___66_25925.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___66_25925.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___66_25925.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___66_25925.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs = uu____25926
                      })) sigelts
             in
          (env1, uu____25912)

and (desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____25958 = desugar_decl_aux env d  in
      match uu____25958 with
      | (env1,ses) ->
          let uu____25969 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____25969)

and (desugar_decl_noattrs :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
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
      | FStar_Parser_AST.Fsdoc uu____25997 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Friend lid ->
          let uu____26002 = FStar_Syntax_DsEnv.iface env  in
          if uu____26002
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____26017 =
               let uu____26019 =
                 let uu____26021 = FStar_Syntax_DsEnv.dep_graph env  in
                 let uu____26022 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Parser_Dep.module_has_interface uu____26021
                   uu____26022
                  in
               Prims.op_Negation uu____26019  in
             if uu____26017
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____26036 =
                  let uu____26038 =
                    let uu____26040 = FStar_Syntax_DsEnv.dep_graph env  in
                    FStar_Parser_Dep.module_has_interface uu____26040 lid  in
                  Prims.op_Negation uu____26038  in
                if uu____26036
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____26054 =
                     let uu____26056 =
                       let uu____26058 = FStar_Syntax_DsEnv.dep_graph env  in
                       FStar_Parser_Dep.deps_has_implementation uu____26058
                         lid
                        in
                     Prims.op_Negation uu____26056  in
                   if uu____26054
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____26076 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____26076, [])
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
              | (FStar_Parser_AST.TyconRecord uu____26117,uu____26118)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu____26157 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1  in
          let tcs1 =
            FStar_List.map
              (fun uu____26184  ->
                 match uu____26184 with | (x,uu____26192) -> x) tcs
             in
          let uu____26197 =
            let uu____26202 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____26202 tcs1  in
          (match uu____26197 with
           | (env1,ses) ->
               let mkclass lid =
                 let uu____26219 =
                   let uu____26220 =
                     let uu____26227 =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun
                        in
                     FStar_Syntax_Syntax.mk_binder uu____26227  in
                   [uu____26220]  in
                 let uu____26240 =
                   let uu____26243 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____26246 =
                     let uu____26257 =
                       let uu____26266 =
                         let uu____26267 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____26267  in
                       FStar_Syntax_Syntax.as_arg uu____26266  in
                     [uu____26257]  in
                   FStar_Syntax_Util.mk_app uu____26243 uu____26246  in
                 FStar_Syntax_Util.abs uu____26219 uu____26240
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____26307,id1))::uu____26309 ->
                       FStar_Pervasives_Native.Some id1
                   | uu____26312::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____26316 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____26316 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id1 ->
                     let uu____26322 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     [uu____26322]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____26343) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____26353,uu____26354,uu____26355,uu____26356,uu____26357)
                     ->
                     let uu____26366 =
                       let uu____26367 =
                         let uu____26368 =
                           let uu____26375 = mkclass lid  in
                           (meths, uu____26375)  in
                         FStar_Syntax_Syntax.Sig_splice uu____26368  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____26367;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = []
                       }  in
                     [uu____26366]
                 | uu____26378 -> []  in
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
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____26412;
                    FStar_Parser_AST.prange = uu____26413;_},uu____26414)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____26424;
                    FStar_Parser_AST.prange = uu____26425;_},uu____26426)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____26442;
                         FStar_Parser_AST.prange = uu____26443;_},uu____26444);
                    FStar_Parser_AST.prange = uu____26445;_},uu____26446)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____26468;
                         FStar_Parser_AST.prange = uu____26469;_},uu____26470);
                    FStar_Parser_AST.prange = uu____26471;_},uu____26472)::[]
                   -> false
               | (p,uu____26501)::[] ->
                   let uu____26510 = is_app_pattern p  in
                   Prims.op_Negation uu____26510
               | uu____26512 -> false)
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
            let uu____26587 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____26587 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____26600 =
                     let uu____26601 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____26601.FStar_Syntax_Syntax.n  in
                   match uu____26600 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____26611) ->
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
                         | uu____26647::uu____26648 ->
                             FStar_List.map
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____26651 ->
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.collect
                                  (fun uu___30_26667  ->
                                     match uu___30_26667 with
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inl uu____26670;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____26671;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____26672;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____26673;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____26674;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____26675;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____26676;_}
                                         -> []
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____26688;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____26689;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____26690;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____26691;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____26692;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____26693;_}
                                         ->
                                         FStar_Syntax_DsEnv.lookup_letbinding_quals
                                           env
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                          in
                       let quals2 =
                         let uu____26707 =
                           FStar_All.pipe_right lets1
                             (FStar_Util.for_some
                                (fun uu____26740  ->
                                   match uu____26740 with
                                   | (uu____26754,(uu____26755,t)) ->
                                       t.FStar_Parser_AST.level =
                                         FStar_Parser_AST.Formula))
                            in
                         if uu____26707
                         then FStar_Syntax_Syntax.Logic :: quals1
                         else quals1  in
                       let lbs1 =
                         let uu____26775 =
                           FStar_All.pipe_right quals2
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract)
                            in
                         if uu____26775
                         then
                           let uu____26781 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu___67_26796 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___68_26798 = fv  in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___68_26798.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___68_26798.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___67_26796.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___67_26796.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___67_26796.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___67_26796.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___67_26796.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___67_26796.FStar_Syntax_Syntax.lbpos)
                                     }))
                              in
                           ((FStar_Pervasives_Native.fst lbs), uu____26781)
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
                   | uu____26828 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____26836 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____26855 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____26836 with
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
                       let uu___69_26892 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___69_26892.FStar_Parser_AST.prange)
                       }
                   | uu____26899 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___70_26906 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___70_26906.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___70_26906.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___70_26906.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____26942 id1 =
                   match uu____26942 with
                   | (env1,ses) ->
                       let main =
                         let uu____26963 =
                           let uu____26964 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____26964  in
                         FStar_Parser_AST.mk_term uu____26963
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
                       let uu____27014 = desugar_decl env1 id_decl  in
                       (match uu____27014 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____27032 = gather_pattern_bound_vars true pat  in
                   FStar_All.pipe_right uu____27032 FStar_Util.set_elements
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
            let uu____27056 = close_fun env t  in
            desugar_term env uu____27056  in
          let quals1 =
            let uu____27060 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____27060
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let se =
            let uu____27069 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____27069;
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
                let uu____27083 =
                  let uu____27092 = FStar_Syntax_Syntax.null_binder t  in
                  [uu____27092]  in
                let uu____27111 =
                  let uu____27114 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total
                    uu____27114
                   in
                FStar_Syntax_Util.arrow uu____27083 uu____27111
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
            let uu____27169 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____27169 with
            | FStar_Pervasives_Native.None  ->
                let uu____27172 =
                  let uu____27178 =
                    let uu____27180 =
                      let uu____27182 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.op_Hat uu____27182 " not found"  in
                    Prims.op_Hat "Effect name " uu____27180  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____27178)  in
                FStar_Errors.raise_error uu____27172
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____27190 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____27208 =
                  let uu____27211 =
                    let uu____27212 = desugar_term env t  in
                    ([], uu____27212)  in
                  FStar_Pervasives_Native.Some uu____27211  in
                (uu____27208, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____27225 =
                  let uu____27228 =
                    let uu____27229 = desugar_term env wp  in
                    ([], uu____27229)  in
                  FStar_Pervasives_Native.Some uu____27228  in
                let uu____27236 =
                  let uu____27239 =
                    let uu____27240 = desugar_term env t  in
                    ([], uu____27240)  in
                  FStar_Pervasives_Native.Some uu____27239  in
                (uu____27225, uu____27236)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____27252 =
                  let uu____27255 =
                    let uu____27256 = desugar_term env t  in
                    ([], uu____27256)  in
                  FStar_Pervasives_Native.Some uu____27255  in
                (FStar_Pervasives_Native.None, uu____27252)
             in
          (match uu____27190 with
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
            let uu____27290 =
              let uu____27291 =
                let uu____27298 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____27298, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____27291  in
            {
              FStar_Syntax_Syntax.sigel = uu____27290;
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
      (env_t * FStar_Syntax_Syntax.sigelt Prims.list))
  =
  fun env  ->
    fun decls  ->
      let uu____27325 =
        FStar_List.fold_left
          (fun uu____27345  ->
             fun d  ->
               match uu____27345 with
               | (env1,sigelts) ->
                   let uu____27365 = desugar_decl env1 d  in
                   (match uu____27365 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____27325 with
      | (env1,sigelts) ->
          let rec forward acc uu___32_27410 =
            match uu___32_27410 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____27424,FStar_Syntax_Syntax.Sig_let uu____27425) ->
                     let uu____27438 =
                       let uu____27441 =
                         let uu___71_27442 = se2  in
                         let uu____27443 =
                           let uu____27446 =
                             FStar_List.filter
                               (fun uu___31_27460  ->
                                  match uu___31_27460 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____27465;
                                           FStar_Syntax_Syntax.vars =
                                             uu____27466;_},uu____27467);
                                      FStar_Syntax_Syntax.pos = uu____27468;
                                      FStar_Syntax_Syntax.vars = uu____27469;_}
                                      when
                                      let uu____27496 =
                                        let uu____27498 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____27498
                                         in
                                      uu____27496 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____27502 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____27446
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___71_27442.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___71_27442.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___71_27442.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___71_27442.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____27443
                         }  in
                       uu____27441 :: se1 :: acc  in
                     forward uu____27438 sigelts1
                 | uu____27508 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____27516 = forward [] sigelts  in (env1, uu____27516)
  
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
        (env_t * FStar_Syntax_Syntax.modul * Prims.bool))
  =
  fun curmod  ->
    fun env  ->
      fun m  ->
        let env1 =
          match (curmod, m) with
          | (FStar_Pervasives_Native.None ,uu____27581) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____27585;
               FStar_Syntax_Syntax.exports = uu____27586;
               FStar_Syntax_Syntax.is_interface = uu____27587;_},FStar_Parser_AST.Module
             (current_lid,uu____27589)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____27598) ->
              let uu____27601 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____27601
           in
        let uu____27606 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____27648 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____27648, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____27670 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____27670, mname, decls, false)
           in
        match uu____27606 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____27712 = desugar_decls env2 decls  in
            (match uu____27712 with
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
    env_t -> FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun curmod  ->
    fun env  ->
      fun m  ->
        let m1 =
          let uu____27780 =
            (FStar_Options.interactive ()) &&
              (let uu____27783 =
                 let uu____27785 =
                   let uu____27787 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____27787  in
                 FStar_Util.get_file_extension uu____27785  in
               FStar_List.mem uu____27783 ["fsti"; "fsi"])
             in
          if uu____27780 then as_interface m else m  in
        let uu____27801 = desugar_modul_common curmod env m1  in
        match uu____27801 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____27823 = FStar_Syntax_DsEnv.pop ()  in
              (uu____27823, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun env  ->
    fun m  ->
      let uu____27845 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____27845 with
      | (env1,modul,pop_when_done) ->
          let uu____27862 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____27862 with
           | (env2,modul1) ->
               ((let uu____27874 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____27874
                 then
                   let uu____27877 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____27877
                 else ());
                (let uu____27882 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____27882, modul1))))
  
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
        (fun uu____27936  ->
           let uu____27937 = desugar_modul env modul  in
           match uu____27937 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____27979  ->
           let uu____27980 = desugar_decls env decls  in
           match uu____27980 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____28035  ->
             let uu____28036 = desugar_partial_modul modul env a_modul  in
             match uu____28036 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____28135 ->
                  let t =
                    let uu____28145 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____28145  in
                  let uu____28158 =
                    let uu____28159 = FStar_Syntax_Subst.compress t  in
                    uu____28159.FStar_Syntax_Syntax.n  in
                  (match uu____28158 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____28171,uu____28172)
                       -> bs1
                   | uu____28197 -> failwith "Impossible")
               in
            let uu____28207 =
              let uu____28214 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____28214
                FStar_Syntax_Syntax.t_unit
               in
            match uu____28207 with
            | (binders,uu____28216,binders_opening) ->
                let erase_term t =
                  let uu____28224 =
                    let uu____28225 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____28225  in
                  FStar_Syntax_Subst.close binders uu____28224  in
                let erase_tscheme uu____28243 =
                  match uu____28243 with
                  | (us,t) ->
                      let t1 =
                        let uu____28263 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____28263 t  in
                      let uu____28266 =
                        let uu____28267 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____28267  in
                      ([], uu____28266)
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
                    | uu____28290 ->
                        let bs =
                          let uu____28300 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____28300  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____28340 =
                          let uu____28341 =
                            let uu____28344 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____28344  in
                          uu____28341.FStar_Syntax_Syntax.n  in
                        (match uu____28340 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____28346,uu____28347) -> bs1
                         | uu____28372 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____28380 =
                      let uu____28381 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____28381  in
                    FStar_Syntax_Subst.close binders uu____28380  in
                  let uu___72_28382 = action  in
                  let uu____28383 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____28384 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___72_28382.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___72_28382.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____28383;
                    FStar_Syntax_Syntax.action_typ = uu____28384
                  }  in
                let uu___73_28385 = ed  in
                let uu____28386 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____28387 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____28388 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____28389 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____28390 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____28391 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____28392 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____28393 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____28394 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____28395 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____28396 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____28397 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____28398 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____28399 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____28400 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____28401 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___73_28385.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___73_28385.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____28386;
                  FStar_Syntax_Syntax.signature = uu____28387;
                  FStar_Syntax_Syntax.ret_wp = uu____28388;
                  FStar_Syntax_Syntax.bind_wp = uu____28389;
                  FStar_Syntax_Syntax.if_then_else = uu____28390;
                  FStar_Syntax_Syntax.ite_wp = uu____28391;
                  FStar_Syntax_Syntax.stronger = uu____28392;
                  FStar_Syntax_Syntax.close_wp = uu____28393;
                  FStar_Syntax_Syntax.assert_p = uu____28394;
                  FStar_Syntax_Syntax.assume_p = uu____28395;
                  FStar_Syntax_Syntax.null_wp = uu____28396;
                  FStar_Syntax_Syntax.trivial = uu____28397;
                  FStar_Syntax_Syntax.repr = uu____28398;
                  FStar_Syntax_Syntax.return_repr = uu____28399;
                  FStar_Syntax_Syntax.bind_repr = uu____28400;
                  FStar_Syntax_Syntax.actions = uu____28401;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___73_28385.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___74_28417 = se  in
                  let uu____28418 =
                    let uu____28419 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____28419  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____28418;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___74_28417.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___74_28417.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___74_28417.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___74_28417.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___75_28423 = se  in
                  let uu____28424 =
                    let uu____28425 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____28425
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____28424;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___75_28423.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___75_28423.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___75_28423.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___75_28423.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____28427 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____28428 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____28428 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____28445 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____28445
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____28447 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____28447)
  