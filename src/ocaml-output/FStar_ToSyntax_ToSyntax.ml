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
  fun uu___84_66  ->
    match uu___84_66 with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
    | uu____71 -> FStar_Pervasives_Native.None
  
let (trans_qual :
  FStar_Range.range ->
    FStar_Ident.lident FStar_Pervasives_Native.option ->
      FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier)
  =
  fun r  ->
    fun maybe_effect_id  ->
      fun uu___85_90  ->
        match uu___85_90 with
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
            let uu____93 =
              FStar_Errors.log_issue r
                (FStar_Errors.Warning_DeprecatedOpaqueQualifier,
                  "The 'opaque' qualifier is deprecated since its use was strangely schizophrenic. There were two overloaded uses: (1) Given 'opaque val f : t', the behavior was to exclude the definition of 'f' to the SMT solver. This corresponds roughly to the new 'irreducible' qualifier. (2) Given 'opaque type t = t'', the behavior was to provide the definition of 't' to the SMT solver, but not to inline it, unless absolutely required for unification. This corresponds roughly to the behavior of 'unfoldable' (which is currently the default).")
               in
            FStar_Syntax_Syntax.Visible_default
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
  fun uu___86_99  ->
    match uu___86_99 with
    | FStar_Parser_AST.SetOptions s -> FStar_Syntax_Syntax.SetOptions s
    | FStar_Parser_AST.ResetOptions sopt ->
        FStar_Syntax_Syntax.ResetOptions sopt
    | FStar_Parser_AST.LightOff  -> FStar_Syntax_Syntax.LightOff
  
let (as_imp :
  FStar_Parser_AST.imp ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
  =
  fun uu___87_110  ->
    match uu___87_110 with
    | FStar_Parser_AST.Hash  ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | uu____113 -> FStar_Pervasives_Native.None
  
let arg_withimp_e :
  'Auu____120 .
    FStar_Parser_AST.imp ->
      'Auu____120 ->
        ('Auu____120,FStar_Syntax_Syntax.arg_qualifier
                       FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2
  = fun imp  -> fun t  -> (t, (as_imp imp)) 
let arg_withimp_t :
  'Auu____145 .
    FStar_Parser_AST.imp ->
      'Auu____145 ->
        ('Auu____145,FStar_Syntax_Syntax.arg_qualifier
                       FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.tuple2
  =
  fun imp  ->
    fun t  ->
      match imp with
      | FStar_Parser_AST.Hash  ->
          (t, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag))
      | uu____164 -> (t, FStar_Pervasives_Native.None)
  
let (contains_binder : FStar_Parser_AST.binder Prims.list -> Prims.bool) =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b  ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____181 -> true
            | uu____186 -> false))
  
let rec (unparen : FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____193 -> t
  
let (tm_type_z : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____199 =
      let uu____200 = FStar_Ident.lid_of_path ["Type0"] r  in
      FStar_Parser_AST.Name uu____200  in
    FStar_Parser_AST.mk_term uu____199 r FStar_Parser_AST.Kind
  
let (tm_type : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____206 =
      let uu____207 = FStar_Ident.lid_of_path ["Type"] r  in
      FStar_Parser_AST.Name uu____207  in
    FStar_Parser_AST.mk_term uu____206 r FStar_Parser_AST.Kind
  
let rec (is_comp_type :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____218 =
        let uu____219 = unparen t  in uu____219.FStar_Parser_AST.tm  in
      match uu____218 with
      | FStar_Parser_AST.Name l ->
          let uu____221 = FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
          FStar_All.pipe_right uu____221 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l,uu____227) ->
          let uu____240 = FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
          FStar_All.pipe_right uu____240 FStar_Option.isSome
      | FStar_Parser_AST.App (head1,uu____246,uu____247) ->
          is_comp_type env head1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,uu____250,uu____251) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____256,t1) -> is_comp_type env t1
      | uu____258 -> false
  
let (unit_ty : FStar_Parser_AST.term) =
  FStar_Parser_AST.mk_term
    (FStar_Parser_AST.Name FStar_Parser_Const.unit_lid)
    FStar_Range.dummyRange FStar_Parser_AST.Type_level
  
let (compile_op_lid :
  Prims.int -> Prims.string -> FStar_Range.range -> FStar_Ident.lident) =
  fun n1  ->
    fun s  ->
      fun r  ->
        let uu____274 =
          let uu____277 =
            let uu____278 =
              let uu____283 = FStar_Parser_AST.compile_op n1 s r  in
              (uu____283, r)  in
            FStar_Ident.mk_ident uu____278  in
          [uu____277]  in
        FStar_All.pipe_right uu____274 FStar_Ident.lid_of_ids
  
let op_as_term :
  'Auu____296 .
    FStar_Syntax_DsEnv.env ->
      Prims.int ->
        'Auu____296 ->
          FStar_Ident.ident ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun arity  ->
      fun rng  ->
        fun op  ->
          let r l dd =
            let uu____330 =
              let uu____331 =
                let uu____332 =
                  FStar_Ident.set_lid_range l op.FStar_Ident.idRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____332 dd
                  FStar_Pervasives_Native.None
                 in
              FStar_All.pipe_right uu____331 FStar_Syntax_Syntax.fv_to_tm  in
            FStar_Pervasives_Native.Some uu____330  in
          let fallback uu____339 =
            let uu____340 = FStar_Ident.text_of_id op  in
            match uu____340 with
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
                let uu____343 = FStar_Options.ml_ish ()  in
                if uu____343
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
            | uu____347 -> FStar_Pervasives_Native.None  in
          let uu____348 =
            let uu____355 =
              compile_op_lid arity op.FStar_Ident.idText
                op.FStar_Ident.idRange
               in
            FStar_Syntax_DsEnv.try_lookup_lid env uu____355  in
          match uu____348 with
          | FStar_Pervasives_Native.Some t ->
              FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst t)
          | uu____367 -> fallback ()
  
let (sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list)
  =
  fun ftv  ->
    let uu____385 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv
       in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____385
  
let rec (free_type_vars_b :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Syntax_DsEnv.env,FStar_Ident.ident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____432 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____436 = FStar_Syntax_DsEnv.push_bv env x  in
          (match uu____436 with | (env1,uu____448) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____451,term) ->
          let uu____453 = free_type_vars env term  in (env, uu____453)
      | FStar_Parser_AST.TAnnotated (id1,uu____459) ->
          let uu____460 = FStar_Syntax_DsEnv.push_bv env id1  in
          (match uu____460 with | (env1,uu____472) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____476 = free_type_vars env t  in (env, uu____476)

and (free_type_vars :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun t  ->
      let uu____483 =
        let uu____484 = unparen t  in uu____484.FStar_Parser_AST.tm  in
      match uu____483 with
      | FStar_Parser_AST.Labeled uu____487 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____497 = FStar_Syntax_DsEnv.try_lookup_id env a  in
          (match uu____497 with
           | FStar_Pervasives_Native.None  -> [a]
           | uu____510 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____517 -> []
      | FStar_Parser_AST.Uvar uu____518 -> []
      | FStar_Parser_AST.Var uu____519 -> []
      | FStar_Parser_AST.Projector uu____520 -> []
      | FStar_Parser_AST.Discrim uu____525 -> []
      | FStar_Parser_AST.Name uu____526 -> []
      | FStar_Parser_AST.Requires (t1,uu____528) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____534) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____539,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None  -> []
             | FStar_Pervasives_Native.Some t2 -> [t2])
             in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____557,ts) ->
          FStar_List.collect
            (fun uu____578  ->
               match uu____578 with | (t1,uu____586) -> free_type_vars env t1)
            ts
      | FStar_Parser_AST.Op (uu____587,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____595) ->
          let uu____596 = free_type_vars env t1  in
          let uu____599 = free_type_vars env t2  in
          FStar_List.append uu____596 uu____599
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____604 = free_type_vars_b env b  in
          (match uu____604 with
           | (env1,f) ->
               let uu____619 = free_type_vars env1 t1  in
               FStar_List.append f uu____619)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____628 =
            FStar_List.fold_left
              (fun uu____648  ->
                 fun binder  ->
                   match uu____648 with
                   | (env1,free) ->
                       let uu____668 = free_type_vars_b env1 binder  in
                       (match uu____668 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____628 with
           | (env1,free) ->
               let uu____699 = free_type_vars env1 body  in
               FStar_List.append free uu____699)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____708 =
            FStar_List.fold_left
              (fun uu____728  ->
                 fun binder  ->
                   match uu____728 with
                   | (env1,free) ->
                       let uu____748 = free_type_vars_b env1 binder  in
                       (match uu____748 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____708 with
           | (env1,free) ->
               let uu____779 = free_type_vars env1 body  in
               FStar_List.append free uu____779)
      | FStar_Parser_AST.Project (t1,uu____783) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.Abs uu____787 -> []
      | FStar_Parser_AST.Let uu____794 -> []
      | FStar_Parser_AST.LetOpen uu____815 -> []
      | FStar_Parser_AST.If uu____820 -> []
      | FStar_Parser_AST.QForall uu____827 -> []
      | FStar_Parser_AST.QExists uu____840 -> []
      | FStar_Parser_AST.Record uu____853 -> []
      | FStar_Parser_AST.Match uu____866 -> []
      | FStar_Parser_AST.TryWith uu____881 -> []
      | FStar_Parser_AST.Bind uu____896 -> []
      | FStar_Parser_AST.Quote uu____903 -> []
      | FStar_Parser_AST.VQuote uu____908 -> []
      | FStar_Parser_AST.Antiquote uu____909 -> []
      | FStar_Parser_AST.Seq uu____914 -> []

let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term,(FStar_Parser_AST.term,FStar_Parser_AST.imp)
                             FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let rec aux args t1 =
      let uu____965 =
        let uu____966 = unparen t1  in uu____966.FStar_Parser_AST.tm  in
      match uu____965 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____1008 -> (t1, args)  in
    aux [] t
  
let (close :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____1032 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1032  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1050 =
                     let uu____1051 =
                       let uu____1056 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____1056)  in
                     FStar_Parser_AST.TAnnotated uu____1051  in
                   FStar_Parser_AST.mk_binder uu____1050
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
        let uu____1073 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1073  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1091 =
                     let uu____1092 =
                       let uu____1097 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____1097)  in
                     FStar_Parser_AST.TAnnotated uu____1092  in
                   FStar_Parser_AST.mk_binder uu____1091
                     x.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____1099 =
             let uu____1100 = unparen t  in uu____1100.FStar_Parser_AST.tm
              in
           match uu____1099 with
           | FStar_Parser_AST.Product uu____1101 -> t
           | uu____1108 ->
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
      | uu____1144 -> (bs, t)
  
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild  -> true
    | FStar_Parser_AST.PatTvar (uu____1152,uu____1153) -> true
    | FStar_Parser_AST.PatVar (uu____1158,uu____1159) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____1165) -> is_var_pattern p1
    | uu____1178 -> false
  
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____1185) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____1198;
           FStar_Parser_AST.prange = uu____1199;_},uu____1200)
        -> true
    | uu____1211 -> false
  
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
    | uu____1225 -> p
  
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
            let uu____1295 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____1295 with
             | (name,args,uu____1338) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1388);
               FStar_Parser_AST.prange = uu____1389;_},args)
            when is_top_level1 ->
            let uu____1399 =
              let uu____1404 = FStar_Syntax_DsEnv.qualify env id1  in
              FStar_Util.Inr uu____1404  in
            (uu____1399, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1426);
               FStar_Parser_AST.prange = uu____1427;_},args)
            -> ((FStar_Util.Inl id1), args, FStar_Pervasives_Native.None)
        | uu____1457 -> failwith "Not an app pattern"
  
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
      | FStar_Parser_AST.PatConst uu____1506 -> acc
      | FStar_Parser_AST.PatVar
          (uu____1507,FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit
           ))
          -> acc
      | FStar_Parser_AST.PatName uu____1510 -> acc
      | FStar_Parser_AST.PatTvar uu____1511 -> acc
      | FStar_Parser_AST.PatOp uu____1518 -> acc
      | FStar_Parser_AST.PatApp (phead,pats) ->
          gather_pattern_bound_vars_from_list (phead :: pats)
      | FStar_Parser_AST.PatVar (x,uu____1526) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatTuple (pats,uu____1535) ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu____1550 =
            FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
          gather_pattern_bound_vars_from_list uu____1550
      | FStar_Parser_AST.PatAscribed (pat,uu____1558) ->
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
    match projectee with | LocalBinder _0 -> true | uu____1618 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____1654 -> false
  
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
  fun uu___88_1700  ->
    match uu___88_1700 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____1707 -> failwith "Impossible"
  
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
      fun uu___89_1738  ->
        match uu___89_1738 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____1754 = FStar_Syntax_Syntax.null_binder k  in
            (uu____1754, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____1759 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____1759 with
             | (env1,a1) ->
                 (((let uu___113_1779 = a1  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___113_1779.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___113_1779.FStar_Syntax_Syntax.index);
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
  fun uu____1808  ->
    match uu____1808 with
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
      let uu____1882 =
        let uu____1897 =
          let uu____1898 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____1898  in
        let uu____1899 =
          let uu____1908 =
            let uu____1915 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____1915)  in
          [uu____1908]  in
        (uu____1897, uu____1899)  in
      FStar_Syntax_Syntax.Tm_app uu____1882  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____1950 =
        let uu____1965 =
          let uu____1966 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____1966  in
        let uu____1967 =
          let uu____1976 =
            let uu____1983 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____1983)  in
          [uu____1976]  in
        (uu____1965, uu____1967)  in
      FStar_Syntax_Syntax.Tm_app uu____1950  in
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
          let uu____2032 =
            let uu____2047 =
              let uu____2048 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.Delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____2048  in
            let uu____2049 =
              let uu____2058 =
                let uu____2065 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____2065)  in
              let uu____2068 =
                let uu____2077 =
                  let uu____2084 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____2084)  in
                [uu____2077]  in
              uu____2058 :: uu____2068  in
            (uu____2047, uu____2049)  in
          FStar_Syntax_Syntax.Tm_app uu____2032  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___90_2117  ->
    match uu___90_2117 with
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
    | uu____2118 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____2130 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____2130)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____2149 =
      let uu____2150 = unparen t  in uu____2150.FStar_Parser_AST.tm  in
    match uu____2149 with
    | FStar_Parser_AST.Wild  ->
        let uu____2155 =
          let uu____2156 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____2156  in
        FStar_Util.Inr uu____2155
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____2167)) ->
        let n1 = FStar_Util.int_of_string repr  in
        let uu____2181 =
          if n1 < (Prims.parse_int "0")
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_NegativeUniverseConstFatal_NotSupported,
                (Prims.strcat
                   "Negative universe constant  are not supported : " repr))
              t.FStar_Parser_AST.range
          else ()  in
        FStar_Util.Inl n1
    | FStar_Parser_AST.Op (op_plus,t1::t2::[]) ->
        let uu____2188 = let uu____2189 = Obj.magic ()  in ()  in
        let u1 = desugar_maybe_non_constant_universe t1  in
        let u2 = desugar_maybe_non_constant_universe t2  in
        (match (u1, u2) with
         | (FStar_Util.Inl n1,FStar_Util.Inl n2) -> FStar_Util.Inl (n1 + n2)
         | (FStar_Util.Inl n1,FStar_Util.Inr u) ->
             let uu____2232 = sum_to_universe u n1  in
             FStar_Util.Inr uu____2232
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____2243 = sum_to_universe u n1  in
             FStar_Util.Inr uu____2243
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____2254 =
               let uu____2259 =
                 let uu____2260 = FStar_Parser_AST.term_to_string t  in
                 Prims.strcat
                   "This universe might contain a sum of two universe variables "
                   uu____2260
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____2259)
                in
             FStar_Errors.raise_error uu____2254 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____2265 ->
        let rec aux t1 univargs =
          let uu____2297 =
            let uu____2298 = unparen t1  in uu____2298.FStar_Parser_AST.tm
             in
          match uu____2297 with
          | FStar_Parser_AST.App (t2,targ,uu____2305) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              let uu____2316 = let uu____2317 = Obj.magic ()  in ()  in
              if
                FStar_List.existsb
                  (fun uu___91_2328  ->
                     match uu___91_2328 with
                     | FStar_Util.Inr uu____2333 -> true
                     | uu____2334 -> false) univargs
              then
                let uu____2339 =
                  let uu____2340 =
                    FStar_List.map
                      (fun uu___92_2349  ->
                         match uu___92_2349 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____2340  in
                FStar_Util.Inr uu____2339
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___93_2366  ->
                        match uu___93_2366 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____2372 -> failwith "impossible")
                     univargs
                    in
                 let uu____2373 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____2373)
          | uu____2379 ->
              let uu____2380 =
                let uu____2385 =
                  let uu____2386 =
                    let uu____2387 = FStar_Parser_AST.term_to_string t1  in
                    Prims.strcat uu____2387 " in universe context"  in
                  Prims.strcat "Unexpected term " uu____2386  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____2385)  in
              FStar_Errors.raise_error uu____2380 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____2396 ->
        let uu____2397 =
          let uu____2402 =
            let uu____2403 =
              let uu____2404 = FStar_Parser_AST.term_to_string t  in
              Prims.strcat uu____2404 " in universe context"  in
            Prims.strcat "Unexpected term " uu____2403  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____2402)  in
        FStar_Errors.raise_error uu____2397 t.FStar_Parser_AST.range
  
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
    | (bv,b,e)::uu____2437 ->
        let uu____2460 =
          let uu____2465 =
            let uu____2466 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format2 "Unexpected antiquotation: %s(%s)"
              (if b then "`@" else "`#") uu____2466
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____2465)  in
        FStar_Errors.raise_error uu____2460 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'Auu____2476 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident,'Auu____2476) FStar_Pervasives_Native.tuple2
        Prims.list -> FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____2504 = FStar_List.hd fields  in
        match uu____2504 with
        | (f,uu____2514) ->
            let uu____2515 =
              FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f  in
            let record =
              FStar_Syntax_DsEnv.fail_or env
                (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
               in
            let check_field uu____2525 =
              match uu____2525 with
              | (f',uu____2531) ->
                  let uu____2532 =
                    FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f'
                     in
                  let uu____2533 =
                    FStar_Syntax_DsEnv.belongs_to_record env f' record  in
                  if uu____2533
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
                         msg) rg)
               in
            let uu____2536 =
              let uu____2537 = FStar_List.tl fields  in
              FStar_List.iter check_field uu____2537  in
            (match uu____2536 with | () -> record)
  
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
            | FStar_Syntax_Syntax.Pat_dot_term uu____2889 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_wild uu____2896 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_constant uu____2897 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_var x ->
                FStar_Util.set_add x FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_cons (uu____2899,pats1) ->
                let aux out uu____2935 =
                  match uu____2935 with
                  | (p2,uu____2947) ->
                      let intersection =
                        let uu____2955 = pat_vars p2  in
                        FStar_Util.set_intersect uu____2955 out  in
                      let uu____2958 = FStar_Util.set_is_empty intersection
                         in
                      if uu____2958
                      then
                        let uu____2961 = pat_vars p2  in
                        FStar_Util.set_union out uu____2961
                      else
                        (let duplicate_bv =
                           let uu____2966 =
                             FStar_Util.set_elements intersection  in
                           FStar_List.hd uu____2966  in
                         let uu____2969 =
                           let uu____2974 =
                             FStar_Util.format1
                               "Non-linear patterns are not permitted. %s appears more than once in this pattern."
                               (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                              in
                           (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                             uu____2974)
                            in
                         FStar_Errors.raise_error uu____2969 r)
                   in
                FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
             in
          match pats with
          | [] -> ()
          | p1::[] ->
              let uu____2994 = pat_vars p1  in
              FStar_All.pipe_right uu____2994
                (fun a246  -> (Obj.magic ()) a246)
          | p1::ps ->
              let pvars = pat_vars p1  in
              let aux p2 =
                let uu____3015 =
                  let uu____3016 = pat_vars p2  in
                  FStar_Util.set_eq pvars uu____3016  in
                if uu____3015
                then ()
                else
                  (let nonlinear_vars =
                     let uu____3023 = pat_vars p2  in
                     FStar_Util.set_symmetric_difference pvars uu____3023  in
                   let first_nonlinear_var =
                     let uu____3027 = FStar_Util.set_elements nonlinear_vars
                        in
                     FStar_List.hd uu____3027  in
                   let uu____3030 =
                     let uu____3035 =
                       FStar_Util.format1
                         "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                         (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                        in
                     (FStar_Errors.Fatal_IncoherentPatterns, uu____3035)  in
                   FStar_Errors.raise_error uu____3030 r)
                 in
              FStar_List.iter aux ps
           in
        let uu____3038 =
          match (is_mut, (p.FStar_Parser_AST.pat)) with
          | (false ,uu____3039) -> ()
          | (true ,FStar_Parser_AST.PatVar uu____3040) -> ()
          | (true ,uu____3047) ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_LetMutableForVariablesOnly,
                  "let-mutable is for variables only")
                p.FStar_Parser_AST.prange
           in
        let resolvex l e x =
          let uu____3067 =
            FStar_All.pipe_right l
              (FStar_Util.find_opt
                 (fun y  ->
                    (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                      x.FStar_Ident.idText))
             in
          match uu____3067 with
          | FStar_Pervasives_Native.Some y -> (l, e, y)
          | uu____3081 ->
              let uu____3084 =
                if is_mut
                then FStar_Syntax_DsEnv.push_bv_mutable e x
                else FStar_Syntax_DsEnv.push_bv e x  in
              (match uu____3084 with | (e1,x1) -> ((x1 :: l), e1, x1))
           in
        let rec aux' top loc env1 p1 =
          let pos q =
            FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange  in
          let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
          let orig = p1  in
          match p1.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOr uu____3186 -> failwith "impossible"
          | FStar_Parser_AST.PatOp op ->
              let uu____3202 =
                let uu____3203 =
                  let uu____3204 =
                    let uu____3211 =
                      let uu____3212 =
                        let uu____3217 =
                          FStar_Parser_AST.compile_op (Prims.parse_int "0")
                            op.FStar_Ident.idText op.FStar_Ident.idRange
                           in
                        (uu____3217, (op.FStar_Ident.idRange))  in
                      FStar_Ident.mk_ident uu____3212  in
                    (uu____3211, FStar_Pervasives_Native.None)  in
                  FStar_Parser_AST.PatVar uu____3204  in
                {
                  FStar_Parser_AST.pat = uu____3203;
                  FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                }  in
              aux loc env1 uu____3202
          | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
              let uu____3233 =
                match tacopt with
                | FStar_Pervasives_Native.None  -> ()
                | FStar_Pervasives_Native.Some uu____3234 ->
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                        "Type ascriptions within patterns are cannot be associated with a tactic")
                      orig.FStar_Parser_AST.prange
                 in
              let uu____3235 = aux loc env1 p2  in
              (match uu____3235 with
               | (loc1,env',binder,p3,imp) ->
                   let annot_pat_var p4 t1 =
                     match p4.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_var x ->
                         let uu___114_3291 = p4  in
                         {
                           FStar_Syntax_Syntax.v =
                             (FStar_Syntax_Syntax.Pat_var
                                (let uu___115_3296 = x  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___115_3296.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___115_3296.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = t1
                                 }));
                           FStar_Syntax_Syntax.p =
                             (uu___114_3291.FStar_Syntax_Syntax.p)
                         }
                     | FStar_Syntax_Syntax.Pat_wild x ->
                         let uu___116_3298 = p4  in
                         {
                           FStar_Syntax_Syntax.v =
                             (FStar_Syntax_Syntax.Pat_wild
                                (let uu___117_3303 = x  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___117_3303.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___117_3303.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = t1
                                 }));
                           FStar_Syntax_Syntax.p =
                             (uu___116_3298.FStar_Syntax_Syntax.p)
                         }
                     | uu____3304 when top -> p4
                     | uu____3305 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                             "Type ascriptions within patterns are only allowed on variables")
                           orig.FStar_Parser_AST.prange
                      in
                   let uu____3308 =
                     match binder with
                     | LetBinder uu____3321 -> failwith "impossible"
                     | LocalBinder (x,aq) ->
                         let t1 =
                           let uu____3341 = close_fun env1 t  in
                           desugar_term env1 uu____3341  in
                         let uu____3342 =
                           if
                             match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                             with
                             | FStar_Syntax_Syntax.Tm_unknown  -> false
                             | uu____3343 -> true
                           then
                             let uu____3344 =
                               let uu____3349 =
                                 let uu____3350 =
                                   FStar_Syntax_Print.bv_to_string x  in
                                 let uu____3351 =
                                   FStar_Syntax_Print.term_to_string
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let uu____3352 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 FStar_Util.format3
                                   "Multiple ascriptions for %s in pattern, type %s was shadowed by %s\n"
                                   uu____3350 uu____3351 uu____3352
                                  in
                               (FStar_Errors.Warning_MultipleAscriptions,
                                 uu____3349)
                                in
                             FStar_Errors.log_issue
                               orig.FStar_Parser_AST.prange uu____3344
                           else ()  in
                         let uu____3354 = annot_pat_var p3 t1  in
                         (uu____3354,
                           (LocalBinder
                              ((let uu___118_3360 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___118_3360.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___118_3360.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }), aq)))
                      in
                   (match uu____3308 with
                    | (p4,binder1) -> (loc1, env', binder1, p4, imp)))
          | FStar_Parser_AST.PatWild  ->
              let x =
                FStar_Syntax_Syntax.new_bv
                  (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                  FStar_Syntax_Syntax.tun
                 in
              let uu____3382 =
                FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
              (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                uu____3382, false)
          | FStar_Parser_AST.PatConst c ->
              let x =
                FStar_Syntax_Syntax.new_bv
                  (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                  FStar_Syntax_Syntax.tun
                 in
              let uu____3393 =
                FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                 in
              (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                uu____3393, false)
          | FStar_Parser_AST.PatTvar (x,aq) ->
              let imp =
                aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                 in
              let aq1 = trans_aqual aq  in
              let uu____3414 = resolvex loc env1 x  in
              (match uu____3414 with
               | (loc1,env2,xbv) ->
                   let uu____3436 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_var xbv)
                      in
                   (loc1, env2, (LocalBinder (xbv, aq1)), uu____3436, imp))
          | FStar_Parser_AST.PatVar (x,aq) ->
              let imp =
                aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                 in
              let aq1 = trans_aqual aq  in
              let uu____3457 = resolvex loc env1 x  in
              (match uu____3457 with
               | (loc1,env2,xbv) ->
                   let uu____3479 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_var xbv)
                      in
                   (loc1, env2, (LocalBinder (xbv, aq1)), uu____3479, imp))
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
              let uu____3491 =
                FStar_All.pipe_left pos
                  (FStar_Syntax_Syntax.Pat_cons (l1, []))
                 in
              (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                uu____3491, false)
          | FStar_Parser_AST.PatApp
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                 FStar_Parser_AST.prange = uu____3515;_},args)
              ->
              let uu____3521 =
                FStar_List.fold_right
                  (fun arg  ->
                     fun uu____3562  ->
                       match uu____3562 with
                       | (loc1,env2,args1) ->
                           let uu____3610 = aux loc1 env2 arg  in
                           (match uu____3610 with
                            | (loc2,env3,uu____3639,arg1,imp) ->
                                (loc2, env3, ((arg1, imp) :: args1)))) args
                  (loc, env1, [])
                 in
              (match uu____3521 with
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
                   let uu____3709 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                      in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None)),
                     uu____3709, false))
          | FStar_Parser_AST.PatApp uu____3726 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                p1.FStar_Parser_AST.prange
          | FStar_Parser_AST.PatList pats ->
              let uu____3748 =
                FStar_List.fold_right
                  (fun pat  ->
                     fun uu____3781  ->
                       match uu____3781 with
                       | (loc1,env2,pats1) ->
                           let uu____3813 = aux loc1 env2 pat  in
                           (match uu____3813 with
                            | (loc2,env3,uu____3838,pat1,uu____3840) ->
                                (loc2, env3, (pat1 :: pats1)))) pats
                  (loc, env1, [])
                 in
              (match uu____3748 with
               | (loc1,env2,pats1) ->
                   let pat =
                     let uu____3883 =
                       let uu____3886 =
                         let uu____3892 =
                           FStar_Range.end_range p1.FStar_Parser_AST.prange
                            in
                         pos_r uu____3892  in
                       let uu____3893 =
                         let uu____3894 =
                           let uu____3907 =
                             FStar_Syntax_Syntax.lid_as_fv
                               FStar_Parser_Const.nil_lid
                               FStar_Syntax_Syntax.Delta_constant
                               (FStar_Pervasives_Native.Some
                                  FStar_Syntax_Syntax.Data_ctor)
                              in
                           (uu____3907, [])  in
                         FStar_Syntax_Syntax.Pat_cons uu____3894  in
                       FStar_All.pipe_left uu____3886 uu____3893  in
                     FStar_List.fold_right
                       (fun hd1  ->
                          fun tl1  ->
                            let r =
                              FStar_Range.union_ranges
                                hd1.FStar_Syntax_Syntax.p
                                tl1.FStar_Syntax_Syntax.p
                               in
                            let uu____3939 =
                              let uu____3940 =
                                let uu____3953 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.cons_lid
                                    FStar_Syntax_Syntax.Delta_constant
                                    (FStar_Pervasives_Native.Some
                                       FStar_Syntax_Syntax.Data_ctor)
                                   in
                                (uu____3953, [(hd1, false); (tl1, false)])
                                 in
                              FStar_Syntax_Syntax.Pat_cons uu____3940  in
                            FStar_All.pipe_left (pos_r r) uu____3939) pats1
                       uu____3883
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
              let uu____3997 =
                FStar_List.fold_left
                  (fun uu____4037  ->
                     fun p2  ->
                       match uu____4037 with
                       | (loc1,env2,pats) ->
                           let uu____4086 = aux loc1 env2 p2  in
                           (match uu____4086 with
                            | (loc2,env3,uu____4115,pat,uu____4117) ->
                                (loc2, env3, ((pat, false) :: pats))))
                  (loc, env1, []) args
                 in
              (match uu____3997 with
               | (loc1,env2,args1) ->
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
                   let uu____4212 =
                     FStar_Syntax_DsEnv.fail_or env2
                       (FStar_Syntax_DsEnv.try_lookup_lid env2) l
                      in
                   (match uu____4212 with
                    | (constr,uu____4234) ->
                        let l1 =
                          match constr.FStar_Syntax_Syntax.n with
                          | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                          | uu____4237 -> failwith "impossible"  in
                        let x =
                          FStar_Syntax_Syntax.new_bv
                            (FStar_Pervasives_Native.Some
                               (p1.FStar_Parser_AST.prange))
                            FStar_Syntax_Syntax.tun
                           in
                        let uu____4239 =
                          FStar_All.pipe_left pos
                            (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                           in
                        (loc1, env2,
                          (LocalBinder (x, FStar_Pervasives_Native.None)),
                          uu____4239, false)))
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
                     (fun uu____4310  ->
                        match uu____4310 with
                        | (f,p2) -> ((f.FStar_Ident.ident), p2)))
                 in
              let args =
                FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                  (FStar_List.map
                     (fun uu____4340  ->
                        match uu____4340 with
                        | (f,uu____4346) ->
                            let uu____4347 =
                              FStar_All.pipe_right fields1
                                (FStar_List.tryFind
                                   (fun uu____4373  ->
                                      match uu____4373 with
                                      | (g,uu____4379) ->
                                          f.FStar_Ident.idText =
                                            g.FStar_Ident.idText))
                               in
                            (match uu____4347 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Parser_AST.mk_pattern
                                   FStar_Parser_AST.PatWild
                                   p1.FStar_Parser_AST.prange
                             | FStar_Pervasives_Native.Some (uu____4384,p2)
                                 -> p2)))
                 in
              let app =
                let uu____4391 =
                  let uu____4392 =
                    let uu____4399 =
                      let uu____4400 =
                        let uu____4401 =
                          FStar_Ident.lid_of_ids
                            (FStar_List.append
                               (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                               [record.FStar_Syntax_DsEnv.constrname])
                           in
                        FStar_Parser_AST.PatName uu____4401  in
                      FStar_Parser_AST.mk_pattern uu____4400
                        p1.FStar_Parser_AST.prange
                       in
                    (uu____4399, args)  in
                  FStar_Parser_AST.PatApp uu____4392  in
                FStar_Parser_AST.mk_pattern uu____4391
                  p1.FStar_Parser_AST.prange
                 in
              let uu____4404 = aux loc env1 app  in
              (match uu____4404 with
               | (env2,e,b,p2,uu____4433) ->
                   let p3 =
                     match p2.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                         let uu____4461 =
                           let uu____4462 =
                             let uu____4475 =
                               let uu___119_4476 = fv  in
                               let uu____4477 =
                                 let uu____4480 =
                                   let uu____4481 =
                                     let uu____4488 =
                                       FStar_All.pipe_right
                                         record.FStar_Syntax_DsEnv.fields
                                         (FStar_List.map
                                            FStar_Pervasives_Native.fst)
                                        in
                                     ((record.FStar_Syntax_DsEnv.typename),
                                       uu____4488)
                                      in
                                   FStar_Syntax_Syntax.Record_ctor uu____4481
                                    in
                                 FStar_Pervasives_Native.Some uu____4480  in
                               {
                                 FStar_Syntax_Syntax.fv_name =
                                   (uu___119_4476.FStar_Syntax_Syntax.fv_name);
                                 FStar_Syntax_Syntax.fv_delta =
                                   (uu___119_4476.FStar_Syntax_Syntax.fv_delta);
                                 FStar_Syntax_Syntax.fv_qual = uu____4477
                               }  in
                             (uu____4475, args1)  in
                           FStar_Syntax_Syntax.Pat_cons uu____4462  in
                         FStar_All.pipe_left pos uu____4461
                     | uu____4515 -> p2  in
                   (env2, e, b, p3, false))
        
        and aux loc env1 p1 = aux' false loc env1 p1
         in
        let aux_maybe_or env1 p1 =
          let loc = []  in
          match p1.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOr [] -> failwith "impossible"
          | FStar_Parser_AST.PatOr (p2::ps) ->
              let uu____4567 = aux' true loc env1 p2  in
              (match uu____4567 with
               | (loc1,env2,var,p3,uu____4594) ->
                   let uu____4599 =
                     FStar_List.fold_left
                       (fun uu____4631  ->
                          fun p4  ->
                            match uu____4631 with
                            | (loc2,env3,ps1) ->
                                let uu____4664 = aux' true loc2 env3 p4  in
                                (match uu____4664 with
                                 | (loc3,env4,uu____4689,p5,uu____4691) ->
                                     (loc3, env4, (p5 :: ps1))))
                       (loc1, env2, []) ps
                      in
                   (match uu____4599 with
                    | (loc2,env3,ps1) ->
                        let pats = p3 :: (FStar_List.rev ps1)  in
                        (env3, var, pats)))
          | uu____4742 ->
              let uu____4743 = aux' true loc env1 p1  in
              (match uu____4743 with
               | (loc1,env2,vars,pat,b) -> (env2, vars, [pat]))
           in
        let uu____4783 = aux_maybe_or env p  in
        match uu____4783 with
        | (env1,b,pats) ->
            let uu____4813 =
              check_linear_pattern_variables pats p.FStar_Parser_AST.prange
               in
            (env1, b, pats)

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
            let uu____4843 =
              let uu____4844 =
                let uu____4855 = FStar_Syntax_DsEnv.qualify env x  in
                (uu____4855,
                  (FStar_Syntax_Syntax.tun, FStar_Pervasives_Native.None))
                 in
              LetBinder uu____4844  in
            (env, uu____4843, [])  in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____4883 =
                  let uu____4884 =
                    let uu____4889 =
                      FStar_Parser_AST.compile_op (Prims.parse_int "0")
                        x.FStar_Ident.idText x.FStar_Ident.idRange
                       in
                    (uu____4889, (x.FStar_Ident.idRange))  in
                  FStar_Ident.mk_ident uu____4884  in
                mklet uu____4883
            | FStar_Parser_AST.PatVar (x,uu____4891) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____4897);
                   FStar_Parser_AST.prange = uu____4898;_},(t,tacopt))
                ->
                let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)
                   in
                let uu____4918 =
                  let uu____4919 =
                    let uu____4930 = FStar_Syntax_DsEnv.qualify env x  in
                    let uu____4931 =
                      let uu____4938 = desugar_term env t  in
                      (uu____4938, tacopt1)  in
                    (uu____4930, uu____4931)  in
                  LetBinder uu____4919  in
                (env, uu____4918, [])
            | uu____4949 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_UnexpectedPattern,
                    "Unexpected pattern at the top-level")
                  p.FStar_Parser_AST.prange
          else
            (let uu____4959 = desugar_data_pat env p is_mut  in
             match uu____4959 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1 with
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                         uu____4988;
                       FStar_Syntax_Syntax.p = uu____4989;_}::[] -> []
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                         uu____4994;
                       FStar_Syntax_Syntax.p = uu____4995;_}::[] -> []
                   | uu____5000 -> p1  in
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
  fun uu____5007  ->
    fun env  ->
      fun pat  ->
        let uu____5010 = desugar_data_pat env pat false  in
        match uu____5010 with | (env1,uu____5026,pat1) -> (env1, pat1)

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
      let uu____5045 = desugar_term_aq env e  in
      match uu____5045 with | (t,aq) -> let uu____5052 = check_no_aq aq  in t

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
      let uu____5062 = desugar_typ_aq env e  in
      match uu____5062 with | (t,aq) -> let uu____5069 = check_no_aq aq  in t

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness,FStar_Const.width)
        FStar_Pervasives_Native.tuple2 ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____5072  ->
        fun range  ->
          match uu____5072 with
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
              let uu____5081 =
                let uu____5082 =
                  let uu____5083 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____5083  in
                if uu____5082
                then
                  let uu____5084 =
                    let uu____5089 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____5089)  in
                  FStar_Errors.log_issue range uu____5084
                else ()  in
              let private_intro_nm =
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
                let uu____5094 = FStar_Ident.path_of_text intro_nm  in
                FStar_Ident.lid_of_path uu____5094 range  in
              let lid1 =
                let uu____5098 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                   in
                match uu____5098 with
                | FStar_Pervasives_Native.Some (intro_term,uu____5108) ->
                    (match intro_term.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let private_lid =
                           let uu____5117 =
                             FStar_Ident.path_of_text private_intro_nm  in
                           FStar_Ident.lid_of_path uu____5117 range  in
                         let private_fv =
                           let uu____5119 =
                             FStar_Syntax_Util.incr_delta_depth
                               fv.FStar_Syntax_Syntax.fv_delta
                              in
                           FStar_Syntax_Syntax.lid_as_fv private_lid
                             uu____5119 fv.FStar_Syntax_Syntax.fv_qual
                            in
                         let uu___120_5120 = intro_term  in
                         {
                           FStar_Syntax_Syntax.n =
                             (FStar_Syntax_Syntax.Tm_fvar private_fv);
                           FStar_Syntax_Syntax.pos =
                             (uu___120_5120.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___120_5120.FStar_Syntax_Syntax.vars)
                         }
                     | uu____5121 ->
                         failwith
                           (Prims.strcat "Unexpected non-fvar for " intro_nm))
                | FStar_Pervasives_Native.None  ->
                    let uu____5128 =
                      let uu____5133 =
                        FStar_Util.format1
                          "Unexpected numeric literal.  Restart F* to load %s."
                          tnm
                         in
                      (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                        uu____5133)
                       in
                    FStar_Errors.raise_error uu____5128 range
                 in
              let repr1 =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_int
                        (repr, FStar_Pervasives_Native.None)))
                  FStar_Pervasives_Native.None range
                 in
              let uu____5149 =
                let uu____5154 =
                  let uu____5155 =
                    let uu____5170 =
                      let uu____5179 =
                        let uu____5186 =
                          FStar_Syntax_Syntax.as_implicit false  in
                        (repr1, uu____5186)  in
                      [uu____5179]  in
                    (lid1, uu____5170)  in
                  FStar_Syntax_Syntax.Tm_app uu____5155  in
                FStar_Syntax_Syntax.mk uu____5154  in
              uu____5149 FStar_Pervasives_Native.None range

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
            let uu____5225 =
              FStar_Syntax_DsEnv.fail_or env
                ((if resolve
                  then FStar_Syntax_DsEnv.try_lookup_lid_with_attributes
                  else
                    FStar_Syntax_DsEnv.try_lookup_lid_with_attributes_no_resolve)
                   env) l
               in
            match uu____5225 with
            | (tm,mut,attrs) ->
                let warn_if_deprecated attrs1 =
                  FStar_List.iter
                    (fun a  ->
                       match a.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_app
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____5273;
                              FStar_Syntax_Syntax.vars = uu____5274;_},args)
                           when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____5297 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____5297 " is deprecated"  in
                           let msg1 =
                             if
                               (FStar_List.length args) >
                                 (Prims.parse_int "0")
                             then
                               let uu____5305 =
                                 let uu____5306 =
                                   let uu____5309 = FStar_List.hd args  in
                                   FStar_Pervasives_Native.fst uu____5309  in
                                 uu____5306.FStar_Syntax_Syntax.n  in
                               match uu____5305 with
                               | FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_string (s,uu____5325))
                                   when
                                   Prims.op_Negation
                                     ((FStar_Util.trim_string s) = "")
                                   ->
                                   Prims.strcat msg
                                     (Prims.strcat ", use "
                                        (Prims.strcat s " instead"))
                               | uu____5326 -> msg
                             else msg  in
                           let uu____5328 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____5328
                             (FStar_Errors.Warning_DeprecatedDefinition,
                               msg1)
                       | FStar_Syntax_Syntax.Tm_fvar fv when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____5331 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____5331 " is deprecated"  in
                           let uu____5332 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____5332
                             (FStar_Errors.Warning_DeprecatedDefinition, msg)
                       | uu____5333 -> ()) attrs1
                   in
                let uu____5334 = warn_if_deprecated attrs  in
                let tm1 = setpos tm  in
                if mut
                then
                  let uu____5338 =
                    let uu____5339 =
                      let uu____5346 = mk_ref_read tm1  in
                      (uu____5346,
                        (FStar_Syntax_Syntax.Meta_desugared
                           FStar_Syntax_Syntax.Mutable_rval))
                       in
                    FStar_Syntax_Syntax.Tm_meta uu____5339  in
                  FStar_All.pipe_left mk1 uu____5338
                else tm1

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____5363 =
          let uu____5364 = unparen t  in uu____5364.FStar_Parser_AST.tm  in
        match uu____5363 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____5365; FStar_Ident.ident = uu____5366;
              FStar_Ident.nsstr = uu____5367; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____5370 ->
            let uu____5371 =
              let uu____5376 =
                let uu____5377 = FStar_Parser_AST.term_to_string t  in
                Prims.strcat "Unknown attribute " uu____5377  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____5376)  in
            FStar_Errors.raise_error uu____5371 t.FStar_Parser_AST.range
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
          let uu___121_5469 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___121_5469.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___121_5469.FStar_Syntax_Syntax.vars)
          }  in
        let uu____5472 =
          let uu____5473 = unparen top  in uu____5473.FStar_Parser_AST.tm  in
        match uu____5472 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____5490 ->
            let uu____5497 = desugar_formula env top  in (uu____5497, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____5514 = desugar_formula env t  in (uu____5514, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____5531 = desugar_formula env t  in (uu____5531, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____5565 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____5565, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____5577 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____5577, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____5599 =
                let uu____5600 =
                  let uu____5607 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____5607, args)  in
                FStar_Parser_AST.Op uu____5600  in
              FStar_Parser_AST.mk_term uu____5599 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____5610 =
              let uu____5611 =
                let uu____5612 =
                  let uu____5619 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____5619, [e])  in
                FStar_Parser_AST.Op uu____5612  in
              FStar_Parser_AST.mk_term uu____5611 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____5610
        | FStar_Parser_AST.Op (op_star,uu____5623::uu____5624::[]) when
            (let uu____5629 = FStar_Ident.text_of_id op_star  in
             uu____5629 = "*") &&
              (let uu____5631 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____5631 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____5645;_},t1::t2::[])
                  ->
                  let uu____5650 = flatten1 t1  in
                  FStar_List.append uu____5650 [t2]
              | uu____5653 -> [t]  in
            let uu____5654 =
              let uu____5663 =
                let uu____5670 =
                  let uu____5673 = unparen top  in flatten1 uu____5673  in
                FStar_All.pipe_right uu____5670
                  (FStar_List.map
                     (fun t  ->
                        let uu____5692 = desugar_typ_aq env t  in
                        match uu____5692 with
                        | (t',aq) ->
                            let uu____5703 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____5703, aq)))
                 in
              FStar_All.pipe_right uu____5663 FStar_List.unzip  in
            (match uu____5654 with
             | (targs,aqs) ->
                 let uu____5732 =
                   let uu____5737 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____5737
                    in
                 (match uu____5732 with
                  | (tup,uu____5747) ->
                      let uu____5748 =
                        mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                      (uu____5748, (join_aqs aqs))))
        | FStar_Parser_AST.Tvar a ->
            let uu____5766 =
              let uu____5769 =
                let uu____5772 =
                  FStar_Syntax_DsEnv.fail_or2
                    (FStar_Syntax_DsEnv.try_lookup_id env) a
                   in
                FStar_Pervasives_Native.fst uu____5772  in
              FStar_All.pipe_left setpos uu____5769  in
            (uu____5766, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____5798 =
              let uu____5803 =
                let uu____5804 =
                  let uu____5805 = FStar_Ident.text_of_id u  in
                  Prims.strcat uu____5805 " in non-universe context"  in
                Prims.strcat "Unexpected universe variable " uu____5804  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____5803)  in
            FStar_Errors.raise_error uu____5798 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____5816 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____5816 with
             | FStar_Pervasives_Native.None  ->
                 let uu____5823 =
                   let uu____5828 =
                     let uu____5829 = FStar_Ident.text_of_id s  in
                     Prims.strcat "Unexpected or unbound operator: "
                       uu____5829
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____5828)
                    in
                 FStar_Errors.raise_error uu____5823
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let uu____5839 =
                     let uu____5854 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____5896 = desugar_term_aq env t  in
                               match uu____5896 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____5854 FStar_List.unzip  in
                   (match uu____5839 with
                    | (args1,aqs) ->
                        let uu____5979 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____5979, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____6015)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____6030 =
              let uu___122_6031 = top  in
              let uu____6032 =
                let uu____6033 =
                  let uu____6040 =
                    let uu___123_6041 = top  in
                    let uu____6042 =
                      let uu____6043 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____6043  in
                    {
                      FStar_Parser_AST.tm = uu____6042;
                      FStar_Parser_AST.range =
                        (uu___123_6041.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___123_6041.FStar_Parser_AST.level)
                    }  in
                  (uu____6040, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____6033  in
              {
                FStar_Parser_AST.tm = uu____6032;
                FStar_Parser_AST.range =
                  (uu___122_6031.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___122_6031.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____6030
        | FStar_Parser_AST.Construct (n1,(a,uu____6046)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            let uu____6061 =
              FStar_Errors.log_issue top.FStar_Parser_AST.range
                (FStar_Errors.Warning_SMTPatTDeprecated,
                  "SMTPatT is deprecated; please just use SMTPat")
               in
            let uu____6062 =
              let uu___124_6063 = top  in
              let uu____6064 =
                let uu____6065 =
                  let uu____6072 =
                    let uu___125_6073 = top  in
                    let uu____6074 =
                      let uu____6075 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____6075  in
                    {
                      FStar_Parser_AST.tm = uu____6074;
                      FStar_Parser_AST.range =
                        (uu___125_6073.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___125_6073.FStar_Parser_AST.level)
                    }  in
                  (uu____6072, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____6065  in
              {
                FStar_Parser_AST.tm = uu____6064;
                FStar_Parser_AST.range =
                  (uu___124_6063.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___124_6063.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____6062
        | FStar_Parser_AST.Construct (n1,(a,uu____6078)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____6093 =
              let uu___126_6094 = top  in
              let uu____6095 =
                let uu____6096 =
                  let uu____6103 =
                    let uu___127_6104 = top  in
                    let uu____6105 =
                      let uu____6106 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____6106  in
                    {
                      FStar_Parser_AST.tm = uu____6105;
                      FStar_Parser_AST.range =
                        (uu___127_6104.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___127_6104.FStar_Parser_AST.level)
                    }  in
                  (uu____6103, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____6096  in
              {
                FStar_Parser_AST.tm = uu____6095;
                FStar_Parser_AST.range =
                  (uu___126_6094.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___126_6094.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____6093
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____6107; FStar_Ident.ident = uu____6108;
              FStar_Ident.nsstr = uu____6109; FStar_Ident.str = "Type0";_}
            ->
            let uu____6112 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____6112, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____6127; FStar_Ident.ident = uu____6128;
              FStar_Ident.nsstr = uu____6129; FStar_Ident.str = "Type";_}
            ->
            let uu____6132 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____6132, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____6147; FStar_Ident.ident = uu____6148;
               FStar_Ident.nsstr = uu____6149; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____6167 =
              let uu____6170 =
                let uu____6171 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____6171  in
              mk1 uu____6170  in
            (uu____6167, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____6184; FStar_Ident.ident = uu____6185;
              FStar_Ident.nsstr = uu____6186; FStar_Ident.str = "Effect";_}
            ->
            let uu____6189 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____6189, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____6204; FStar_Ident.ident = uu____6205;
              FStar_Ident.nsstr = uu____6206; FStar_Ident.str = "True";_}
            ->
            let uu____6209 =
              let uu____6210 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____6210
                FStar_Syntax_Syntax.Delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____6209, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____6221; FStar_Ident.ident = uu____6222;
              FStar_Ident.nsstr = uu____6223; FStar_Ident.str = "False";_}
            ->
            let uu____6226 =
              let uu____6227 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____6227
                FStar_Syntax_Syntax.Delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____6226, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____6240;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            let uu____6241 =
              FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name
               in
            let uu____6242 =
              FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
            (match uu____6242 with
             | FStar_Pervasives_Native.Some ed ->
                 let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                 let uu____6251 =
                   FStar_Syntax_Syntax.fvar lid
                     (FStar_Syntax_Syntax.Delta_defined_at_level
                        (Prims.parse_int "1")) FStar_Pervasives_Native.None
                    in
                 (uu____6251, noaqs)
             | FStar_Pervasives_Native.None  ->
                 let uu____6262 =
                   let uu____6263 = FStar_Ident.text_of_lid eff_name  in
                   FStar_Util.format2
                     "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                     uu____6263 txt
                    in
                 failwith uu____6262)
        | FStar_Parser_AST.Var l ->
            let uu____6269 =
              FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l  in
            let uu____6270 = desugar_name mk1 setpos env true l  in
            (uu____6270, noaqs)
        | FStar_Parser_AST.Name l ->
            let uu____6282 =
              FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l  in
            let uu____6283 = desugar_name mk1 setpos env true l  in
            (uu____6283, noaqs)
        | FStar_Parser_AST.Projector (l,i) ->
            let uu____6296 =
              FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l  in
            let name =
              let uu____6304 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____6304 with
              | FStar_Pervasives_Native.Some uu____6313 ->
                  FStar_Pervasives_Native.Some (true, l)
              | FStar_Pervasives_Native.None  ->
                  let uu____6318 =
                    FStar_Syntax_DsEnv.try_lookup_root_effect_name env l  in
                  (match uu____6318 with
                   | FStar_Pervasives_Native.Some new_name ->
                       FStar_Pervasives_Native.Some (false, new_name)
                   | uu____6332 -> FStar_Pervasives_Native.None)
               in
            (match name with
             | FStar_Pervasives_Native.Some (resolve,new_name) ->
                 let uu____6349 =
                   let uu____6350 =
                     FStar_Syntax_Util.mk_field_projector_name_from_ident
                       new_name i
                      in
                   desugar_name mk1 setpos env resolve uu____6350  in
                 (uu____6349, noaqs)
             | uu____6361 ->
                 let uu____6368 =
                   let uu____6373 =
                     FStar_Util.format1
                       "Data constructor or effect %s not found"
                       l.FStar_Ident.str
                      in
                   (FStar_Errors.Fatal_EffectNotFound, uu____6373)  in
                 FStar_Errors.raise_error uu____6368
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Discrim lid ->
            let uu____6379 =
              FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid  in
            let uu____6380 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
               in
            (match uu____6380 with
             | FStar_Pervasives_Native.None  ->
                 let uu____6387 =
                   let uu____6392 =
                     FStar_Util.format1 "Data constructor %s not found"
                       lid.FStar_Ident.str
                      in
                   (FStar_Errors.Fatal_DataContructorNotFound, uu____6392)
                    in
                 FStar_Errors.raise_error uu____6387
                   top.FStar_Parser_AST.range
             | uu____6397 ->
                 let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                 let uu____6401 = desugar_name mk1 setpos env true lid'  in
                 (uu____6401, noaqs))
        | FStar_Parser_AST.Construct (l,args) ->
            let uu____6426 =
              FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l  in
            let uu____6427 = FStar_Syntax_DsEnv.try_lookup_datacon env l  in
            (match uu____6427 with
             | FStar_Pervasives_Native.Some head1 ->
                 let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                 (match args with
                  | [] -> (head2, noaqs)
                  | uu____6458 ->
                      let uu____6465 =
                        FStar_Util.take
                          (fun uu____6489  ->
                             match uu____6489 with
                             | (uu____6494,imp) ->
                                 imp = FStar_Parser_AST.UnivApp) args
                         in
                      (match uu____6465 with
                       | (universes,args1) ->
                           let universes1 =
                             FStar_List.map
                               (fun x  ->
                                  desugar_universe
                                    (FStar_Pervasives_Native.fst x))
                               universes
                              in
                           let uu____6539 =
                             let uu____6554 =
                               FStar_List.map
                                 (fun uu____6587  ->
                                    match uu____6587 with
                                    | (t,imp) ->
                                        let uu____6604 =
                                          desugar_term_aq env t  in
                                        (match uu____6604 with
                                         | (te,aq) ->
                                             ((arg_withimp_e imp te), aq)))
                                 args1
                                in
                             FStar_All.pipe_right uu____6554 FStar_List.unzip
                              in
                           (match uu____6539 with
                            | (args2,aqs) ->
                                let head3 =
                                  if universes1 = []
                                  then head2
                                  else
                                    mk1
                                      (FStar_Syntax_Syntax.Tm_uinst
                                         (head2, universes1))
                                   in
                                let uu____6697 =
                                  mk1
                                    (FStar_Syntax_Syntax.Tm_app
                                       (head3, args2))
                                   in
                                (uu____6697, (join_aqs aqs)))))
             | FStar_Pervasives_Native.None  ->
                 let err =
                   let uu____6727 =
                     FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                   match uu____6727 with
                   | FStar_Pervasives_Native.None  ->
                       (FStar_Errors.Fatal_ConstructorNotFound,
                         (Prims.strcat "Constructor "
                            (Prims.strcat l.FStar_Ident.str " not found")))
                   | FStar_Pervasives_Native.Some uu____6734 ->
                       (FStar_Errors.Fatal_UnexpectedEffect,
                         (Prims.strcat "Effect "
                            (Prims.strcat l.FStar_Ident.str
                               " used at an unexpected position")))
                    in
                 FStar_Errors.raise_error err top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____6745 =
              FStar_List.fold_left
                (fun uu____6790  ->
                   fun b  ->
                     match uu____6790 with
                     | (env1,tparams,typs) ->
                         let uu____6847 = desugar_binder env1 b  in
                         (match uu____6847 with
                          | (xopt,t1) ->
                              let uu____6876 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____6885 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____6885)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____6876 with
                               | (env2,x) ->
                                   let uu____6905 =
                                     let uu____6908 =
                                       let uu____6911 =
                                         let uu____6912 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____6912
                                          in
                                       [uu____6911]  in
                                     FStar_List.append typs uu____6908  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___128_6938 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___128_6938.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___128_6938.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____6905)))) (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      FStar_Pervasives_Native.None])
               in
            (match uu____6745 with
             | (env1,uu____6966,targs) ->
                 let uu____6988 =
                   let uu____6993 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____6993
                    in
                 (match uu____6988 with
                  | (tup,uu____7003) ->
                      let uu____7004 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_app (tup, targs))
                         in
                      (uu____7004, noaqs)))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____7029 = uncurry binders t  in
            (match uu____7029 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___94_7068 =
                   match uu___94_7068 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1  in
                       let uu____7082 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____7082
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____7104 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____7104 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____7113 = aux env [] bs  in (uu____7113, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____7134 = desugar_binder env b  in
            (match uu____7134 with
             | (FStar_Pervasives_Native.None ,uu____7145) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____7159 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____7159 with
                  | ((x,uu____7169),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____7176 =
                        let uu____7179 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____7179  in
                      (uu____7176, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern)
               in
            let uu____7211 =
              FStar_List.fold_left
                (fun uu____7231  ->
                   fun pat  ->
                     match uu____7231 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed
                              (uu____7257,(t,FStar_Pervasives_Native.None ))
                              ->
                              let uu____7267 =
                                let uu____7270 = free_type_vars env1 t  in
                                FStar_List.append uu____7270 ftvs  in
                              (env1, uu____7267)
                          | FStar_Parser_AST.PatAscribed
                              (uu____7275,(t,FStar_Pervasives_Native.Some
                                           tac))
                              ->
                              let uu____7286 =
                                let uu____7289 = free_type_vars env1 t  in
                                let uu____7292 =
                                  let uu____7295 = free_type_vars env1 tac
                                     in
                                  FStar_List.append uu____7295 ftvs  in
                                FStar_List.append uu____7289 uu____7292  in
                              (env1, uu____7286)
                          | uu____7300 -> (env1, ftvs))) (env, []) binders1
               in
            (match uu____7211 with
             | (uu____7309,ftv) ->
                 let ftv1 = sort_ftv ftv  in
                 let binders2 =
                   let uu____7321 =
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
                   FStar_List.append uu____7321 binders1  in
                 let rec aux env1 bs sc_pat_opt uu___95_7370 =
                   match uu___95_7370 with
                   | [] ->
                       let uu____7393 = desugar_term_aq env1 body  in
                       (match uu____7393 with
                        | (body1,aq) ->
                            let body2 =
                              match sc_pat_opt with
                              | FStar_Pervasives_Native.Some (sc,pat) ->
                                  let body2 =
                                    let uu____7424 =
                                      let uu____7425 =
                                        FStar_Syntax_Syntax.pat_bvs pat  in
                                      FStar_All.pipe_right uu____7425
                                        (FStar_List.map
                                           FStar_Syntax_Syntax.mk_binder)
                                       in
                                    FStar_Syntax_Subst.close uu____7424 body1
                                     in
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_match
                                       (sc,
                                         [(pat, FStar_Pervasives_Native.None,
                                            body2)]))
                                    FStar_Pervasives_Native.None
                                    body2.FStar_Syntax_Syntax.pos
                              | FStar_Pervasives_Native.None  -> body1  in
                            let uu____7478 =
                              let uu____7481 =
                                no_annot_abs (FStar_List.rev bs) body2  in
                              setpos uu____7481  in
                            (uu____7478, aq))
                   | p::rest ->
                       let uu____7494 = desugar_binding_pat env1 p  in
                       (match uu____7494 with
                        | (env2,b,pat) ->
                            let pat1 =
                              match pat with
                              | [] -> FStar_Pervasives_Native.None
                              | p1::[] -> FStar_Pervasives_Native.Some p1
                              | uu____7522 ->
                                  FStar_Errors.raise_error
                                    (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                      "Disjunctive patterns are not supported in abstractions")
                                    p.FStar_Parser_AST.prange
                               in
                            let uu____7527 =
                              match b with
                              | LetBinder uu____7560 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat1, sc_pat_opt) with
                                    | (FStar_Pervasives_Native.None
                                       ,uu____7616) -> sc_pat_opt
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.None ) ->
                                        let uu____7652 =
                                          let uu____7657 =
                                            FStar_Syntax_Syntax.bv_to_name x
                                             in
                                          (uu____7657, p1)  in
                                        FStar_Pervasives_Native.Some
                                          uu____7652
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.Some
                                       (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____7693,uu____7694) ->
                                             let tup2 =
                                               let uu____7696 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____7696
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____7700 =
                                                 let uu____7705 =
                                                   let uu____7706 =
                                                     let uu____7721 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2)
                                                        in
                                                     let uu____7724 =
                                                       let uu____7727 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc
                                                          in
                                                       let uu____7728 =
                                                         let uu____7731 =
                                                           let uu____7732 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x
                                                              in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____7732
                                                            in
                                                         [uu____7731]  in
                                                       uu____7727 ::
                                                         uu____7728
                                                        in
                                                     (uu____7721, uu____7724)
                                                      in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____7706
                                                    in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____7705
                                                  in
                                               uu____7700
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Parser_AST.range
                                                in
                                             let p2 =
                                               let uu____7743 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p1, false)]))
                                                 uu____7743
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____7774,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____7776,pats)) ->
                                             let tupn =
                                               let uu____7815 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____7815
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____7825 =
                                                 let uu____7826 =
                                                   let uu____7841 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn)
                                                      in
                                                   let uu____7844 =
                                                     let uu____7853 =
                                                       let uu____7862 =
                                                         let uu____7863 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____7863
                                                          in
                                                       [uu____7862]  in
                                                     FStar_List.append args
                                                       uu____7853
                                                      in
                                                   (uu____7841, uu____7844)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____7826
                                                  in
                                               mk1 uu____7825  in
                                             let p2 =
                                               let uu____7883 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p1, false)])))
                                                 uu____7883
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | uu____7918 ->
                                             failwith "Impossible")
                                     in
                                  ((x, aq), sc_pat_opt1)
                               in
                            (match uu____7527 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest))
                    in
                 aux env [] FStar_Pervasives_Native.None binders2)
        | FStar_Parser_AST.App
            (uu____7989,uu____7990,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____8010 =
                let uu____8011 = unparen e  in uu____8011.FStar_Parser_AST.tm
                 in
              match uu____8010 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____8021 ->
                  let uu____8022 = desugar_term_aq env e  in
                  (match uu____8022 with
                   | (head1,aq) ->
                       let uu____8035 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____8035, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____8042 ->
            let rec aux args aqs e =
              let uu____8098 =
                let uu____8099 = unparen e  in uu____8099.FStar_Parser_AST.tm
                 in
              match uu____8098 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____8119 = desugar_term_aq env t  in
                  (match uu____8119 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____8155 ->
                  let uu____8156 = desugar_term_aq env e  in
                  (match uu____8156 with
                   | (head1,aq) ->
                       let uu____8179 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____8179, (join_aqs (aq :: aqs))))
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
            let uu____8219 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____8219
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
            let uu____8271 = desugar_term_aq env t  in
            (match uu____8271 with
             | (tm,s) ->
                 let uu____8282 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____8282, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____8290 =
              let uu____8301 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____8301 then desugar_typ_aq else desugar_term_aq  in
            uu____8290 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____8355 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____8498  ->
                        match uu____8498 with
                        | (attr_opt,(p,def)) ->
                            let uu____8556 = is_app_pattern p  in
                            if uu____8556
                            then
                              let uu____8587 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____8587, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____8669 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____8669, def1)
                               | uu____8714 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____8752);
                                           FStar_Parser_AST.prange =
                                             uu____8753;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____8801 =
                                            let uu____8822 =
                                              let uu____8827 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____8827  in
                                            (uu____8822, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____8801, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____8918) ->
                                        if top_level
                                        then
                                          let uu____8953 =
                                            let uu____8974 =
                                              let uu____8979 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____8979  in
                                            (uu____8974, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____8953, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____9069 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____9100 =
                FStar_List.fold_left
                  (fun uu____9173  ->
                     fun uu____9174  ->
                       match (uu____9173, uu____9174) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____9282,uu____9283),uu____9284))
                           ->
                           let uu____9401 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____9427 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____9427 with
                                  | (env2,xx) ->
                                      let uu____9446 =
                                        let uu____9449 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____9449 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx), uu____9446))
                             | FStar_Util.Inr l ->
                                 let uu____9457 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.Delta_equational
                                    in
                                 (uu____9457, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____9401 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____9100 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____9602 =
                    match uu____9602 with
                    | (attrs_opt,(uu____9638,args,result_t),def) ->
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
                                let uu____9726 = is_comp_type env1 t  in
                                if uu____9726
                                then
                                  let uu____9727 =
                                    let uu____9728 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____9738 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____9738))
                                       in
                                    match uu____9728 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange
                                     in
                                  t
                                else
                                  (let uu____9741 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____9743 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____9743))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____9741
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t)
                                 in
                              let uu____9747 =
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range
                                 in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed (def, t1, tacopt))
                                uu____9747 FStar_Parser_AST.Expr
                           in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____9751 ->
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
                              let uu____9766 =
                                let uu____9767 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____9767
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____9766
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
                  let uu____9826 = desugar_term_aq env' body  in
                  (match uu____9826 with
                   | (body1,aq) ->
                       let uu____9839 =
                         let uu____9842 =
                           let uu____9843 =
                             let uu____9856 =
                               FStar_Syntax_Subst.close rec_bindings1 body1
                                in
                             ((is_rec, lbs1), uu____9856)  in
                           FStar_Syntax_Syntax.Tm_let uu____9843  in
                         FStar_All.pipe_left mk1 uu____9842  in
                       (uu____9839, aq))
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
              let uu____9920 =
                desugar_binding_pat_maybe_top top_level env pat is_mutable
                 in
              match uu____9920 with
              | (env1,binder,pat1) ->
                  let uu____9942 =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let uu____9968 = desugar_term_aq env1 t2  in
                        (match uu____9968 with
                         | (body1,aq) ->
                             let fv =
                               let uu____9982 =
                                 FStar_Syntax_Util.incr_delta_qualifier t12
                                  in
                               FStar_Syntax_Syntax.lid_as_fv l uu____9982
                                 FStar_Pervasives_Native.None
                                in
                             let uu____9983 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t12,
                                            (t12.FStar_Syntax_Syntax.pos))]),
                                      body1))
                                in
                             (uu____9983, aq))
                    | LocalBinder (x,uu____10007) ->
                        let uu____10008 = desugar_term_aq env1 t2  in
                        (match uu____10008 with
                         | (body1,aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | {
                                   FStar_Syntax_Syntax.v =
                                     FStar_Syntax_Syntax.Pat_wild uu____10022;
                                   FStar_Syntax_Syntax.p = uu____10023;_}::[]
                                   -> body1
                               | uu____10028 ->
                                   let uu____10031 =
                                     let uu____10036 =
                                       let uu____10037 =
                                         let uu____10060 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         let uu____10061 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1
                                            in
                                         (uu____10060, uu____10061)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____10037
                                        in
                                     FStar_Syntax_Syntax.mk uu____10036  in
                                   uu____10031 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range
                                in
                             let uu____10071 =
                               let uu____10074 =
                                 let uu____10075 =
                                   let uu____10088 =
                                     let uu____10089 =
                                       let uu____10090 =
                                         FStar_Syntax_Syntax.mk_binder x  in
                                       [uu____10090]  in
                                     FStar_Syntax_Subst.close uu____10089
                                       body2
                                      in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t12,
                                           (t12.FStar_Syntax_Syntax.pos))]),
                                     uu____10088)
                                    in
                                 FStar_Syntax_Syntax.Tm_let uu____10075  in
                               FStar_All.pipe_left mk1 uu____10074  in
                             (uu____10071, aq))
                     in
                  (match uu____9942 with
                   | (tm,aq) ->
                       if is_mutable
                       then
                         let uu____10131 =
                           FStar_All.pipe_left mk1
                             (FStar_Syntax_Syntax.Tm_meta
                                (tm,
                                  (FStar_Syntax_Syntax.Meta_desugared
                                     FStar_Syntax_Syntax.Mutable_alloc)))
                            in
                         (uu____10131, aq)
                       else (tm, aq))
               in
            let uu____10143 = FStar_List.hd lbs  in
            (match uu____10143 with
             | (attrs,(head_pat,defn)) ->
                 let uu____10187 = is_rec || (is_app_pattern head_pat)  in
                 if uu____10187
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____10200 =
                let uu____10201 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.Delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____10201  in
              mk1 uu____10200  in
            let uu____10202 = desugar_term_aq env t1  in
            (match uu____10202 with
             | (t1',aq1) ->
                 let uu____10213 = desugar_term_aq env t2  in
                 (match uu____10213 with
                  | (t2',aq2) ->
                      let uu____10224 = desugar_term_aq env t3  in
                      (match uu____10224 with
                       | (t3',aq3) ->
                           let uu____10235 =
                             let uu____10238 =
                               let uu____10239 =
                                 let uu____10262 =
                                   FStar_Syntax_Util.ascribe t1'
                                     ((FStar_Util.Inl t_bool1),
                                       FStar_Pervasives_Native.None)
                                    in
                                 let uu____10283 =
                                   let uu____10298 =
                                     let uu____10311 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t2.FStar_Parser_AST.range
                                        in
                                     (uu____10311,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____10322 =
                                     let uu____10337 =
                                       let uu____10350 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t3.FStar_Parser_AST.range
                                          in
                                       (uu____10350,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____10337]  in
                                   uu____10298 :: uu____10322  in
                                 (uu____10262, uu____10283)  in
                               FStar_Syntax_Syntax.Tm_match uu____10239  in
                             mk1 uu____10238  in
                           (uu____10235, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____10510 =
              match uu____10510 with
              | (pat,wopt,b) ->
                  let uu____10532 = desugar_match_pat env pat  in
                  (match uu____10532 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____10557 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____10557
                          in
                       let uu____10558 = desugar_term_aq env1 b  in
                       (match uu____10558 with
                        | (b1,aq) ->
                            let uu____10571 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____10571, aq)))
               in
            let uu____10576 = desugar_term_aq env e  in
            (match uu____10576 with
             | (e1,aq) ->
                 let uu____10587 =
                   let uu____10596 =
                     let uu____10607 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____10607 FStar_List.unzip  in
                   FStar_All.pipe_right uu____10596
                     (fun uu____10671  ->
                        match uu____10671 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____10587 with
                  | (brs,aqs) ->
                      let uu____10722 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____10722, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____10755 = is_comp_type env t  in
              if uu____10755
              then
                let uu____10762 = desugar_comp t.FStar_Parser_AST.range env t
                   in
                FStar_Util.Inr uu____10762
              else
                (let uu____10768 = desugar_term env t  in
                 FStar_Util.Inl uu____10768)
               in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)  in
            let uu____10774 = desugar_term_aq env e  in
            (match uu____10774 with
             | (e1,aq) ->
                 let uu____10785 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_ascribed
                        (e1, (annot, tac_opt1), FStar_Pervasives_Native.None))
                    in
                 (uu____10785, aq))
        | FStar_Parser_AST.Record (uu____10814,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____10855 = FStar_List.hd fields  in
              match uu____10855 with | (f,uu____10867) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____10911  ->
                        match uu____10911 with
                        | (g,uu____10917) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____10923,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____10937 =
                         let uu____10942 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____10942)
                          in
                       FStar_Errors.raise_error uu____10937
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
                  let uu____10950 =
                    let uu____10961 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____10992  ->
                              match uu____10992 with
                              | (f,uu____11002) ->
                                  let uu____11003 =
                                    let uu____11004 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____11004
                                     in
                                  (uu____11003, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____10961)  in
                  FStar_Parser_AST.Construct uu____10950
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____11022 =
                      let uu____11023 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____11023  in
                    FStar_Parser_AST.mk_term uu____11022
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____11025 =
                      let uu____11038 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____11068  ->
                                match uu____11068 with
                                | (f,uu____11078) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____11038)  in
                    FStar_Parser_AST.Record uu____11025  in
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
            let uu____11138 = desugar_term_aq env recterm1  in
            (match uu____11138 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____11154;
                         FStar_Syntax_Syntax.vars = uu____11155;_},args)
                      ->
                      let uu____11177 =
                        let uu____11180 =
                          let uu____11181 =
                            let uu____11196 =
                              let uu____11197 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____11198 =
                                let uu____11201 =
                                  let uu____11202 =
                                    let uu____11209 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____11209)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____11202
                                   in
                                FStar_Pervasives_Native.Some uu____11201  in
                              FStar_Syntax_Syntax.fvar uu____11197
                                FStar_Syntax_Syntax.Delta_constant
                                uu____11198
                               in
                            (uu____11196, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____11181  in
                        FStar_All.pipe_left mk1 uu____11180  in
                      (uu____11177, s)
                  | uu____11238 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            let uu____11241 =
              FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f  in
            let uu____11242 =
              FStar_Syntax_DsEnv.fail_or env
                (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
               in
            (match uu____11242 with
             | (constrname,is_rec) ->
                 let uu____11257 = desugar_term_aq env e  in
                 (match uu____11257 with
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
                      let uu____11275 =
                        let uu____11278 =
                          let uu____11279 =
                            let uu____11294 =
                              let uu____11295 =
                                let uu____11296 = FStar_Ident.range_of_lid f
                                   in
                                FStar_Ident.set_lid_range projname
                                  uu____11296
                                 in
                              FStar_Syntax_Syntax.fvar uu____11295
                                FStar_Syntax_Syntax.Delta_equational qual
                               in
                            let uu____11297 =
                              let uu____11300 = FStar_Syntax_Syntax.as_arg e1
                                 in
                              [uu____11300]  in
                            (uu____11294, uu____11297)  in
                          FStar_Syntax_Syntax.Tm_app uu____11279  in
                        FStar_All.pipe_left mk1 uu____11278  in
                      (uu____11275, s)))
        | FStar_Parser_AST.NamedTyp (uu____11307,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____11316 =
              let uu____11317 = FStar_Syntax_Subst.compress tm  in
              uu____11317.FStar_Syntax_Syntax.n  in
            (match uu____11316 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____11325 =
                   let uu___129_11328 =
                     let uu____11329 =
                       let uu____11330 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____11330  in
                     FStar_Syntax_Util.exp_string uu____11329  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___129_11328.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___129_11328.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____11325, noaqs)
             | uu____11343 ->
                 let uu____11344 =
                   let uu____11349 =
                     let uu____11350 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.strcat "VQuote, expected an fvar, got: "
                       uu____11350
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____11349)  in
                 FStar_Errors.raise_error uu____11344
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____11356 = desugar_term_aq env e  in
            (match uu____11356 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____11368 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____11368, noaqs))
        | FStar_Parser_AST.Antiquote (b,e) ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____11388 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____11389 =
              let uu____11398 =
                let uu____11405 = desugar_term env e  in (bv, b, uu____11405)
                 in
              [uu____11398]  in
            (uu____11388, uu____11389)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____11436 =
              let uu____11439 =
                let uu____11440 =
                  let uu____11447 = desugar_term env e  in (uu____11447, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____11440  in
              FStar_All.pipe_left mk1 uu____11439  in
            (uu____11436, noaqs)
        | uu____11462 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____11463 = desugar_formula env top  in
            (uu____11463, noaqs)
        | uu____11474 ->
            let uu____11475 =
              let uu____11480 =
                let uu____11481 = FStar_Parser_AST.term_to_string top  in
                Prims.strcat "Unexpected term: " uu____11481  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____11480)  in
            FStar_Errors.raise_error uu____11475 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____11487 -> false
    | uu____11496 -> true

and (is_synth_by_tactic :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (l,r,FStar_Parser_AST.Hash ) ->
          is_synth_by_tactic e l
      | FStar_Parser_AST.Var lid ->
          let uu____11502 =
            FStar_Syntax_DsEnv.resolve_to_fully_qualified_name e lid  in
          (match uu____11502 with
           | FStar_Pervasives_Native.Some lid1 ->
               FStar_Ident.lid_equals lid1 FStar_Parser_Const.synth_lid
           | FStar_Pervasives_Native.None  -> false)
      | uu____11506 -> false

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
           (fun uu____11543  ->
              match uu____11543 with
              | (a,imp) ->
                  let uu____11556 = desugar_term env a  in
                  arg_withimp_e imp uu____11556))

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
        let is_requires uu____11585 =
          match uu____11585 with
          | (t1,uu____11591) ->
              let uu____11592 =
                let uu____11593 = unparen t1  in
                uu____11593.FStar_Parser_AST.tm  in
              (match uu____11592 with
               | FStar_Parser_AST.Requires uu____11594 -> true
               | uu____11601 -> false)
           in
        let is_ensures uu____11610 =
          match uu____11610 with
          | (t1,uu____11616) ->
              let uu____11617 =
                let uu____11618 = unparen t1  in
                uu____11618.FStar_Parser_AST.tm  in
              (match uu____11617 with
               | FStar_Parser_AST.Ensures uu____11619 -> true
               | uu____11626 -> false)
           in
        let is_app head1 uu____11639 =
          match uu____11639 with
          | (t1,uu____11645) ->
              let uu____11646 =
                let uu____11647 = unparen t1  in
                uu____11647.FStar_Parser_AST.tm  in
              (match uu____11646 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____11649;
                      FStar_Parser_AST.level = uu____11650;_},uu____11651,uu____11652)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____11653 -> false)
           in
        let is_smt_pat uu____11662 =
          match uu____11662 with
          | (t1,uu____11668) ->
              let uu____11669 =
                let uu____11670 = unparen t1  in
                uu____11670.FStar_Parser_AST.tm  in
              (match uu____11669 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____11673);
                             FStar_Parser_AST.range = uu____11674;
                             FStar_Parser_AST.level = uu____11675;_},uu____11676)::uu____11677::[])
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
                             FStar_Parser_AST.range = uu____11716;
                             FStar_Parser_AST.level = uu____11717;_},uu____11718)::uu____11719::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
               | uu____11744 -> false)
           in
        let is_decreases = is_app "decreases"  in
        let pre_process_comp_typ t1 =
          let uu____11774 = head_and_args t1  in
          match uu____11774 with
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
                   let thunk_ens uu____11870 =
                     match uu____11870 with
                     | (e,i) ->
                         let uu____11881 = thunk_ens_ e  in (uu____11881, i)
                      in
                   let fail_lemma uu____11892 =
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
                         let uu____11972 =
                           let uu____11979 =
                             let uu____11986 = thunk_ens ens  in
                             [uu____11986; nil_pat]  in
                           req_true :: uu____11979  in
                         unit_tm :: uu____11972
                     | req::ens::[] when
                         (is_requires req) && (is_ensures ens) ->
                         let uu____12033 =
                           let uu____12040 =
                             let uu____12047 = thunk_ens ens  in
                             [uu____12047; nil_pat]  in
                           req :: uu____12040  in
                         unit_tm :: uu____12033
                     | ens::smtpat::[] when
                         (((let uu____12096 = is_requires ens  in
                            Prims.op_Negation uu____12096) &&
                             (let uu____12098 = is_smt_pat ens  in
                              Prims.op_Negation uu____12098))
                            &&
                            (let uu____12100 = is_decreases ens  in
                             Prims.op_Negation uu____12100))
                           && (is_smt_pat smtpat)
                         ->
                         let uu____12101 =
                           let uu____12108 =
                             let uu____12115 = thunk_ens ens  in
                             [uu____12115; smtpat]  in
                           req_true :: uu____12108  in
                         unit_tm :: uu____12101
                     | ens::dec::[] when
                         (is_ensures ens) && (is_decreases dec) ->
                         let uu____12162 =
                           let uu____12169 =
                             let uu____12176 = thunk_ens ens  in
                             [uu____12176; nil_pat; dec]  in
                           req_true :: uu____12169  in
                         unit_tm :: uu____12162
                     | ens::dec::smtpat::[] when
                         ((is_ensures ens) && (is_decreases dec)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____12236 =
                           let uu____12243 =
                             let uu____12250 = thunk_ens ens  in
                             [uu____12250; smtpat; dec]  in
                           req_true :: uu____12243  in
                         unit_tm :: uu____12236
                     | req::ens::dec::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_decreases dec)
                         ->
                         let uu____12310 =
                           let uu____12317 =
                             let uu____12324 = thunk_ens ens  in
                             [uu____12324; nil_pat; dec]  in
                           req :: uu____12317  in
                         unit_tm :: uu____12310
                     | req::ens::smtpat::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____12384 =
                           let uu____12391 =
                             let uu____12398 = thunk_ens ens  in
                             [uu____12398; smtpat]  in
                           req :: uu____12391  in
                         unit_tm :: uu____12384
                     | req::ens::dec::smtpat::[] when
                         (((is_requires req) && (is_ensures ens)) &&
                            (is_smt_pat smtpat))
                           && (is_decreases dec)
                         ->
                         let uu____12463 =
                           let uu____12470 =
                             let uu____12477 = thunk_ens ens  in
                             [uu____12477; dec; smtpat]  in
                           req :: uu____12470  in
                         unit_tm :: uu____12463
                     | _other -> fail_lemma ()  in
                   let head_and_attributes =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) lemma
                      in
                   (head_and_attributes, args1)
               | FStar_Parser_AST.Name l when
                   FStar_Syntax_DsEnv.is_effect_name env l ->
                   let uu____12539 =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) l
                      in
                   (uu____12539, args)
               | FStar_Parser_AST.Name l when
                   (let uu____12567 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____12567
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   let uu____12568 =
                     let uu____12575 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_Tot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____12575, [])  in
                   (uu____12568, args)
               | FStar_Parser_AST.Name l when
                   (let uu____12593 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____12593
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                   ->
                   let uu____12594 =
                     let uu____12601 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_GTot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____12601, [])  in
                   (uu____12594, args)
               | FStar_Parser_AST.Name l when
                   (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                      ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                     || ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                   ->
                   let uu____12617 =
                     let uu____12624 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_Tot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____12624, [])  in
                   (uu____12617, [(t1, FStar_Parser_AST.Nothing)])
               | uu____12647 ->
                   let default_effect =
                     let uu____12649 = FStar_Options.ml_ish ()  in
                     if uu____12649
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       (let uu____12651 =
                          let uu____12652 =
                            FStar_Options.warn_default_effects ()  in
                          if uu____12652
                          then
                            FStar_Errors.log_issue
                              head1.FStar_Parser_AST.range
                              (FStar_Errors.Warning_UseDefaultEffect,
                                "Using default effect Tot")
                          else ()  in
                        FStar_Parser_Const.effect_Tot_lid)
                      in
                   let uu____12654 =
                     let uu____12661 =
                       FStar_Ident.set_lid_range default_effect
                         head1.FStar_Parser_AST.range
                        in
                     (uu____12661, [])  in
                   (uu____12654, [(t1, FStar_Parser_AST.Nothing)]))
           in
        let uu____12684 = pre_process_comp_typ t  in
        match uu____12684 with
        | ((eff,cattributes),args) ->
            let uu____12728 =
              Obj.magic
                (if (FStar_List.length args) = (Prims.parse_int "0")
                 then
                   Obj.repr
                     (let uu____12733 =
                        let uu____12738 =
                          let uu____12739 =
                            FStar_Syntax_Print.lid_to_string eff  in
                          FStar_Util.format1 "Not enough args to effect %s"
                            uu____12739
                           in
                        (FStar_Errors.Fatal_NotEnoughArgsToEffect,
                          uu____12738)
                         in
                      fail1 () uu____12733)
                 else Obj.repr ())
               in
            let is_universe uu____12749 =
              match uu____12749 with
              | (uu____12754,imp) -> imp = FStar_Parser_AST.UnivApp  in
            let uu____12756 = FStar_Util.take is_universe args  in
            (match uu____12756 with
             | (universes,args1) ->
                 let universes1 =
                   FStar_List.map
                     (fun uu____12815  ->
                        match uu____12815 with
                        | (u,imp) -> desugar_universe u) universes
                    in
                 let uu____12822 =
                   let uu____12837 = FStar_List.hd args1  in
                   let uu____12846 = FStar_List.tl args1  in
                   (uu____12837, uu____12846)  in
                 (match uu____12822 with
                  | (result_arg,rest) ->
                      let result_typ =
                        desugar_typ env
                          (FStar_Pervasives_Native.fst result_arg)
                         in
                      let rest1 = desugar_args env rest  in
                      let uu____12901 =
                        let is_decrease uu____12938 =
                          match uu____12938 with
                          | (t1,uu____12948) ->
                              (match t1.FStar_Syntax_Syntax.n with
                               | FStar_Syntax_Syntax.Tm_app
                                   ({
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_fvar fv;
                                      FStar_Syntax_Syntax.pos = uu____12958;
                                      FStar_Syntax_Syntax.vars = uu____12959;_},uu____12960::[])
                                   ->
                                   FStar_Syntax_Syntax.fv_eq_lid fv
                                     FStar_Parser_Const.decreases_lid
                               | uu____12991 -> false)
                           in
                        FStar_All.pipe_right rest1
                          (FStar_List.partition is_decrease)
                         in
                      (match uu____12901 with
                       | (dec,rest2) ->
                           let decreases_clause =
                             FStar_All.pipe_right dec
                               (FStar_List.map
                                  (fun uu____13105  ->
                                     match uu____13105 with
                                     | (t1,uu____13115) ->
                                         (match t1.FStar_Syntax_Syntax.n with
                                          | FStar_Syntax_Syntax.Tm_app
                                              (uu____13124,(arg,uu____13126)::[])
                                              ->
                                              FStar_Syntax_Syntax.DECREASES
                                                arg
                                          | uu____13155 -> failwith "impos")))
                              in
                           let no_additional_args =
                             let is_empty a l =
                               match l with
                               | [] -> true
                               | uu____13170 -> false  in
                             (((is_empty () (Obj.magic decreases_clause)) &&
                                 (is_empty () (Obj.magic rest2)))
                                && (is_empty () (Obj.magic cattributes)))
                               && (is_empty () (Obj.magic universes1))
                              in
                           let uu____13173 =
                             no_additional_args &&
                               (FStar_Ident.lid_equals eff
                                  FStar_Parser_Const.effect_Tot_lid)
                              in
                           if uu____13173
                           then FStar_Syntax_Syntax.mk_Total result_typ
                           else
                             (let uu____13177 =
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_GTot_lid)
                                 in
                              if uu____13177
                              then FStar_Syntax_Syntax.mk_GTotal result_typ
                              else
                                (let flags1 =
                                   let uu____13184 =
                                     FStar_Ident.lid_equals eff
                                       FStar_Parser_Const.effect_Lemma_lid
                                      in
                                   if uu____13184
                                   then [FStar_Syntax_Syntax.LEMMA]
                                   else
                                     (let uu____13188 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Tot_lid
                                         in
                                      if uu____13188
                                      then [FStar_Syntax_Syntax.TOTAL]
                                      else
                                        (let uu____13192 =
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         if uu____13192
                                         then [FStar_Syntax_Syntax.MLEFFECT]
                                         else
                                           (let uu____13196 =
                                              FStar_Ident.lid_equals eff
                                                FStar_Parser_Const.effect_GTot_lid
                                               in
                                            if uu____13196
                                            then
                                              [FStar_Syntax_Syntax.SOMETRIVIAL]
                                            else [])))
                                    in
                                 let flags2 =
                                   FStar_List.append flags1 cattributes  in
                                 let rest3 =
                                   let uu____13214 =
                                     FStar_Ident.lid_equals eff
                                       FStar_Parser_Const.effect_Lemma_lid
                                      in
                                   if uu____13214
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
                                                 let uu____13303 =
                                                   FStar_Ident.set_lid_range
                                                     FStar_Parser_Const.pattern_lid
                                                     pat.FStar_Syntax_Syntax.pos
                                                    in
                                                 FStar_Syntax_Syntax.fvar
                                                   uu____13303
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
                                           | uu____13318 -> pat  in
                                         let uu____13319 =
                                           let uu____13330 =
                                             let uu____13341 =
                                               let uu____13350 =
                                                 FStar_Syntax_Syntax.mk
                                                   (FStar_Syntax_Syntax.Tm_meta
                                                      (pat1,
                                                        (FStar_Syntax_Syntax.Meta_desugared
                                                           FStar_Syntax_Syntax.Meta_smt_pat)))
                                                   FStar_Pervasives_Native.None
                                                   pat1.FStar_Syntax_Syntax.pos
                                                  in
                                               (uu____13350, aq)  in
                                             [uu____13341]  in
                                           ens :: uu____13330  in
                                         req :: uu____13319
                                     | uu____13391 -> rest2
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
        | uu____13414 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___130_13433 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___130_13433.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___130_13433.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___131_13471 = b  in
             {
               FStar_Parser_AST.b = (uu___131_13471.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___131_13471.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___131_13471.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____13532 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____13532)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____13545 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____13545 with
             | (env1,a1) ->
                 let a2 =
                   let uu___132_13555 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___132_13555.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___132_13555.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____13577 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____13591 =
                     let uu____13594 =
                       let uu____13595 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____13595]  in
                     no_annot_abs uu____13594 body2  in
                   FStar_All.pipe_left setpos uu____13591  in
                 let uu____13600 =
                   let uu____13601 =
                     let uu____13616 =
                       let uu____13617 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____13617
                         (FStar_Syntax_Syntax.Delta_defined_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____13618 =
                       let uu____13621 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____13621]  in
                     (uu____13616, uu____13618)  in
                   FStar_Syntax_Syntax.Tm_app uu____13601  in
                 FStar_All.pipe_left mk1 uu____13600)
        | uu____13626 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____13702 = q (rest, pats, body)  in
              let uu____13709 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____13702 uu____13709
                FStar_Parser_AST.Formula
               in
            let uu____13710 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____13710 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____13719 -> failwith "impossible"  in
      let uu____13722 =
        let uu____13723 = unparen f  in uu____13723.FStar_Parser_AST.tm  in
      match uu____13722 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____13730,uu____13731) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____13742,uu____13743) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____13774 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____13774
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____13810 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____13810
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____13853 -> desugar_term env f

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
      let uu____13858 =
        FStar_List.fold_left
          (fun uu____13894  ->
             fun b  ->
               match uu____13894 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___133_13946 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___133_13946.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___133_13946.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___133_13946.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____13963 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____13963 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___134_13983 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___134_13983.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___134_13983.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____14000 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____13858 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

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
          let uu____14087 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____14087)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____14092 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____14092)
      | FStar_Parser_AST.TVariable x ->
          let uu____14096 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____14096)
      | FStar_Parser_AST.NoName t ->
          let uu____14104 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____14104)
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
               (fun uu___96_14143  ->
                  match uu___96_14143 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____14144 -> false))
           in
        let quals2 q =
          let uu____14156 =
            (let uu____14159 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____14159) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____14156
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____14173 = FStar_Ident.range_of_lid disc_name  in
                let uu____14174 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____14173;
                  FStar_Syntax_Syntax.sigquals = uu____14174;
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
            let uu____14215 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____14245  ->
                        match uu____14245 with
                        | (x,uu____14253) ->
                            let uu____14254 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____14254 with
                             | (field_name,uu____14262) ->
                                 let only_decl =
                                   ((let uu____14266 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____14266)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____14268 =
                                        let uu____14269 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____14269.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____14268)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____14284 =
                                       FStar_List.filter
                                         (fun uu___97_14288  ->
                                            match uu___97_14288 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____14289 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____14284
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___98_14302  ->
                                             match uu___98_14302 with
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____14303 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____14305 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____14305;
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____14312 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____14312
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          FStar_Syntax_Syntax.Delta_equational
                                      else
                                        FStar_Syntax_Syntax.Delta_equational
                                       in
                                    let lb =
                                      let uu____14317 =
                                        let uu____14322 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____14322  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____14317;
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
                                      let uu____14326 =
                                        let uu____14327 =
                                          let uu____14334 =
                                            let uu____14337 =
                                              let uu____14338 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____14338
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____14337]  in
                                          ((false, [lb]), uu____14334)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____14327
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____14326;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____14215 FStar_List.flatten
  
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
            (lid,uu____14388,t,uu____14390,n1,uu____14392) when
            let uu____14397 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____14397 ->
            let uu____14398 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____14398 with
             | (formals,uu____14414) ->
                 (match formals with
                  | [] -> []
                  | uu____14437 ->
                      let filter_records uu___99_14450 =
                        match uu___99_14450 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____14453,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____14465 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____14467 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____14467 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Syntax_Syntax.Data_ctor
                        | FStar_Pervasives_Native.Some q -> q  in
                      let iquals1 =
                        if
                          FStar_List.contains FStar_Syntax_Syntax.Abstract
                            iquals
                        then FStar_Syntax_Syntax.Private :: iquals
                        else iquals  in
                      let uu____14477 = FStar_Util.first_N n1 formals  in
                      (match uu____14477 with
                       | (uu____14500,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____14526 -> []
  
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
                    let uu____14592 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____14592
                    then
                      let uu____14595 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____14595
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____14598 =
                      let uu____14603 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____14603  in
                    let uu____14604 =
                      let uu____14607 = FStar_Syntax_Syntax.mk_Total k  in
                      FStar_Syntax_Util.arrow typars uu____14607  in
                    let uu____14610 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____14598;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____14604;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____14610;
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
          let tycon_id uu___100_14666 =
            match uu___100_14666 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____14668,uu____14669) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____14679,uu____14680,uu____14681) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____14691,uu____14692,uu____14693) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____14723,uu____14724,uu____14725) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____14768) ->
                let uu____14769 =
                  let uu____14770 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____14770  in
                FStar_Parser_AST.mk_term uu____14769 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____14772 =
                  let uu____14773 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____14773  in
                FStar_Parser_AST.mk_term uu____14772 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____14775) ->
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
              | uu____14802 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____14808 =
                     let uu____14809 =
                       let uu____14816 = binder_to_term b  in
                       (out, uu____14816, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____14809  in
                   FStar_Parser_AST.mk_term uu____14808
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___101_14827 =
            match uu___101_14827 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____14883  ->
                       match uu____14883 with
                       | (x,t,uu____14894) ->
                           let uu____14899 =
                             let uu____14900 =
                               let uu____14905 =
                                 FStar_Syntax_Util.mangle_field_name x  in
                               (uu____14905, t)  in
                             FStar_Parser_AST.Annotated uu____14900  in
                           FStar_Parser_AST.mk_binder uu____14899
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____14907 =
                    let uu____14908 =
                      let uu____14909 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____14909  in
                    FStar_Parser_AST.mk_term uu____14908
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____14907 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let uu____14913 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____14940  ->
                          match uu____14940 with
                          | (x,uu____14950,uu____14951) ->
                              FStar_Syntax_Util.unmangle_field_name x))
                   in
                ((FStar_Parser_AST.TyconVariant
                    (id1, parms, kopt,
                      [(constrName, (FStar_Pervasives_Native.Some constrTyp),
                         FStar_Pervasives_Native.None, false)])),
                  uu____14913)
            | uu____15004 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___102_15039 =
            match uu___102_15039 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____15063 = typars_of_binders _env binders  in
                (match uu____15063 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____15109 =
                         let uu____15110 =
                           let uu____15111 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____15111  in
                         FStar_Parser_AST.mk_term uu____15110
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____15109 binders  in
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
            | uu____15124 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____15170 =
              FStar_List.fold_left
                (fun uu____15210  ->
                   fun uu____15211  ->
                     match (uu____15210, uu____15211) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____15302 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____15302 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____15170 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____15415 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____15415
                | uu____15416 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____15424 = desugar_abstract_tc quals env [] tc  in
              (match uu____15424 with
               | (uu____15437,uu____15438,se,uu____15440) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____15443,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             (let uu____15459 =
                                let uu____15460 =
                                  let uu____15461 = FStar_Options.ml_ish ()
                                     in
                                  Prims.op_Negation uu____15461  in
                                if uu____15460
                                then
                                  let uu____15462 =
                                    let uu____15467 =
                                      let uu____15468 =
                                        FStar_Syntax_Print.lid_to_string l
                                         in
                                      FStar_Util.format1
                                        "Adding an implicit 'assume new' qualifier on %s"
                                        uu____15468
                                       in
                                    (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                      uu____15467)
                                     in
                                  FStar_Errors.log_issue
                                    se.FStar_Syntax_Syntax.sigrng uu____15462
                                else ()  in
                              FStar_Syntax_Syntax.Assumption ::
                                FStar_Syntax_Syntax.New :: quals1)
                            in
                         let t =
                           match typars with
                           | [] -> k
                           | uu____15475 ->
                               let uu____15476 =
                                 let uu____15481 =
                                   let uu____15482 =
                                     let uu____15495 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____15495)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____15482
                                    in
                                 FStar_Syntax_Syntax.mk uu____15481  in
                               uu____15476 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___135_15499 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___135_15499.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___135_15499.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___135_15499.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____15502 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____15505 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____15505
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____15520 = typars_of_binders env binders  in
              (match uu____15520 with
               | (env',typars) ->
                   let k =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____15556 =
                           FStar_Util.for_some
                             (fun uu___103_15558  ->
                                match uu___103_15558 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____15559 -> false) quals
                            in
                         if uu____15556
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Util.ktype
                     | FStar_Pervasives_Native.Some k -> desugar_term env' k
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____15566 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___104_15570  ->
                               match uu___104_15570 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____15571 -> false))
                        in
                     if uu____15566
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____15580 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____15580
                     then
                       let uu____15583 =
                         let uu____15590 =
                           let uu____15591 = unparen t  in
                           uu____15591.FStar_Parser_AST.tm  in
                         match uu____15590 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____15612 =
                               match FStar_List.rev args with
                               | (last_arg,uu____15642)::args_rev ->
                                   let uu____15654 =
                                     let uu____15655 = unparen last_arg  in
                                     uu____15655.FStar_Parser_AST.tm  in
                                   (match uu____15654 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____15683 -> ([], args))
                               | uu____15692 -> ([], args)  in
                             (match uu____15612 with
                              | (cattributes,args1) ->
                                  let uu____15731 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____15731))
                         | uu____15742 -> (t, [])  in
                       match uu____15583 with
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
                                  (fun uu___105_15764  ->
                                     match uu___105_15764 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____15765 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____15776)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____15800 = tycon_record_as_variant trec  in
              (match uu____15800 with
               | (t,fs) ->
                   let uu____15817 =
                     let uu____15820 =
                       let uu____15821 =
                         let uu____15830 =
                           let uu____15833 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____15833  in
                         (uu____15830, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____15821  in
                     uu____15820 :: quals  in
                   desugar_tycon env d uu____15817 [t])
          | uu____15838::uu____15839 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____16003 = et  in
                match uu____16003 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____16228 ->
                         let trec = tc  in
                         let uu____16252 = tycon_record_as_variant trec  in
                         (match uu____16252 with
                          | (t,fs) ->
                              let uu____16311 =
                                let uu____16314 =
                                  let uu____16315 =
                                    let uu____16324 =
                                      let uu____16327 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____16327  in
                                    (uu____16324, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____16315
                                   in
                                uu____16314 :: quals1  in
                              collect_tcs uu____16311 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____16414 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____16414 with
                          | (env2,uu____16474,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____16623 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____16623 with
                          | (env2,uu____16683,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____16808 ->
                         failwith "Unrecognized mutual type definition")
                 in
              let uu____16855 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____16855 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___107_17366  ->
                             match uu___107_17366 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____17433,uu____17434);
                                    FStar_Syntax_Syntax.sigrng = uu____17435;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____17436;
                                    FStar_Syntax_Syntax.sigmeta = uu____17437;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____17438;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____17499 =
                                     typars_of_binders env1 binders  in
                                   match uu____17499 with
                                   | (env2,tpars1) ->
                                       let uu____17530 =
                                         push_tparams env2 tpars1  in
                                       (match uu____17530 with
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
                                 let uu____17563 =
                                   let uu____17584 =
                                     mk_typ_abbrev id1 uvs tpars k t1 
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____17584)
                                    in
                                 [uu____17563]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____17652);
                                    FStar_Syntax_Syntax.sigrng = uu____17653;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____17655;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____17656;_},constrs,tconstr,quals1)
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
                                 let uu____17753 = push_tparams env1 tpars
                                    in
                                 (match uu____17753 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____17830  ->
                                             match uu____17830 with
                                             | (x,uu____17844) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____17852 =
                                        let uu____17881 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____17995  ->
                                                  match uu____17995 with
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
                                                        let uu____18051 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____18051
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
                                                                uu___106_18062
                                                                 ->
                                                                match uu___106_18062
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____18074
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____18082 =
                                                        let uu____18103 =
                                                          let uu____18104 =
                                                            let uu____18105 =
                                                              let uu____18120
                                                                =
                                                                let uu____18123
                                                                  =
                                                                  let uu____18126
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____18126
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____18123
                                                                 in
                                                              (name, univs1,
                                                                uu____18120,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____18105
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____18104;
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
                                                          uu____18103)
                                                         in
                                                      (name, uu____18082)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____17881
                                         in
                                      (match uu____17852 with
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
                             | uu____18365 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____18497  ->
                             match uu____18497 with
                             | (name_doc,uu____18525,uu____18526) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____18606  ->
                             match uu____18606 with
                             | (uu____18627,uu____18628,se) -> se))
                      in
                   let uu____18658 =
                     let uu____18665 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____18665 rng
                      in
                   (match uu____18658 with
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
                               (fun uu____18731  ->
                                  match uu____18731 with
                                  | (uu____18754,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____18805,tps,k,uu____18808,constrs)
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
                                  | uu____18827 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____18844  ->
                                 match uu____18844 with
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
      let uu____18883 =
        FStar_List.fold_left
          (fun uu____18906  ->
             fun b  ->
               match uu____18906 with
               | (env1,binders1) ->
                   let uu____18926 = desugar_binder env1 b  in
                   (match uu____18926 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____18943 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____18943 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____18960 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____18883 with
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
          let uu____19013 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___108_19018  ->
                    match uu___108_19018 with
                    | FStar_Syntax_Syntax.Reflectable uu____19019 -> true
                    | uu____19020 -> false))
             in
          if uu____19013
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____19023 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____19023
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
                  let uu____19167 = desugar_binders monad_env eff_binders  in
                  match uu____19167 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let for_free =
                        let uu____19188 =
                          let uu____19189 =
                            let uu____19196 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____19196  in
                          FStar_List.length uu____19189  in
                        uu____19188 = (Prims.parse_int "1")  in
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
                            (uu____19239,(FStar_Parser_AST.TyconAbbrev
                                          (name,uu____19241,uu____19242,uu____19243),uu____19244)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____19277 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____19278 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____19290 = name_of_eff_decl decl  in
                             FStar_List.mem uu____19290 mandatory_members)
                          eff_decls
                         in
                      (match uu____19278 with
                       | (mandatory_members_decls,actions) ->
                           let uu____19307 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____19336  ->
                                     fun decl  ->
                                       match uu____19336 with
                                       | (env2,out) ->
                                           let uu____19356 =
                                             desugar_decl env2 decl  in
                                           (match uu____19356 with
                                            | (env3,ses) ->
                                                let uu____19369 =
                                                  let uu____19372 =
                                                    FStar_List.hd ses  in
                                                  uu____19372 :: out  in
                                                (env3, uu____19369)))
                                  (env1, []))
                              in
                           (match uu____19307 with
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
                                              (uu____19440,(FStar_Parser_AST.TyconAbbrev
                                                            (name,action_params,uu____19443,
                                                             {
                                                               FStar_Parser_AST.tm
                                                                 =
                                                                 FStar_Parser_AST.Construct
                                                                 (uu____19444,
                                                                  (def,uu____19446)::
                                                                  (cps_type,uu____19448)::[]);
                                                               FStar_Parser_AST.range
                                                                 =
                                                                 uu____19449;
                                                               FStar_Parser_AST.level
                                                                 =
                                                                 uu____19450;_}),doc1)::[])
                                              when Prims.op_Negation for_free
                                              ->
                                              let uu____19502 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____19502 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____19522 =
                                                     let uu____19523 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____19524 =
                                                       let uu____19525 =
                                                         desugar_term env3
                                                           def
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____19525
                                                        in
                                                     let uu____19530 =
                                                       let uu____19531 =
                                                         desugar_typ env3
                                                           cps_type
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____19531
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____19523;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____19524;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____19530
                                                     }  in
                                                   (uu____19522, doc1))
                                          | FStar_Parser_AST.Tycon
                                              (uu____19538,(FStar_Parser_AST.TyconAbbrev
                                                            (name,action_params,uu____19541,defn),doc1)::[])
                                              when for_free ->
                                              let uu____19576 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____19576 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____19596 =
                                                     let uu____19597 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____19598 =
                                                       let uu____19599 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____19599
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____19597;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____19598;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____19596, doc1))
                                          | uu____19606 ->
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
                                    let uu____19637 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____19637
                                     in
                                  let uu____19638 =
                                    let uu____19639 =
                                      FStar_Syntax_DsEnv.fail_or env2
                                        (FStar_Syntax_DsEnv.try_lookup_definition
                                           env2) l
                                       in
                                    FStar_All.pipe_left
                                      (FStar_Syntax_Subst.close binders1)
                                      uu____19639
                                     in
                                  ([], uu____19638)  in
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
                                      let uu____19656 =
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      ([], uu____19656)  in
                                    let uu____19663 =
                                      let uu____19664 =
                                        let uu____19665 =
                                          let uu____19666 = lookup1 "repr"
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____19666
                                           in
                                        let uu____19675 = lookup1 "return"
                                           in
                                        let uu____19676 = lookup1 "bind"  in
                                        let uu____19677 =
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
                                            uu____19665;
                                          FStar_Syntax_Syntax.return_repr =
                                            uu____19675;
                                          FStar_Syntax_Syntax.bind_repr =
                                            uu____19676;
                                          FStar_Syntax_Syntax.actions =
                                            actions1;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            uu____19677
                                        }  in
                                      FStar_Syntax_Syntax.Sig_new_effect_for_free
                                        uu____19664
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____19663;
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
                                         (fun uu___109_19683  ->
                                            match uu___109_19683 with
                                            | FStar_Syntax_Syntax.Reifiable 
                                                -> true
                                            | FStar_Syntax_Syntax.Reflectable
                                                uu____19684 -> true
                                            | uu____19685 -> false)
                                         qualifiers
                                        in
                                     let un_ts =
                                       ([], FStar_Syntax_Syntax.tun)  in
                                     let uu____19695 =
                                       let uu____19696 =
                                         let uu____19697 =
                                           lookup1 "return_wp"  in
                                         let uu____19698 = lookup1 "bind_wp"
                                            in
                                         let uu____19699 =
                                           lookup1 "if_then_else"  in
                                         let uu____19700 = lookup1 "ite_wp"
                                            in
                                         let uu____19701 = lookup1 "stronger"
                                            in
                                         let uu____19702 = lookup1 "close_wp"
                                            in
                                         let uu____19703 = lookup1 "assert_p"
                                            in
                                         let uu____19704 = lookup1 "assume_p"
                                            in
                                         let uu____19705 = lookup1 "null_wp"
                                            in
                                         let uu____19706 = lookup1 "trivial"
                                            in
                                         let uu____19707 =
                                           if rr
                                           then
                                             let uu____19708 = lookup1 "repr"
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.snd
                                               uu____19708
                                           else FStar_Syntax_Syntax.tun  in
                                         let uu____19724 =
                                           if rr
                                           then lookup1 "return"
                                           else un_ts  in
                                         let uu____19726 =
                                           if rr
                                           then lookup1 "bind"
                                           else un_ts  in
                                         let uu____19728 =
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
                                             uu____19697;
                                           FStar_Syntax_Syntax.bind_wp =
                                             uu____19698;
                                           FStar_Syntax_Syntax.if_then_else =
                                             uu____19699;
                                           FStar_Syntax_Syntax.ite_wp =
                                             uu____19700;
                                           FStar_Syntax_Syntax.stronger =
                                             uu____19701;
                                           FStar_Syntax_Syntax.close_wp =
                                             uu____19702;
                                           FStar_Syntax_Syntax.assert_p =
                                             uu____19703;
                                           FStar_Syntax_Syntax.assume_p =
                                             uu____19704;
                                           FStar_Syntax_Syntax.null_wp =
                                             uu____19705;
                                           FStar_Syntax_Syntax.trivial =
                                             uu____19706;
                                           FStar_Syntax_Syntax.repr =
                                             uu____19707;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____19724;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____19726;
                                           FStar_Syntax_Syntax.actions =
                                             actions1;
                                           FStar_Syntax_Syntax.eff_attrs =
                                             uu____19728
                                         }  in
                                       FStar_Syntax_Syntax.Sig_new_effect
                                         uu____19696
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         uu____19695;
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
                                          fun uu____19754  ->
                                            match uu____19754 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____19768 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____19768
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
                let uu____19792 = desugar_binders env1 eff_binders  in
                match uu____19792 with
                | (env2,binders) ->
                    let uu____19811 =
                      let uu____19830 = head_and_args defn  in
                      match uu____19830 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____19875 ->
                                let uu____19876 =
                                  let uu____19881 =
                                    let uu____19882 =
                                      let uu____19883 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.strcat uu____19883 " not found"
                                       in
                                    Prims.strcat "Effect " uu____19882  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____19881)
                                   in
                                FStar_Errors.raise_error uu____19876
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____19885 =
                            match FStar_List.rev args with
                            | (last_arg,uu____19915)::args_rev ->
                                let uu____19927 =
                                  let uu____19928 = unparen last_arg  in
                                  uu____19928.FStar_Parser_AST.tm  in
                                (match uu____19927 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____19956 -> ([], args))
                            | uu____19965 -> ([], args)  in
                          (match uu____19885 with
                           | (cattributes,args1) ->
                               let uu____20016 = desugar_args env2 args1  in
                               let uu____20025 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____20016, uu____20025))
                       in
                    (match uu____19811 with
                     | (ed_lid,ed,args,cattributes) ->
                         let binders1 =
                           FStar_Syntax_Subst.close_binders binders  in
                         let uu____20069 =
                           if
                             (FStar_List.length args) <>
                               (FStar_List.length
                                  ed.FStar_Syntax_Syntax.binders)
                           then
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_ArgumentLengthMismatch,
                                 "Unexpected number of arguments to effect constructor")
                               defn.FStar_Parser_AST.range
                           else ()  in
                         let uu____20081 =
                           FStar_Syntax_Subst.open_term'
                             ed.FStar_Syntax_Syntax.binders
                             FStar_Syntax_Syntax.t_unit
                            in
                         (match uu____20081 with
                          | (ed_binders,uu____20095,ed_binders_opening) ->
                              let sub1 uu____20107 =
                                match uu____20107 with
                                | (us,x) ->
                                    let x1 =
                                      let uu____20121 =
                                        FStar_Syntax_Subst.shift_subst
                                          (FStar_List.length us)
                                          ed_binders_opening
                                         in
                                      FStar_Syntax_Subst.subst uu____20121 x
                                       in
                                    let s =
                                      FStar_Syntax_Util.subst_of_list
                                        ed_binders args
                                       in
                                    let uu____20125 =
                                      let uu____20126 =
                                        FStar_Syntax_Subst.subst s x1  in
                                      (us, uu____20126)  in
                                    FStar_Syntax_Subst.close_tscheme binders1
                                      uu____20125
                                 in
                              let mname =
                                FStar_Syntax_DsEnv.qualify env0 eff_name  in
                              let ed1 =
                                let uu____20131 =
                                  let uu____20132 =
                                    sub1
                                      ([],
                                        (ed.FStar_Syntax_Syntax.signature))
                                     in
                                  FStar_Pervasives_Native.snd uu____20132  in
                                let uu____20143 =
                                  sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                let uu____20144 =
                                  sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                let uu____20145 =
                                  sub1 ed.FStar_Syntax_Syntax.if_then_else
                                   in
                                let uu____20146 =
                                  sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                let uu____20147 =
                                  sub1 ed.FStar_Syntax_Syntax.stronger  in
                                let uu____20148 =
                                  sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                let uu____20149 =
                                  sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                let uu____20150 =
                                  sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                let uu____20151 =
                                  sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                let uu____20152 =
                                  sub1 ed.FStar_Syntax_Syntax.trivial  in
                                let uu____20153 =
                                  let uu____20154 =
                                    sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                     in
                                  FStar_Pervasives_Native.snd uu____20154  in
                                let uu____20165 =
                                  sub1 ed.FStar_Syntax_Syntax.return_repr  in
                                let uu____20166 =
                                  sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                let uu____20167 =
                                  FStar_List.map
                                    (fun action  ->
                                       let uu____20175 =
                                         FStar_Syntax_DsEnv.qualify env2
                                           action.FStar_Syntax_Syntax.action_unqualified_name
                                          in
                                       let uu____20176 =
                                         let uu____20177 =
                                           sub1
                                             ([],
                                               (action.FStar_Syntax_Syntax.action_defn))
                                            in
                                         FStar_Pervasives_Native.snd
                                           uu____20177
                                          in
                                       let uu____20188 =
                                         let uu____20189 =
                                           sub1
                                             ([],
                                               (action.FStar_Syntax_Syntax.action_typ))
                                            in
                                         FStar_Pervasives_Native.snd
                                           uu____20189
                                          in
                                       {
                                         FStar_Syntax_Syntax.action_name =
                                           uu____20175;
                                         FStar_Syntax_Syntax.action_unqualified_name
                                           =
                                           (action.FStar_Syntax_Syntax.action_unqualified_name);
                                         FStar_Syntax_Syntax.action_univs =
                                           (action.FStar_Syntax_Syntax.action_univs);
                                         FStar_Syntax_Syntax.action_params =
                                           (action.FStar_Syntax_Syntax.action_params);
                                         FStar_Syntax_Syntax.action_defn =
                                           uu____20176;
                                         FStar_Syntax_Syntax.action_typ =
                                           uu____20188
                                       }) ed.FStar_Syntax_Syntax.actions
                                   in
                                {
                                  FStar_Syntax_Syntax.cattributes =
                                    cattributes;
                                  FStar_Syntax_Syntax.mname = mname;
                                  FStar_Syntax_Syntax.univs =
                                    (ed.FStar_Syntax_Syntax.univs);
                                  FStar_Syntax_Syntax.binders = binders1;
                                  FStar_Syntax_Syntax.signature = uu____20131;
                                  FStar_Syntax_Syntax.ret_wp = uu____20143;
                                  FStar_Syntax_Syntax.bind_wp = uu____20144;
                                  FStar_Syntax_Syntax.if_then_else =
                                    uu____20145;
                                  FStar_Syntax_Syntax.ite_wp = uu____20146;
                                  FStar_Syntax_Syntax.stronger = uu____20147;
                                  FStar_Syntax_Syntax.close_wp = uu____20148;
                                  FStar_Syntax_Syntax.assert_p = uu____20149;
                                  FStar_Syntax_Syntax.assume_p = uu____20150;
                                  FStar_Syntax_Syntax.null_wp = uu____20151;
                                  FStar_Syntax_Syntax.trivial = uu____20152;
                                  FStar_Syntax_Syntax.repr = uu____20153;
                                  FStar_Syntax_Syntax.return_repr =
                                    uu____20165;
                                  FStar_Syntax_Syntax.bind_repr = uu____20166;
                                  FStar_Syntax_Syntax.actions = uu____20167;
                                  FStar_Syntax_Syntax.eff_attrs =
                                    (ed.FStar_Syntax_Syntax.eff_attrs)
                                }  in
                              let se =
                                let for_free =
                                  let uu____20202 =
                                    let uu____20203 =
                                      let uu____20210 =
                                        FStar_Syntax_Util.arrow_formals
                                          ed1.FStar_Syntax_Syntax.signature
                                         in
                                      FStar_Pervasives_Native.fst uu____20210
                                       in
                                    FStar_List.length uu____20203  in
                                  uu____20202 = (Prims.parse_int "1")  in
                                let uu____20239 =
                                  let uu____20242 =
                                    trans_qual1
                                      (FStar_Pervasives_Native.Some mname)
                                     in
                                  FStar_List.map uu____20242 quals  in
                                {
                                  FStar_Syntax_Syntax.sigel =
                                    (if for_free
                                     then
                                       FStar_Syntax_Syntax.Sig_new_effect_for_free
                                         ed1
                                     else
                                       FStar_Syntax_Syntax.Sig_new_effect ed1);
                                  FStar_Syntax_Syntax.sigrng =
                                    (d.FStar_Parser_AST.drange);
                                  FStar_Syntax_Syntax.sigquals = uu____20239;
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
                                            let uu____20263 =
                                              FStar_Syntax_Util.action_as_lb
                                                mname a
                                                (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                               in
                                            FStar_Syntax_DsEnv.push_sigelt
                                              env5 uu____20263
                                             in
                                          FStar_Syntax_DsEnv.push_doc env6
                                            a.FStar_Syntax_Syntax.action_name
                                            doc1) env4)
                                 in
                              let env6 =
                                let uu____20265 =
                                  FStar_All.pipe_right quals
                                    (FStar_List.contains
                                       FStar_Parser_AST.Reflectable)
                                   in
                                if uu____20265
                                then
                                  let reflect_lid =
                                    let uu____20269 =
                                      FStar_Ident.id_of_text "reflect"  in
                                    FStar_All.pipe_right uu____20269
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
                              (env7, [se])))

and (mk_comment_attr :
  FStar_Parser_AST.decl ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun d  ->
    let uu____20281 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____20281 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.strcat "  " (Prims.strcat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____20332 ->
              let uu____20333 =
                let uu____20334 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____20334
                 in
              Prims.strcat "\n  " uu____20333
          | uu____20335 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____20348  ->
               match uu____20348 with
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
          let uu____20366 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____20366
            FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____20368 =
          let uu____20377 = FStar_Syntax_Syntax.as_arg arg  in [uu____20377]
           in
        FStar_Syntax_Util.mk_app fv uu____20368

and (desugar_decl :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      let uu____20384 = desugar_decl_noattrs env d  in
      match uu____20384 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____20404 = mk_comment_attr d  in uu____20404 :: attrs1  in
          let uu____20409 =
            FStar_List.map
              (fun sigelt  ->
                 let uu___136_20415 = sigelt  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___136_20415.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___136_20415.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___136_20415.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___136_20415.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs = attrs2
                 }) sigelts
             in
          (env1, uu____20409)

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
          let uu____20439 =
            if p = FStar_Parser_AST.LightOff
            then FStar_Options.set_ml_ish ()
            else ()  in
          (env, [se])
      | FStar_Parser_AST.Fsdoc uu____20443 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____20459 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____20459, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals  in
          let tcs1 =
            FStar_List.map
              (fun uu____20498  ->
                 match uu____20498 with | (x,uu____20506) -> x) tcs
             in
          let uu____20511 =
            FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals
             in
          desugar_tycon env d uu____20511 tcs1
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals  in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____20533;
                    FStar_Parser_AST.prange = uu____20534;_},uu____20535)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____20544;
                    FStar_Parser_AST.prange = uu____20545;_},uu____20546)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____20561;
                         FStar_Parser_AST.prange = uu____20562;_},uu____20563);
                    FStar_Parser_AST.prange = uu____20564;_},uu____20565)::[]
                   -> false
               | (p,uu____20593)::[] ->
                   let uu____20602 = is_app_pattern p  in
                   Prims.op_Negation uu____20602
               | uu____20603 -> false)
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
            let uu____20676 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____20676 with
             | (ds_lets,aq) ->
                 let uu____20687 = check_no_aq aq  in
                 let uu____20688 =
                   let uu____20689 =
                     FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets
                      in
                   uu____20689.FStar_Syntax_Syntax.n  in
                 (match uu____20688 with
                  | FStar_Syntax_Syntax.Tm_let (lbs,uu____20697) ->
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
                        | uu____20730::uu____20731 ->
                            FStar_List.map
                              (trans_qual1 FStar_Pervasives_Native.None)
                              quals
                        | uu____20734 ->
                            FStar_All.pipe_right
                              (FStar_Pervasives_Native.snd lbs)
                              (FStar_List.collect
                                 (fun uu___110_20749  ->
                                    match uu___110_20749 with
                                    | {
                                        FStar_Syntax_Syntax.lbname =
                                          FStar_Util.Inl uu____20752;
                                        FStar_Syntax_Syntax.lbunivs =
                                          uu____20753;
                                        FStar_Syntax_Syntax.lbtyp =
                                          uu____20754;
                                        FStar_Syntax_Syntax.lbeff =
                                          uu____20755;
                                        FStar_Syntax_Syntax.lbdef =
                                          uu____20756;
                                        FStar_Syntax_Syntax.lbattrs =
                                          uu____20757;
                                        FStar_Syntax_Syntax.lbpos =
                                          uu____20758;_}
                                        -> []
                                    | {
                                        FStar_Syntax_Syntax.lbname =
                                          FStar_Util.Inr fv;
                                        FStar_Syntax_Syntax.lbunivs =
                                          uu____20770;
                                        FStar_Syntax_Syntax.lbtyp =
                                          uu____20771;
                                        FStar_Syntax_Syntax.lbeff =
                                          uu____20772;
                                        FStar_Syntax_Syntax.lbdef =
                                          uu____20773;
                                        FStar_Syntax_Syntax.lbattrs =
                                          uu____20774;
                                        FStar_Syntax_Syntax.lbpos =
                                          uu____20775;_}
                                        ->
                                        FStar_Syntax_DsEnv.lookup_letbinding_quals
                                          env
                                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                         in
                      let quals2 =
                        let uu____20789 =
                          FStar_All.pipe_right lets1
                            (FStar_Util.for_some
                               (fun uu____20820  ->
                                  match uu____20820 with
                                  | (uu____20833,(uu____20834,t)) ->
                                      t.FStar_Parser_AST.level =
                                        FStar_Parser_AST.Formula))
                           in
                        if uu____20789
                        then FStar_Syntax_Syntax.Logic :: quals1
                        else quals1  in
                      let lbs1 =
                        let uu____20858 =
                          FStar_All.pipe_right quals2
                            (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                           in
                        if uu____20858
                        then
                          let uu____20867 =
                            FStar_All.pipe_right
                              (FStar_Pervasives_Native.snd lbs)
                              (FStar_List.map
                                 (fun lb  ->
                                    let fv =
                                      FStar_Util.right
                                        lb.FStar_Syntax_Syntax.lbname
                                       in
                                    let uu___137_20881 = lb  in
                                    {
                                      FStar_Syntax_Syntax.lbname =
                                        (FStar_Util.Inr
                                           (let uu___138_20883 = fv  in
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                (uu___138_20883.FStar_Syntax_Syntax.fv_name);
                                              FStar_Syntax_Syntax.fv_delta =
                                                (FStar_Syntax_Syntax.Delta_abstract
                                                   (fv.FStar_Syntax_Syntax.fv_delta));
                                              FStar_Syntax_Syntax.fv_qual =
                                                (uu___138_20883.FStar_Syntax_Syntax.fv_qual)
                                            }));
                                      FStar_Syntax_Syntax.lbunivs =
                                        (uu___137_20881.FStar_Syntax_Syntax.lbunivs);
                                      FStar_Syntax_Syntax.lbtyp =
                                        (uu___137_20881.FStar_Syntax_Syntax.lbtyp);
                                      FStar_Syntax_Syntax.lbeff =
                                        (uu___137_20881.FStar_Syntax_Syntax.lbeff);
                                      FStar_Syntax_Syntax.lbdef =
                                        (uu___137_20881.FStar_Syntax_Syntax.lbdef);
                                      FStar_Syntax_Syntax.lbattrs =
                                        (uu___137_20881.FStar_Syntax_Syntax.lbattrs);
                                      FStar_Syntax_Syntax.lbpos =
                                        (uu___137_20881.FStar_Syntax_Syntax.lbpos)
                                    }))
                             in
                          ((FStar_Pervasives_Native.fst lbs), uu____20867)
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
                  | uu____20918 ->
                      failwith "Desugaring a let did not produce a let"))
          else
            (let uu____20924 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____20943 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____20924 with
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
                       let uu___139_20979 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___139_20979.FStar_Parser_AST.prange)
                       }
                   | uu____20986 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___140_20993 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___140_20993.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___140_20993.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___140_20993.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____21027 id1 =
                   match uu____21027 with
                   | (env1,ses) ->
                       let main =
                         let uu____21048 =
                           let uu____21049 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____21049  in
                         FStar_Parser_AST.mk_term uu____21048
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
                       let uu____21099 = desugar_decl env1 id_decl  in
                       (match uu____21099 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____21117 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____21117 FStar_Util.set_elements
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
            let uu____21148 = close_fun env t  in
            desugar_term env uu____21148  in
          let quals1 =
            let uu____21152 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____21152
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let se =
            let uu____21158 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____21158;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in
          let env2 =
            FStar_Syntax_DsEnv.push_doc env1 lid d.FStar_Parser_AST.doc  in
          (env2, [se])
      | FStar_Parser_AST.Exception (id1,FStar_Pervasives_Native.None ) ->
          let uu____21170 =
            FStar_Syntax_DsEnv.fail_or env
              (FStar_Syntax_DsEnv.try_lookup_lid env)
              FStar_Parser_Const.exn_lid
             in
          (match uu____21170 with
           | (t,uu____21184) ->
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
            let uu____21218 =
              let uu____21225 = FStar_Syntax_Syntax.null_binder t  in
              [uu____21225]  in
            let uu____21226 =
              let uu____21229 =
                let uu____21230 =
                  FStar_Syntax_DsEnv.fail_or env
                    (FStar_Syntax_DsEnv.try_lookup_lid env)
                    FStar_Parser_Const.exn_lid
                   in
                FStar_Pervasives_Native.fst uu____21230  in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____21229
               in
            FStar_Syntax_Util.arrow uu____21218 uu____21226  in
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
            let uu____21294 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____21294 with
            | FStar_Pervasives_Native.None  ->
                let uu____21297 =
                  let uu____21302 =
                    let uu____21303 =
                      let uu____21304 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.strcat uu____21304 " not found"  in
                    Prims.strcat "Effect name " uu____21303  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____21302)  in
                FStar_Errors.raise_error uu____21297
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____21308 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____21350 =
                  let uu____21359 =
                    let uu____21366 = desugar_term env t  in
                    ([], uu____21366)  in
                  FStar_Pervasives_Native.Some uu____21359  in
                (uu____21350, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____21399 =
                  let uu____21408 =
                    let uu____21415 = desugar_term env wp  in
                    ([], uu____21415)  in
                  FStar_Pervasives_Native.Some uu____21408  in
                let uu____21424 =
                  let uu____21433 =
                    let uu____21440 = desugar_term env t  in
                    ([], uu____21440)  in
                  FStar_Pervasives_Native.Some uu____21433  in
                (uu____21399, uu____21424)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____21466 =
                  let uu____21475 =
                    let uu____21482 = desugar_term env t  in
                    ([], uu____21482)  in
                  FStar_Pervasives_Native.Some uu____21475  in
                (FStar_Pervasives_Native.None, uu____21466)
             in
          (match uu____21308 with
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
            let uu____21562 =
              let uu____21563 =
                let uu____21570 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____21570, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____21563  in
            {
              FStar_Syntax_Syntax.sigel = uu____21562;
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
      let uu____21598 =
        FStar_List.fold_left
          (fun uu____21618  ->
             fun d  ->
               match uu____21618 with
               | (env1,sigelts) ->
                   let uu____21638 = desugar_decl env1 d  in
                   (match uu____21638 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____21598 with
      | (env1,sigelts) ->
          let rec forward acc uu___112_21681 =
            match uu___112_21681 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____21695,FStar_Syntax_Syntax.Sig_let uu____21696) ->
                     let uu____21709 =
                       let uu____21712 =
                         let uu___141_21713 = se2  in
                         let uu____21714 =
                           let uu____21717 =
                             FStar_List.filter
                               (fun uu___111_21731  ->
                                  match uu___111_21731 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____21735;
                                           FStar_Syntax_Syntax.vars =
                                             uu____21736;_},uu____21737);
                                      FStar_Syntax_Syntax.pos = uu____21738;
                                      FStar_Syntax_Syntax.vars = uu____21739;_}
                                      when
                                      let uu____21762 =
                                        let uu____21763 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____21763
                                         in
                                      uu____21762 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____21764 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____21717
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___141_21713.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___141_21713.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___141_21713.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___141_21713.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____21714
                         }  in
                       uu____21712 :: se1 :: acc  in
                     forward uu____21709 sigelts1
                 | uu____21769 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____21777 = forward [] sigelts  in (env1, uu____21777)
  
let (open_prims_all :
  (FStar_Parser_AST.decoration Prims.list -> FStar_Parser_AST.decl)
    Prims.list)
  =
  [FStar_Parser_AST.mk_decl
     (FStar_Parser_AST.Open FStar_Parser_Const.prims_lid)
     FStar_Range.dummyRange;
  FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open FStar_Parser_Const.all_lid)
    FStar_Range.dummyRange]
  
let (generalize_annotated_univs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun s  ->
    let bs_univnames bs =
      let uu____21818 =
        let uu____21824 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____21841  ->
               match uu____21841 with
               | ({ FStar_Syntax_Syntax.ppname = uu____21850;
                    FStar_Syntax_Syntax.index = uu____21851;
                    FStar_Syntax_Syntax.sort = t;_},uu____21853)
                   ->
                   let uu____21856 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____21856) uu____21824
         in
      FStar_All.pipe_right bs uu____21818  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____21864 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____21881 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____21909 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____21930,uu____21931,bs,t,uu____21934,uu____21935)
                            ->
                            let uu____21944 = bs_univnames bs  in
                            let uu____21947 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____21944 uu____21947
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____21950,uu____21951,t,uu____21953,uu____21954,uu____21955)
                            -> FStar_Syntax_Free.univnames t
                        | uu____21960 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____21909 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___142_21970 = s  in
        let uu____21971 =
          let uu____21972 =
            let uu____21981 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____21999,bs,t,lids1,lids2) ->
                          let uu___143_22012 = se  in
                          let uu____22013 =
                            let uu____22014 =
                              let uu____22031 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____22032 =
                                let uu____22033 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____22033 t  in
                              (lid, uvs, uu____22031, uu____22032, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____22014
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____22013;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___143_22012.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___143_22012.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___143_22012.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___143_22012.FStar_Syntax_Syntax.sigattrs)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____22047,t,tlid,n1,lids1) ->
                          let uu___144_22056 = se  in
                          let uu____22057 =
                            let uu____22058 =
                              let uu____22073 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____22073, tlid, n1, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____22058  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____22057;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___144_22056.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___144_22056.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___144_22056.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___144_22056.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____22078 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____21981, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____21972  in
        {
          FStar_Syntax_Syntax.sigel = uu____21971;
          FStar_Syntax_Syntax.sigrng =
            (uu___142_21970.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___142_21970.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___142_21970.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___142_21970.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22084,t) ->
        let uvs =
          let uu____22089 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____22089 FStar_Util.set_elements  in
        let uu___145_22096 = s  in
        let uu____22097 =
          let uu____22098 =
            let uu____22105 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____22105)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____22098  in
        {
          FStar_Syntax_Syntax.sigel = uu____22097;
          FStar_Syntax_Syntax.sigrng =
            (uu___145_22096.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___145_22096.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___145_22096.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___145_22096.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____22134 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____22137 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____22144) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____22173,(FStar_Util.Inl t,uu____22175),uu____22176)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____22223,(FStar_Util.Inr c,uu____22225),uu____22226)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____22273 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____22274,(FStar_Util.Inl t,uu____22276),uu____22277) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____22324,(FStar_Util.Inr c,uu____22326),uu____22327) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____22374 -> empty_set  in
          FStar_Util.set_union uu____22134 uu____22137  in
        let all_lb_univs =
          let uu____22378 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____22394 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____22394) empty_set)
             in
          FStar_All.pipe_right uu____22378 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___146_22404 = s  in
        let uu____22405 =
          let uu____22406 =
            let uu____22413 =
              let uu____22420 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___147_22432 = lb  in
                        let uu____22433 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____22436 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___147_22432.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____22433;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___147_22432.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____22436;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___147_22432.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___147_22432.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____22420)  in
            (uu____22413, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____22406  in
        {
          FStar_Syntax_Syntax.sigel = uu____22405;
          FStar_Syntax_Syntax.sigrng =
            (uu___146_22404.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___146_22404.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___146_22404.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___146_22404.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____22450,fml) ->
        let uvs =
          let uu____22455 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____22455 FStar_Util.set_elements  in
        let uu___148_22462 = s  in
        let uu____22463 =
          let uu____22464 =
            let uu____22471 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____22471)  in
          FStar_Syntax_Syntax.Sig_assume uu____22464  in
        {
          FStar_Syntax_Syntax.sigel = uu____22463;
          FStar_Syntax_Syntax.sigrng =
            (uu___148_22462.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___148_22462.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___148_22462.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___148_22462.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____22475,bs,c,flags1) ->
        let uvs =
          let uu____22486 =
            let uu____22489 = bs_univnames bs  in
            let uu____22492 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____22489 uu____22492  in
          FStar_All.pipe_right uu____22486 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___149_22502 = s  in
        let uu____22503 =
          let uu____22504 =
            let uu____22517 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____22518 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____22517, uu____22518, flags1)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____22504  in
        {
          FStar_Syntax_Syntax.sigel = uu____22503;
          FStar_Syntax_Syntax.sigrng =
            (uu___149_22502.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___149_22502.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___149_22502.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___149_22502.FStar_Syntax_Syntax.sigattrs)
        }
    | uu____22523 -> s
  
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
          | (FStar_Pervasives_Native.None ,uu____22558) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____22562;
               FStar_Syntax_Syntax.exports = uu____22563;
               FStar_Syntax_Syntax.is_interface = uu____22564;_},FStar_Parser_AST.Module
             (current_lid,uu____22566)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____22574) ->
              let uu____22577 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____22577
           in
        let uu____22582 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____22618 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____22618, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____22635 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____22635, mname, decls, false)
           in
        match uu____22582 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____22665 = desugar_decls env2 decls  in
            (match uu____22665 with
             | (env3,sigelts) ->
                 let sigelts1 =
                   FStar_All.pipe_right sigelts
                     (FStar_List.map generalize_annotated_univs)
                    in
                 let modul =
                   {
                     FStar_Syntax_Syntax.name = mname;
                     FStar_Syntax_Syntax.declarations = sigelts1;
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
          let uu____22734 =
            (FStar_Options.interactive ()) &&
              (let uu____22736 =
                 let uu____22737 =
                   let uu____22738 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____22738  in
                 FStar_Util.get_file_extension uu____22737  in
               FStar_List.mem uu____22736 ["fsti"; "fsi"])
             in
          if uu____22734 then as_interface m else m  in
        let uu____22742 = desugar_modul_common curmod env m1  in
        match uu____22742 with
        | (x,y,pop_when_done) ->
            let uu____22756 =
              if pop_when_done
              then let uu____22757 = FStar_Syntax_DsEnv.pop ()  in ()
              else ()  in
            (x, y)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul ->
      (env_t,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun m  ->
      let uu____22777 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____22777 with
      | (env1,modul,pop_when_done) ->
          let uu____22791 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____22791 with
           | (env2,modul1) ->
               let uu____22802 =
                 let uu____22803 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____22803
                 then
                   let uu____22804 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____22804
                 else ()  in
               let uu____22806 =
                 if pop_when_done
                 then
                   FStar_Syntax_DsEnv.export_interface
                     modul1.FStar_Syntax_Syntax.name env2
                 else env2  in
               (uu____22806, modul1))
  
let (ast_modul_to_modul :
  FStar_Parser_AST.modul ->
    FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun env  ->
      let uu____22824 = desugar_modul env modul  in
      match uu____22824 with | (env1,modul1) -> (modul1, env1)
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      let uu____22855 = desugar_decls env decls  in
      match uu____22855 with | (env1,sigelts) -> (sigelts, env1)
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        let uu____22899 = desugar_partial_modul modul env a_modul  in
        match uu____22899 with | (env1,modul1) -> (modul1, env1)
  
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
              | uu____22983 ->
                  let t =
                    let uu____22991 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____22991  in
                  let uu____23000 =
                    let uu____23001 = FStar_Syntax_Subst.compress t  in
                    uu____23001.FStar_Syntax_Syntax.n  in
                  (match uu____23000 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____23011,uu____23012)
                       -> bs1
                   | uu____23033 -> failwith "Impossible")
               in
            let uu____23040 =
              let uu____23047 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____23047
                FStar_Syntax_Syntax.t_unit
               in
            match uu____23040 with
            | (binders,uu____23049,binders_opening) ->
                let erase_term t =
                  let uu____23056 =
                    let uu____23057 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____23057  in
                  FStar_Syntax_Subst.close binders uu____23056  in
                let erase_tscheme uu____23074 =
                  match uu____23074 with
                  | (us,t) ->
                      let t1 =
                        let uu____23094 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____23094 t  in
                      let uu____23097 =
                        let uu____23098 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____23098  in
                      ([], uu____23097)
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
                    | uu____23128 ->
                        let bs =
                          let uu____23136 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____23136  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____23166 =
                          let uu____23167 =
                            let uu____23170 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____23170  in
                          uu____23167.FStar_Syntax_Syntax.n  in
                        (match uu____23166 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____23178,uu____23179) -> bs1
                         | uu____23200 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____23212 =
                      let uu____23213 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____23213  in
                    FStar_Syntax_Subst.close binders uu____23212  in
                  let uu___150_23214 = action  in
                  let uu____23215 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____23216 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___150_23214.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___150_23214.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____23215;
                    FStar_Syntax_Syntax.action_typ = uu____23216
                  }  in
                let uu___151_23217 = ed  in
                let uu____23218 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____23219 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____23220 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____23221 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____23222 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____23223 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____23224 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____23225 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____23226 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____23227 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____23228 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____23229 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____23230 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____23231 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____23232 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____23233 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___151_23217.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___151_23217.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____23218;
                  FStar_Syntax_Syntax.signature = uu____23219;
                  FStar_Syntax_Syntax.ret_wp = uu____23220;
                  FStar_Syntax_Syntax.bind_wp = uu____23221;
                  FStar_Syntax_Syntax.if_then_else = uu____23222;
                  FStar_Syntax_Syntax.ite_wp = uu____23223;
                  FStar_Syntax_Syntax.stronger = uu____23224;
                  FStar_Syntax_Syntax.close_wp = uu____23225;
                  FStar_Syntax_Syntax.assert_p = uu____23226;
                  FStar_Syntax_Syntax.assume_p = uu____23227;
                  FStar_Syntax_Syntax.null_wp = uu____23228;
                  FStar_Syntax_Syntax.trivial = uu____23229;
                  FStar_Syntax_Syntax.repr = uu____23230;
                  FStar_Syntax_Syntax.return_repr = uu____23231;
                  FStar_Syntax_Syntax.bind_repr = uu____23232;
                  FStar_Syntax_Syntax.actions = uu____23233;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___151_23217.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___152_23247 = se  in
                  let uu____23248 =
                    let uu____23249 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____23249  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____23248;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___152_23247.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___152_23247.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___152_23247.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___152_23247.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___153_23253 = se  in
                  let uu____23254 =
                    let uu____23255 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____23255
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____23254;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___153_23253.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___153_23253.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___153_23253.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___153_23253.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____23257 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____23258 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____23258 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____23270 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____23270
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____23272 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____23272)
  