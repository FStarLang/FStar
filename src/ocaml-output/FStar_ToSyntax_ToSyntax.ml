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
  fun uu___111_66  ->
    match uu___111_66 with
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
      fun uu___112_90  ->
        match uu___112_90 with
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
  fun uu___113_99  ->
    match uu___113_99 with
    | FStar_Parser_AST.SetOptions s -> FStar_Syntax_Syntax.SetOptions s
    | FStar_Parser_AST.ResetOptions sopt ->
        FStar_Syntax_Syntax.ResetOptions sopt
    | FStar_Parser_AST.LightOff  -> FStar_Syntax_Syntax.LightOff
  
let (as_imp :
  FStar_Parser_AST.imp ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
  =
  fun uu___114_110  ->
    match uu___114_110 with
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
            let uu____332 =
              let uu____333 =
                let uu____334 =
                  FStar_Ident.set_lid_range l op.FStar_Ident.idRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____334 dd
                  FStar_Pervasives_Native.None
                 in
              FStar_All.pipe_right uu____333 FStar_Syntax_Syntax.fv_to_tm  in
            FStar_Pervasives_Native.Some uu____332  in
          let fallback uu____342 =
            let uu____343 = FStar_Ident.text_of_id op  in
            match uu____343 with
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
                let uu____346 = FStar_Options.ml_ish ()  in
                if uu____346
                then
                  r FStar_Parser_Const.list_append_lid
                    FStar_Syntax_Syntax.delta_equational
                else
                  r FStar_Parser_Const.list_tot_append_lid
                    FStar_Syntax_Syntax.delta_equational
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
            | uu____350 -> FStar_Pervasives_Native.None  in
          let uu____351 =
            let uu____358 =
              compile_op_lid arity op.FStar_Ident.idText
                op.FStar_Ident.idRange
               in
            FStar_Syntax_DsEnv.try_lookup_lid env uu____358  in
          match uu____351 with
          | FStar_Pervasives_Native.Some t ->
              FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst t)
          | uu____370 -> fallback ()
  
let (sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list)
  =
  fun ftv  ->
    let uu____388 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv
       in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____388
  
let rec (free_type_vars_b :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Syntax_DsEnv.env,FStar_Ident.ident Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____435 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____439 = FStar_Syntax_DsEnv.push_bv env x  in
          (match uu____439 with | (env1,uu____451) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____454,term) ->
          let uu____456 = free_type_vars env term  in (env, uu____456)
      | FStar_Parser_AST.TAnnotated (id1,uu____462) ->
          let uu____463 = FStar_Syntax_DsEnv.push_bv env id1  in
          (match uu____463 with | (env1,uu____475) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____479 = free_type_vars env t  in (env, uu____479)

and (free_type_vars :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun t  ->
      let uu____486 =
        let uu____487 = unparen t  in uu____487.FStar_Parser_AST.tm  in
      match uu____486 with
      | FStar_Parser_AST.Labeled uu____490 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____500 = FStar_Syntax_DsEnv.try_lookup_id env a  in
          (match uu____500 with
           | FStar_Pervasives_Native.None  -> [a]
           | uu____513 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____520 -> []
      | FStar_Parser_AST.Uvar uu____521 -> []
      | FStar_Parser_AST.Var uu____522 -> []
      | FStar_Parser_AST.Projector uu____523 -> []
      | FStar_Parser_AST.Discrim uu____528 -> []
      | FStar_Parser_AST.Name uu____529 -> []
      | FStar_Parser_AST.Requires (t1,uu____531) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____537) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____542,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None  -> []
             | FStar_Pervasives_Native.Some t2 -> [t2])
             in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____560,ts) ->
          FStar_List.collect
            (fun uu____581  ->
               match uu____581 with | (t1,uu____589) -> free_type_vars env t1)
            ts
      | FStar_Parser_AST.Op (uu____590,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____598) ->
          let uu____599 = free_type_vars env t1  in
          let uu____602 = free_type_vars env t2  in
          FStar_List.append uu____599 uu____602
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____607 = free_type_vars_b env b  in
          (match uu____607 with
           | (env1,f) ->
               let uu____622 = free_type_vars env1 t1  in
               FStar_List.append f uu____622)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____631 =
            FStar_List.fold_left
              (fun uu____651  ->
                 fun binder  ->
                   match uu____651 with
                   | (env1,free) ->
                       let uu____671 = free_type_vars_b env1 binder  in
                       (match uu____671 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____631 with
           | (env1,free) ->
               let uu____702 = free_type_vars env1 body  in
               FStar_List.append free uu____702)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____711 =
            FStar_List.fold_left
              (fun uu____731  ->
                 fun binder  ->
                   match uu____731 with
                   | (env1,free) ->
                       let uu____751 = free_type_vars_b env1 binder  in
                       (match uu____751 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____711 with
           | (env1,free) ->
               let uu____782 = free_type_vars env1 body  in
               FStar_List.append free uu____782)
      | FStar_Parser_AST.Project (t1,uu____786) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.Abs uu____790 -> []
      | FStar_Parser_AST.Let uu____797 -> []
      | FStar_Parser_AST.LetOpen uu____818 -> []
      | FStar_Parser_AST.If uu____823 -> []
      | FStar_Parser_AST.QForall uu____830 -> []
      | FStar_Parser_AST.QExists uu____843 -> []
      | FStar_Parser_AST.Record uu____856 -> []
      | FStar_Parser_AST.Match uu____869 -> []
      | FStar_Parser_AST.TryWith uu____884 -> []
      | FStar_Parser_AST.Bind uu____899 -> []
      | FStar_Parser_AST.Quote uu____906 -> []
      | FStar_Parser_AST.VQuote uu____911 -> []
      | FStar_Parser_AST.Antiquote uu____912 -> []
      | FStar_Parser_AST.Seq uu____917 -> []

let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term,(FStar_Parser_AST.term,FStar_Parser_AST.imp)
                             FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    let rec aux args t1 =
      let uu____970 =
        let uu____971 = unparen t1  in uu____971.FStar_Parser_AST.tm  in
      match uu____970 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____1013 -> (t1, args)  in
    aux [] t
  
let (close :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____1037 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1037  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1056 =
                     let uu____1057 =
                       let uu____1062 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____1062)  in
                     FStar_Parser_AST.TAnnotated uu____1057  in
                   FStar_Parser_AST.mk_binder uu____1056
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
        let uu____1079 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1079  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1098 =
                     let uu____1099 =
                       let uu____1104 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____1104)  in
                     FStar_Parser_AST.TAnnotated uu____1099  in
                   FStar_Parser_AST.mk_binder uu____1098
                     x.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____1106 =
             let uu____1107 = unparen t  in uu____1107.FStar_Parser_AST.tm
              in
           match uu____1106 with
           | FStar_Parser_AST.Product uu____1108 -> t
           | uu____1115 ->
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
      | uu____1151 -> (bs, t)
  
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild  -> true
    | FStar_Parser_AST.PatTvar (uu____1159,uu____1160) -> true
    | FStar_Parser_AST.PatVar (uu____1165,uu____1166) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____1172) -> is_var_pattern p1
    | uu____1185 -> false
  
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____1192) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____1205;
           FStar_Parser_AST.prange = uu____1206;_},uu____1207)
        -> true
    | uu____1218 -> false
  
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
    | uu____1232 -> p
  
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
            let uu____1302 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____1302 with
             | (name,args,uu____1345) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1395);
               FStar_Parser_AST.prange = uu____1396;_},args)
            when is_top_level1 ->
            let uu____1406 =
              let uu____1411 = FStar_Syntax_DsEnv.qualify env id1  in
              FStar_Util.Inr uu____1411  in
            (uu____1406, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1433);
               FStar_Parser_AST.prange = uu____1434;_},args)
            -> ((FStar_Util.Inl id1), args, FStar_Pervasives_Native.None)
        | uu____1464 -> failwith "Not an app pattern"
  
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
      | FStar_Parser_AST.PatConst uu____1514 -> acc
      | FStar_Parser_AST.PatVar
          (uu____1515,FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit
           ))
          -> acc
      | FStar_Parser_AST.PatName uu____1518 -> acc
      | FStar_Parser_AST.PatTvar uu____1519 -> acc
      | FStar_Parser_AST.PatOp uu____1526 -> acc
      | FStar_Parser_AST.PatApp (phead,pats) ->
          gather_pattern_bound_vars_from_list (phead :: pats)
      | FStar_Parser_AST.PatVar (x,uu____1534) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatTuple (pats,uu____1543) ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu____1558 =
            FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
          gather_pattern_bound_vars_from_list uu____1558
      | FStar_Parser_AST.PatAscribed (pat,uu____1566) ->
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
    match projectee with | LocalBinder _0 -> true | uu____1628 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____1664 -> false
  
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
  fun uu___115_1710  ->
    match uu___115_1710 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____1717 -> failwith "Impossible"
  
let (as_binder :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      (FStar_Ident.ident FStar_Pervasives_Native.option,FStar_Syntax_Syntax.term'
                                                          FStar_Syntax_Syntax.syntax)
        FStar_Pervasives_Native.tuple2 ->
        ((FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                                   FStar_Pervasives_Native.option)
           FStar_Pervasives_Native.tuple2,FStar_Syntax_DsEnv.env)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun imp  ->
      fun uu___116_1756  ->
        match uu___116_1756 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____1784 = FStar_Syntax_Syntax.null_binder k  in
            (uu____1784, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____1793 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____1793 with
             | (env1,a1) ->
                 (((let uu___140_1819 = a1  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___140_1819.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___140_1819.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = k
                    }), (trans_aqual imp)), env1))
  
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
  fun uu____1848  ->
    match uu____1848 with
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
      let uu____1928 =
        let uu____1943 =
          let uu____1946 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____1946  in
        let uu____1947 =
          let uu____1956 =
            let uu____1963 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____1963)  in
          [uu____1956]  in
        (uu____1943, uu____1947)  in
      FStar_Syntax_Syntax.Tm_app uu____1928  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____2000 =
        let uu____2015 =
          let uu____2018 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____2018  in
        let uu____2019 =
          let uu____2028 =
            let uu____2035 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2035)  in
          [uu____2028]  in
        (uu____2015, uu____2019)  in
      FStar_Syntax_Syntax.Tm_app uu____2000  in
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
          let uu____2086 =
            let uu____2101 =
              let uu____2104 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____2104  in
            let uu____2105 =
              let uu____2114 =
                let uu____2121 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____2121)  in
              let uu____2124 =
                let uu____2133 =
                  let uu____2140 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____2140)  in
                [uu____2133]  in
              uu____2114 :: uu____2124  in
            (uu____2101, uu____2105)  in
          FStar_Syntax_Syntax.Tm_app uu____2086  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let (generalize_annotated_univs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun s  ->
    let bs_univnames bs =
      let uu____2186 =
        let uu____2199 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____2216  ->
               match uu____2216 with
               | ({ FStar_Syntax_Syntax.ppname = uu____2225;
                    FStar_Syntax_Syntax.index = uu____2226;
                    FStar_Syntax_Syntax.sort = t;_},uu____2228)
                   ->
                   let uu____2231 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____2231) uu____2199
         in
      FStar_All.pipe_right bs uu____2186  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____2245 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____2262 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____2288 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____2309,uu____2310,bs,t,uu____2313,uu____2314)
                            ->
                            let uu____2323 = bs_univnames bs  in
                            let uu____2326 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____2323 uu____2326
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____2329,uu____2330,t,uu____2332,uu____2333,uu____2334)
                            -> FStar_Syntax_Free.univnames t
                        | uu____2339 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____2288 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___141_2347 = s  in
        let uu____2348 =
          let uu____2349 =
            let uu____2358 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____2376,bs,t,lids1,lids2) ->
                          let uu___142_2389 = se  in
                          let uu____2390 =
                            let uu____2391 =
                              let uu____2408 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____2409 =
                                let uu____2410 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____2410 t  in
                              (lid, uvs, uu____2408, uu____2409, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____2391
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____2390;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___142_2389.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___142_2389.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___142_2389.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___142_2389.FStar_Syntax_Syntax.sigattrs)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____2422,t,tlid,n1,lids1) ->
                          let uu___143_2431 = se  in
                          let uu____2432 =
                            let uu____2433 =
                              let uu____2448 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____2448, tlid, n1, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____2433  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____2432;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___143_2431.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___143_2431.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___143_2431.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___143_2431.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____2451 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____2358, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____2349  in
        {
          FStar_Syntax_Syntax.sigel = uu____2348;
          FStar_Syntax_Syntax.sigrng =
            (uu___141_2347.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___141_2347.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___141_2347.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___141_2347.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2457,t) ->
        let uvs =
          let uu____2460 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____2460 FStar_Util.set_elements  in
        let uu___144_2465 = s  in
        let uu____2466 =
          let uu____2467 =
            let uu____2474 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____2474)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____2467  in
        {
          FStar_Syntax_Syntax.sigel = uu____2466;
          FStar_Syntax_Syntax.sigrng =
            (uu___144_2465.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___144_2465.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___144_2465.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___144_2465.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____2496 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____2499 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____2506) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____2535,(FStar_Util.Inl t,uu____2537),uu____2538)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____2585,(FStar_Util.Inr c,uu____2587),uu____2588)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____2635 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____2636,(FStar_Util.Inl t,uu____2638),uu____2639) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____2686,(FStar_Util.Inr c,uu____2688),uu____2689) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____2736 -> empty_set  in
          FStar_Util.set_union uu____2496 uu____2499  in
        let all_lb_univs =
          let uu____2740 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____2756 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____2756) empty_set)
             in
          FStar_All.pipe_right uu____2740 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___145_2766 = s  in
        let uu____2767 =
          let uu____2768 =
            let uu____2775 =
              let uu____2776 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___146_2788 = lb  in
                        let uu____2789 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____2792 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___146_2788.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____2789;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___146_2788.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____2792;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___146_2788.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___146_2788.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____2776)  in
            (uu____2775, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____2768  in
        {
          FStar_Syntax_Syntax.sigel = uu____2767;
          FStar_Syntax_Syntax.sigrng =
            (uu___145_2766.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___145_2766.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___145_2766.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___145_2766.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____2800,fml) ->
        let uvs =
          let uu____2803 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____2803 FStar_Util.set_elements  in
        let uu___147_2808 = s  in
        let uu____2809 =
          let uu____2810 =
            let uu____2817 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____2817)  in
          FStar_Syntax_Syntax.Sig_assume uu____2810  in
        {
          FStar_Syntax_Syntax.sigel = uu____2809;
          FStar_Syntax_Syntax.sigrng =
            (uu___147_2808.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___147_2808.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___147_2808.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___147_2808.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____2819,bs,c,flags1) ->
        let uvs =
          let uu____2828 =
            let uu____2831 = bs_univnames bs  in
            let uu____2834 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____2831 uu____2834  in
          FStar_All.pipe_right uu____2828 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___148_2842 = s  in
        let uu____2843 =
          let uu____2844 =
            let uu____2857 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____2858 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____2857, uu____2858, flags1)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____2844  in
        {
          FStar_Syntax_Syntax.sigel = uu____2843;
          FStar_Syntax_Syntax.sigrng =
            (uu___148_2842.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___148_2842.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___148_2842.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___148_2842.FStar_Syntax_Syntax.sigattrs)
        }
    | uu____2861 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___117_2866  ->
    match uu___117_2866 with
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
    | uu____2867 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____2879 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____2879)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____2898 =
      let uu____2899 = unparen t  in uu____2899.FStar_Parser_AST.tm  in
    match uu____2898 with
    | FStar_Parser_AST.Wild  ->
        let uu____2904 =
          let uu____2905 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____2905  in
        FStar_Util.Inr uu____2904
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____2916)) ->
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
             let uu____2981 = sum_to_universe u n1  in
             FStar_Util.Inr uu____2981
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____2992 = sum_to_universe u n1  in
             FStar_Util.Inr uu____2992
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____3003 =
               let uu____3008 =
                 let uu____3009 = FStar_Parser_AST.term_to_string t  in
                 Prims.strcat
                   "This universe might contain a sum of two universe variables "
                   uu____3009
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____3008)
                in
             FStar_Errors.raise_error uu____3003 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____3014 ->
        let rec aux t1 univargs =
          let uu____3048 =
            let uu____3049 = unparen t1  in uu____3049.FStar_Parser_AST.tm
             in
          match uu____3048 with
          | FStar_Parser_AST.App (t2,targ,uu____3056) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___118_3079  ->
                     match uu___118_3079 with
                     | FStar_Util.Inr uu____3084 -> true
                     | uu____3085 -> false) univargs
              then
                let uu____3090 =
                  let uu____3091 =
                    FStar_List.map
                      (fun uu___119_3100  ->
                         match uu___119_3100 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____3091  in
                FStar_Util.Inr uu____3090
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___120_3117  ->
                        match uu___120_3117 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____3123 -> failwith "impossible")
                     univargs
                    in
                 let uu____3124 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____3124)
          | uu____3130 ->
              let uu____3131 =
                let uu____3136 =
                  let uu____3137 =
                    let uu____3138 = FStar_Parser_AST.term_to_string t1  in
                    Prims.strcat uu____3138 " in universe context"  in
                  Prims.strcat "Unexpected term " uu____3137  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3136)  in
              FStar_Errors.raise_error uu____3131 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____3147 ->
        let uu____3148 =
          let uu____3153 =
            let uu____3154 =
              let uu____3155 = FStar_Parser_AST.term_to_string t  in
              Prims.strcat uu____3155 " in universe context"  in
            Prims.strcat "Unexpected term " uu____3154  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3153)  in
        FStar_Errors.raise_error uu____3148 t.FStar_Parser_AST.range
  
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
    | (bv,b,e)::uu____3188 ->
        let uu____3211 =
          let uu____3216 =
            let uu____3217 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format2 "Unexpected antiquotation: %s(%s)"
              (if b then "`@" else "`#") uu____3217
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____3216)  in
        FStar_Errors.raise_error uu____3211 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'Auu____3227 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident,'Auu____3227) FStar_Pervasives_Native.tuple2
        Prims.list -> FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____3255 = FStar_List.hd fields  in
        match uu____3255 with
        | (f,uu____3265) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____3277 =
                match uu____3277 with
                | (f',uu____3283) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____3285 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____3285
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
              (let uu____3289 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____3289);
              (match () with | () -> record)))
  
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
            | FStar_Syntax_Syntax.Pat_dot_term uu____3640 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_wild uu____3647 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_constant uu____3648 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_var x ->
                FStar_Util.set_add x FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_cons (uu____3650,pats1) ->
                let aux out uu____3688 =
                  match uu____3688 with
                  | (p2,uu____3700) ->
                      let intersection =
                        let uu____3708 = pat_vars p2  in
                        FStar_Util.set_intersect uu____3708 out  in
                      let uu____3711 = FStar_Util.set_is_empty intersection
                         in
                      if uu____3711
                      then
                        let uu____3714 = pat_vars p2  in
                        FStar_Util.set_union out uu____3714
                      else
                        (let duplicate_bv =
                           let uu____3719 =
                             FStar_Util.set_elements intersection  in
                           FStar_List.hd uu____3719  in
                         let uu____3722 =
                           let uu____3727 =
                             FStar_Util.format1
                               "Non-linear patterns are not permitted. %s appears more than once in this pattern."
                               (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                              in
                           (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                             uu____3727)
                            in
                         FStar_Errors.raise_error uu____3722 r)
                   in
                FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
             in
          match pats with
          | [] -> ()
          | p1::[] ->
              let uu____3747 = pat_vars p1  in
              FStar_All.pipe_right uu____3747 (fun a237  -> ())
          | p1::ps ->
              let pvars = pat_vars p1  in
              let aux p2 =
                let uu____3775 =
                  let uu____3776 = pat_vars p2  in
                  FStar_Util.set_eq pvars uu____3776  in
                if uu____3775
                then ()
                else
                  (let nonlinear_vars =
                     let uu____3783 = pat_vars p2  in
                     FStar_Util.set_symmetric_difference pvars uu____3783  in
                   let first_nonlinear_var =
                     let uu____3787 = FStar_Util.set_elements nonlinear_vars
                        in
                     FStar_List.hd uu____3787  in
                   let uu____3790 =
                     let uu____3795 =
                       FStar_Util.format1
                         "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                         (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                        in
                     (FStar_Errors.Fatal_IncoherentPatterns, uu____3795)  in
                   FStar_Errors.raise_error uu____3790 r)
                 in
              FStar_List.iter aux ps
           in
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false ,uu____3799) -> ()
         | (true ,FStar_Parser_AST.PatVar uu____3800) -> ()
         | (true ,uu____3807) ->
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_LetMutableForVariablesOnly,
                 "let-mutable is for variables only")
               p.FStar_Parser_AST.prange);
        (let resolvex l e x =
           let uu____3830 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText))
              in
           match uu____3830 with
           | FStar_Pervasives_Native.Some y -> (l, e, y)
           | uu____3846 ->
               let uu____3849 =
                 if is_mut
                 then FStar_Syntax_DsEnv.push_bv_mutable e x
                 else FStar_Syntax_DsEnv.push_bv e x  in
               (match uu____3849 with | (e1,x1) -> ((x1 :: l), e1, x1))
            in
         let rec aux' top loc env1 p1 =
           let pos q =
             FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange  in
           let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
           let orig = p1  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr uu____3961 -> failwith "impossible"
           | FStar_Parser_AST.PatOp op ->
               let uu____3977 =
                 let uu____3978 =
                   let uu____3979 =
                     let uu____3986 =
                       let uu____3987 =
                         let uu____3992 =
                           FStar_Parser_AST.compile_op (Prims.parse_int "0")
                             op.FStar_Ident.idText op.FStar_Ident.idRange
                            in
                         (uu____3992, (op.FStar_Ident.idRange))  in
                       FStar_Ident.mk_ident uu____3987  in
                     (uu____3986, FStar_Pervasives_Native.None)  in
                   FStar_Parser_AST.PatVar uu____3979  in
                 {
                   FStar_Parser_AST.pat = uu____3978;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 }  in
               aux loc env1 uu____3977
           | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
               ((match tacopt with
                 | FStar_Pervasives_Native.None  -> ()
                 | FStar_Pervasives_Native.Some uu____4009 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                         "Type ascriptions within patterns are cannot be associated with a tactic")
                       orig.FStar_Parser_AST.prange);
                (let uu____4010 = aux loc env1 p2  in
                 match uu____4010 with
                 | (loc1,env',binder,p3,imp) ->
                     let annot_pat_var p4 t1 =
                       match p4.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let uu___149_4068 = p4  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var
                                  (let uu___150_4073 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___150_4073.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___150_4073.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }));
                             FStar_Syntax_Syntax.p =
                               (uu___149_4068.FStar_Syntax_Syntax.p)
                           }
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let uu___151_4075 = p4  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild
                                  (let uu___152_4080 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___152_4080.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___152_4080.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }));
                             FStar_Syntax_Syntax.p =
                               (uu___151_4075.FStar_Syntax_Syntax.p)
                           }
                       | uu____4081 when top -> p4
                       | uu____4082 ->
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                               "Type ascriptions within patterns are only allowed on variables")
                             orig.FStar_Parser_AST.prange
                        in
                     let uu____4085 =
                       match binder with
                       | LetBinder uu____4098 -> failwith "impossible"
                       | LocalBinder (x,aq) ->
                           let t1 =
                             let uu____4118 = close_fun env1 t  in
                             desugar_term env1 uu____4118  in
                           (if
                              (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                               with
                               | FStar_Syntax_Syntax.Tm_unknown  -> false
                               | uu____4120 -> true)
                            then
                              (let uu____4121 =
                                 let uu____4126 =
                                   let uu____4127 =
                                     FStar_Syntax_Print.bv_to_string x  in
                                   let uu____4128 =
                                     FStar_Syntax_Print.term_to_string
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____4129 =
                                     FStar_Syntax_Print.term_to_string t1  in
                                   FStar_Util.format3
                                     "Multiple ascriptions for %s in pattern, type %s was shadowed by %s\n"
                                     uu____4127 uu____4128 uu____4129
                                    in
                                 (FStar_Errors.Warning_MultipleAscriptions,
                                   uu____4126)
                                  in
                               FStar_Errors.log_issue
                                 orig.FStar_Parser_AST.prange uu____4121)
                            else ();
                            (let uu____4131 = annot_pat_var p3 t1  in
                             (uu____4131,
                               (LocalBinder
                                  ((let uu___153_4137 = x  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___153_4137.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___153_4137.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    }), aq)))))
                        in
                     (match uu____4085 with
                      | (p4,binder1) -> (loc1, env', binder1, p4, imp))))
           | FStar_Parser_AST.PatWild  ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____4159 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____4159, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____4168 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____4168, false)
           | FStar_Parser_AST.PatTvar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual aq  in
               let uu____4187 = resolvex loc env1 x  in
               (match uu____4187 with
                | (loc1,env2,xbv) ->
                    let uu____4209 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____4209, imp))
           | FStar_Parser_AST.PatVar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual aq  in
               let uu____4228 = resolvex loc env1 x  in
               (match uu____4228 with
                | (loc1,env2,xbv) ->
                    let uu____4250 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____4250, imp))
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
               let uu____4260 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, []))
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____4260, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____4282;_},args)
               ->
               let uu____4288 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____4329  ->
                        match uu____4329 with
                        | (loc1,env2,args1) ->
                            let uu____4377 = aux loc1 env2 arg  in
                            (match uu____4377 with
                             | (loc2,env3,uu____4406,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, [])
                  in
               (match uu____4288 with
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
                    let uu____4476 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                       in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)),
                      uu____4476, false))
           | FStar_Parser_AST.PatApp uu____4491 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                 p1.FStar_Parser_AST.prange
           | FStar_Parser_AST.PatList pats ->
               let uu____4513 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____4546  ->
                        match uu____4546 with
                        | (loc1,env2,pats1) ->
                            let uu____4578 = aux loc1 env2 pat  in
                            (match uu____4578 with
                             | (loc2,env3,uu____4603,pat1,uu____4605) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, [])
                  in
               (match uu____4513 with
                | (loc1,env2,pats1) ->
                    let pat =
                      let uu____4648 =
                        let uu____4651 =
                          let uu____4658 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange
                             in
                          pos_r uu____4658  in
                        let uu____4659 =
                          let uu____4660 =
                            let uu____4673 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Parser_Const.nil_lid
                                FStar_Syntax_Syntax.delta_constant
                                (FStar_Pervasives_Native.Some
                                   FStar_Syntax_Syntax.Data_ctor)
                               in
                            (uu____4673, [])  in
                          FStar_Syntax_Syntax.Pat_cons uu____4660  in
                        FStar_All.pipe_left uu____4651 uu____4659  in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p
                                in
                             let uu____4705 =
                               let uu____4706 =
                                 let uu____4719 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.cons_lid
                                     FStar_Syntax_Syntax.delta_constant
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Data_ctor)
                                    in
                                 (uu____4719, [(hd1, false); (tl1, false)])
                                  in
                               FStar_Syntax_Syntax.Pat_cons uu____4706  in
                             FStar_All.pipe_left (pos_r r) uu____4705) pats1
                        uu____4648
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
               let uu____4761 =
                 FStar_List.fold_left
                   (fun uu____4801  ->
                      fun p2  ->
                        match uu____4801 with
                        | (loc1,env2,pats) ->
                            let uu____4850 = aux loc1 env2 p2  in
                            (match uu____4850 with
                             | (loc2,env3,uu____4879,pat,uu____4881) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args
                  in
               (match uu____4761 with
                | (loc1,env2,args1) ->
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
                    let uu____4976 =
                      FStar_Syntax_DsEnv.fail_or env2
                        (FStar_Syntax_DsEnv.try_lookup_lid env2) l
                       in
                    (match uu____4976 with
                     | (constr,uu____4998) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____5001 -> failwith "impossible"  in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (FStar_Pervasives_Native.Some
                                (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun
                            in
                         let uu____5003 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                            in
                         (loc1, env2,
                           (LocalBinder (x, FStar_Pervasives_Native.None)),
                           uu____5003, false)))
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
                      (fun uu____5072  ->
                         match uu____5072 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2)))
                  in
               let args =
                 FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                   (FStar_List.map
                      (fun uu____5102  ->
                         match uu____5102 with
                         | (f,uu____5108) ->
                             let uu____5109 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____5135  ->
                                       match uu____5135 with
                                       | (g,uu____5141) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText))
                                in
                             (match uu____5109 with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
                              | FStar_Pervasives_Native.Some (uu____5146,p2)
                                  -> p2)))
                  in
               let app =
                 let uu____5153 =
                   let uu____5154 =
                     let uu____5161 =
                       let uu____5162 =
                         let uu____5163 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                                [record.FStar_Syntax_DsEnv.constrname])
                            in
                         FStar_Parser_AST.PatName uu____5163  in
                       FStar_Parser_AST.mk_pattern uu____5162
                         p1.FStar_Parser_AST.prange
                        in
                     (uu____5161, args)  in
                   FStar_Parser_AST.PatApp uu____5154  in
                 FStar_Parser_AST.mk_pattern uu____5153
                   p1.FStar_Parser_AST.prange
                  in
               let uu____5166 = aux loc env1 app  in
               (match uu____5166 with
                | (env2,e,b,p2,uu____5195) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____5223 =
                            let uu____5224 =
                              let uu____5237 =
                                let uu___154_5238 = fv  in
                                let uu____5239 =
                                  let uu____5242 =
                                    let uu____5243 =
                                      let uu____5250 =
                                        FStar_All.pipe_right
                                          record.FStar_Syntax_DsEnv.fields
                                          (FStar_List.map
                                             FStar_Pervasives_Native.fst)
                                         in
                                      ((record.FStar_Syntax_DsEnv.typename),
                                        uu____5250)
                                       in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____5243
                                     in
                                  FStar_Pervasives_Native.Some uu____5242  in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___154_5238.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___154_5238.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____5239
                                }  in
                              (uu____5237, args1)  in
                            FStar_Syntax_Syntax.Pat_cons uu____5224  in
                          FStar_All.pipe_left pos uu____5223
                      | uu____5277 -> p2  in
                    (env2, e, b, p3, false))
         
         and aux loc env1 p1 = aux' false loc env1 p1
          in
         let aux_maybe_or env1 p1 =
           let loc = []  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____5331 = aux' true loc env1 p2  in
               (match uu____5331 with
                | (loc1,env2,var,p3,uu____5358) ->
                    let uu____5363 =
                      FStar_List.fold_left
                        (fun uu____5395  ->
                           fun p4  ->
                             match uu____5395 with
                             | (loc2,env3,ps1) ->
                                 let uu____5428 = aux' true loc2 env3 p4  in
                                 (match uu____5428 with
                                  | (loc3,env4,uu____5453,p5,uu____5455) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps
                       in
                    (match uu____5363 with
                     | (loc2,env3,ps1) ->
                         let pats = p3 :: (FStar_List.rev ps1)  in
                         (env3, var, pats)))
           | uu____5506 ->
               let uu____5507 = aux' true loc env1 p1  in
               (match uu____5507 with
                | (loc1,env2,vars,pat,b) -> (env2, vars, [pat]))
            in
         let uu____5547 = aux_maybe_or env p  in
         match uu____5547 with
         | (env1,b,pats) ->
             (check_linear_pattern_variables pats p.FStar_Parser_AST.prange;
              (env1, b, pats)))

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
            let uu____5606 =
              let uu____5607 =
                let uu____5618 = FStar_Syntax_DsEnv.qualify env x  in
                (uu____5618,
                  (FStar_Syntax_Syntax.tun, FStar_Pervasives_Native.None))
                 in
              LetBinder uu____5607  in
            (env, uu____5606, [])  in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____5646 =
                  let uu____5647 =
                    let uu____5652 =
                      FStar_Parser_AST.compile_op (Prims.parse_int "0")
                        x.FStar_Ident.idText x.FStar_Ident.idRange
                       in
                    (uu____5652, (x.FStar_Ident.idRange))  in
                  FStar_Ident.mk_ident uu____5647  in
                mklet uu____5646
            | FStar_Parser_AST.PatVar (x,uu____5654) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____5660);
                   FStar_Parser_AST.prange = uu____5661;_},(t,tacopt))
                ->
                let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)
                   in
                let uu____5681 =
                  let uu____5682 =
                    let uu____5693 = FStar_Syntax_DsEnv.qualify env x  in
                    let uu____5694 =
                      let uu____5701 = desugar_term env t  in
                      (uu____5701, tacopt1)  in
                    (uu____5693, uu____5694)  in
                  LetBinder uu____5682  in
                (env, uu____5681, [])
            | uu____5712 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_UnexpectedPattern,
                    "Unexpected pattern at the top-level")
                  p.FStar_Parser_AST.prange
          else
            (let uu____5722 = desugar_data_pat env p is_mut  in
             match uu____5722 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1 with
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                         uu____5751;
                       FStar_Syntax_Syntax.p = uu____5752;_}::[] -> []
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                         uu____5753;
                       FStar_Syntax_Syntax.p = uu____5754;_}::[] -> []
                   | uu____5755 -> p1  in
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
  fun uu____5762  ->
    fun env  ->
      fun pat  ->
        let uu____5765 = desugar_data_pat env pat false  in
        match uu____5765 with | (env1,uu____5781,pat1) -> (env1, pat1)

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
      let uu____5800 = desugar_term_aq env e  in
      match uu____5800 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____5817 = desugar_typ_aq env e  in
      match uu____5817 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness,FStar_Const.width)
        FStar_Pervasives_Native.tuple2 ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____5827  ->
        fun range  ->
          match uu____5827 with
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
              ((let uu____5837 =
                  let uu____5838 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____5838  in
                if uu____5837
                then
                  let uu____5839 =
                    let uu____5844 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____5844)  in
                  FStar_Errors.log_issue range uu____5839
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
                  let uu____5849 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____5849 range  in
                let lid1 =
                  let uu____5853 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____5853 with
                  | FStar_Pervasives_Native.Some (intro_term,uu____5863) ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____5872 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____5872 range  in
                           let private_fv =
                             let uu____5874 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____5874 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___155_5875 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___155_5875.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___155_5875.FStar_Syntax_Syntax.vars)
                           }
                       | uu____5876 ->
                           failwith
                             (Prims.strcat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____5883 =
                        let uu____5888 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____5888)
                         in
                      FStar_Errors.raise_error uu____5883 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____5904 =
                  let uu____5911 =
                    let uu____5912 =
                      let uu____5927 =
                        let uu____5936 =
                          let uu____5943 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____5943)  in
                        [uu____5936]  in
                      (lid1, uu____5927)  in
                    FStar_Syntax_Syntax.Tm_app uu____5912  in
                  FStar_Syntax_Syntax.mk uu____5911  in
                uu____5904 FStar_Pervasives_Native.None range))

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
            let uu____5982 =
              let uu____5991 =
                (if resolve
                 then FStar_Syntax_DsEnv.try_lookup_lid_with_attributes
                 else
                   FStar_Syntax_DsEnv.try_lookup_lid_with_attributes_no_resolve)
                  env
                 in
              FStar_Syntax_DsEnv.fail_or env uu____5991 l  in
            match uu____5982 with
            | (tm,mut,attrs) ->
                let warn_if_deprecated attrs1 =
                  FStar_List.iter
                    (fun a  ->
                       match a.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_app
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____6046;
                              FStar_Syntax_Syntax.vars = uu____6047;_},args)
                           when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____6070 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____6070 " is deprecated"  in
                           let msg1 =
                             if
                               (FStar_List.length args) >
                                 (Prims.parse_int "0")
                             then
                               let uu____6078 =
                                 let uu____6079 =
                                   let uu____6082 = FStar_List.hd args  in
                                   FStar_Pervasives_Native.fst uu____6082  in
                                 uu____6079.FStar_Syntax_Syntax.n  in
                               match uu____6078 with
                               | FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_string (s,uu____6098))
                                   when
                                   Prims.op_Negation
                                     ((FStar_Util.trim_string s) = "")
                                   ->
                                   Prims.strcat msg
                                     (Prims.strcat ", use "
                                        (Prims.strcat s " instead"))
                               | uu____6099 -> msg
                             else msg  in
                           let uu____6101 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____6101
                             (FStar_Errors.Warning_DeprecatedDefinition,
                               msg1)
                       | FStar_Syntax_Syntax.Tm_fvar fv when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____6104 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____6104 " is deprecated"  in
                           let uu____6105 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____6105
                             (FStar_Errors.Warning_DeprecatedDefinition, msg)
                       | uu____6106 -> ()) attrs1
                   in
                (warn_if_deprecated attrs;
                 (let tm1 = setpos tm  in
                  if mut
                  then
                    let uu____6111 =
                      let uu____6112 =
                        let uu____6119 = mk_ref_read tm1  in
                        (uu____6119,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Mutable_rval))
                         in
                      FStar_Syntax_Syntax.Tm_meta uu____6112  in
                    FStar_All.pipe_left mk1 uu____6111
                  else tm1))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____6137 =
          let uu____6138 = unparen t  in uu____6138.FStar_Parser_AST.tm  in
        match uu____6137 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____6139; FStar_Ident.ident = uu____6140;
              FStar_Ident.nsstr = uu____6141; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____6144 ->
            let uu____6145 =
              let uu____6150 =
                let uu____6151 = FStar_Parser_AST.term_to_string t  in
                Prims.strcat "Unknown attribute " uu____6151  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____6150)  in
            FStar_Errors.raise_error uu____6145 t.FStar_Parser_AST.range
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
          let uu___156_6246 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___156_6246.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___156_6246.FStar_Syntax_Syntax.vars)
          }  in
        let uu____6249 =
          let uu____6250 = unparen top  in uu____6250.FStar_Parser_AST.tm  in
        match uu____6249 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____6255 ->
            let uu____6262 = desugar_formula env top  in (uu____6262, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____6269 = desugar_formula env t  in (uu____6269, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____6276 = desugar_formula env t  in (uu____6276, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____6300 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____6300, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____6302 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____6302, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____6310 =
                let uu____6311 =
                  let uu____6318 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____6318, args)  in
                FStar_Parser_AST.Op uu____6311  in
              FStar_Parser_AST.mk_term uu____6310 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____6321 =
              let uu____6322 =
                let uu____6323 =
                  let uu____6330 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____6330, [e])  in
                FStar_Parser_AST.Op uu____6323  in
              FStar_Parser_AST.mk_term uu____6322 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____6321
        | FStar_Parser_AST.Op (op_star,uu____6334::uu____6335::[]) when
            (let uu____6340 = FStar_Ident.text_of_id op_star  in
             uu____6340 = "*") &&
              (let uu____6342 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____6342 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____6357;_},t1::t2::[])
                  ->
                  let uu____6362 = flatten1 t1  in
                  FStar_List.append uu____6362 [t2]
              | uu____6365 -> [t]  in
            let uu____6366 =
              let uu____6391 =
                let uu____6414 =
                  let uu____6417 = unparen top  in flatten1 uu____6417  in
                FStar_All.pipe_right uu____6414
                  (FStar_List.map
                     (fun t  ->
                        let uu____6436 = desugar_typ_aq env t  in
                        match uu____6436 with
                        | (t',aq) ->
                            let uu____6447 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____6447, aq)))
                 in
              FStar_All.pipe_right uu____6391 FStar_List.unzip  in
            (match uu____6366 with
             | (targs,aqs) ->
                 let uu____6556 =
                   let uu____6561 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____6561
                    in
                 (match uu____6556 with
                  | (tup,uu____6577) ->
                      let uu____6578 =
                        mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                      (uu____6578, (join_aqs aqs))))
        | FStar_Parser_AST.Tvar a ->
            let uu____6590 =
              let uu____6591 =
                let uu____6594 =
                  FStar_Syntax_DsEnv.fail_or2
                    (FStar_Syntax_DsEnv.try_lookup_id env) a
                   in
                FStar_Pervasives_Native.fst uu____6594  in
              FStar_All.pipe_left setpos uu____6591  in
            (uu____6590, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____6606 =
              let uu____6611 =
                let uu____6612 =
                  let uu____6613 = FStar_Ident.text_of_id u  in
                  Prims.strcat uu____6613 " in non-universe context"  in
                Prims.strcat "Unexpected universe variable " uu____6612  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____6611)  in
            FStar_Errors.raise_error uu____6606 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____6624 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____6624 with
             | FStar_Pervasives_Native.None  ->
                 let uu____6631 =
                   let uu____6636 =
                     let uu____6637 = FStar_Ident.text_of_id s  in
                     Prims.strcat "Unexpected or unbound operator: "
                       uu____6637
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____6636)
                    in
                 FStar_Errors.raise_error uu____6631
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let uu____6647 =
                     let uu____6672 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____6724 = desugar_term_aq env t  in
                               match uu____6724 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____6672 FStar_List.unzip  in
                   (match uu____6647 with
                    | (args1,aqs) ->
                        let uu____6857 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____6857, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____6871)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____6886 =
              let uu___157_6887 = top  in
              let uu____6888 =
                let uu____6889 =
                  let uu____6896 =
                    let uu___158_6897 = top  in
                    let uu____6898 =
                      let uu____6899 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____6899  in
                    {
                      FStar_Parser_AST.tm = uu____6898;
                      FStar_Parser_AST.range =
                        (uu___158_6897.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___158_6897.FStar_Parser_AST.level)
                    }  in
                  (uu____6896, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____6889  in
              {
                FStar_Parser_AST.tm = uu____6888;
                FStar_Parser_AST.range =
                  (uu___157_6887.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___157_6887.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____6886
        | FStar_Parser_AST.Construct (n1,(a,uu____6902)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____6918 =
                let uu___159_6919 = top  in
                let uu____6920 =
                  let uu____6921 =
                    let uu____6928 =
                      let uu___160_6929 = top  in
                      let uu____6930 =
                        let uu____6931 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____6931  in
                      {
                        FStar_Parser_AST.tm = uu____6930;
                        FStar_Parser_AST.range =
                          (uu___160_6929.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___160_6929.FStar_Parser_AST.level)
                      }  in
                    (uu____6928, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____6921  in
                {
                  FStar_Parser_AST.tm = uu____6920;
                  FStar_Parser_AST.range =
                    (uu___159_6919.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___159_6919.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____6918))
        | FStar_Parser_AST.Construct (n1,(a,uu____6934)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____6949 =
              let uu___161_6950 = top  in
              let uu____6951 =
                let uu____6952 =
                  let uu____6959 =
                    let uu___162_6960 = top  in
                    let uu____6961 =
                      let uu____6962 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____6962  in
                    {
                      FStar_Parser_AST.tm = uu____6961;
                      FStar_Parser_AST.range =
                        (uu___162_6960.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___162_6960.FStar_Parser_AST.level)
                    }  in
                  (uu____6959, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____6952  in
              {
                FStar_Parser_AST.tm = uu____6951;
                FStar_Parser_AST.range =
                  (uu___161_6950.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___161_6950.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____6949
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____6963; FStar_Ident.ident = uu____6964;
              FStar_Ident.nsstr = uu____6965; FStar_Ident.str = "Type0";_}
            ->
            let uu____6968 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____6968, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____6969; FStar_Ident.ident = uu____6970;
              FStar_Ident.nsstr = uu____6971; FStar_Ident.str = "Type";_}
            ->
            let uu____6974 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____6974, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____6975; FStar_Ident.ident = uu____6976;
               FStar_Ident.nsstr = uu____6977; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____6995 =
              let uu____6996 =
                let uu____6997 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____6997  in
              mk1 uu____6996  in
            (uu____6995, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____6998; FStar_Ident.ident = uu____6999;
              FStar_Ident.nsstr = uu____7000; FStar_Ident.str = "Effect";_}
            ->
            let uu____7003 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____7003, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____7004; FStar_Ident.ident = uu____7005;
              FStar_Ident.nsstr = uu____7006; FStar_Ident.str = "True";_}
            ->
            let uu____7009 =
              let uu____7010 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____7010
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____7009, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____7011; FStar_Ident.ident = uu____7012;
              FStar_Ident.nsstr = uu____7013; FStar_Ident.str = "False";_}
            ->
            let uu____7016 =
              let uu____7017 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____7017
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____7016, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____7020;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____7022 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____7022 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____7031 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_constant_at_level
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None
                     in
                  (uu____7031, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____7032 =
                    let uu____7033 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____7033 txt
                     in
                  failwith uu____7032))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____7040 = desugar_name mk1 setpos env true l  in
              (uu____7040, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____7043 = desugar_name mk1 setpos env true l  in
              (uu____7043, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____7054 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____7054 with
                | FStar_Pervasives_Native.Some uu____7063 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____7068 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____7068 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____7082 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____7099 =
                    let uu____7100 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____7100  in
                  (uu____7099, noaqs)
              | uu____7101 ->
                  let uu____7108 =
                    let uu____7113 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____7113)  in
                  FStar_Errors.raise_error uu____7108
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____7120 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____7120 with
              | FStar_Pervasives_Native.None  ->
                  let uu____7127 =
                    let uu____7132 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____7132)
                     in
                  FStar_Errors.raise_error uu____7127
                    top.FStar_Parser_AST.range
              | uu____7137 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____7141 = desugar_name mk1 setpos env true lid'  in
                  (uu____7141, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____7157 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____7157 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____7176 ->
                       let uu____7183 =
                         FStar_Util.take
                           (fun uu____7207  ->
                              match uu____7207 with
                              | (uu____7212,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____7183 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____7257 =
                              let uu____7282 =
                                FStar_List.map
                                  (fun uu____7325  ->
                                     match uu____7325 with
                                     | (t,imp) ->
                                         let uu____7342 =
                                           desugar_term_aq env t  in
                                         (match uu____7342 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____7282
                                FStar_List.unzip
                               in
                            (match uu____7257 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____7483 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____7483, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____7499 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____7499 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.strcat "Constructor "
                             (Prims.strcat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____7506 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.strcat "Effect "
                             (Prims.strcat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____7517 =
              FStar_List.fold_left
                (fun uu____7562  ->
                   fun b  ->
                     match uu____7562 with
                     | (env1,tparams,typs) ->
                         let uu____7619 = desugar_binder env1 b  in
                         (match uu____7619 with
                          | (xopt,t1) ->
                              let uu____7648 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____7657 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____7657)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____7648 with
                               | (env2,x) ->
                                   let uu____7677 =
                                     let uu____7680 =
                                       let uu____7683 =
                                         let uu____7684 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____7684
                                          in
                                       [uu____7683]  in
                                     FStar_List.append typs uu____7680  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___163_7710 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___163_7710.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___163_7710.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____7677)))) (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      FStar_Pervasives_Native.None])
               in
            (match uu____7517 with
             | (env1,uu____7738,targs) ->
                 let uu____7760 =
                   let uu____7765 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____7765
                    in
                 (match uu____7760 with
                  | (tup,uu____7775) ->
                      let uu____7776 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_app (tup, targs))
                         in
                      (uu____7776, noaqs)))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____7793 = uncurry binders t  in
            (match uu____7793 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___121_7835 =
                   match uu___121_7835 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1  in
                       let uu____7849 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____7849
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____7871 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____7871 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____7904 = aux env [] bs  in (uu____7904, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____7911 = desugar_binder env b  in
            (match uu____7911 with
             | (FStar_Pervasives_Native.None ,uu____7922) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____7936 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____7936 with
                  | ((x,uu____7952),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____7965 =
                        let uu____7966 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____7966  in
                      (uu____7965, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern)
               in
            let uu____7984 =
              FStar_List.fold_left
                (fun uu____8004  ->
                   fun pat  ->
                     match uu____8004 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed
                              (uu____8030,(t,FStar_Pervasives_Native.None ))
                              ->
                              let uu____8040 =
                                let uu____8043 = free_type_vars env1 t  in
                                FStar_List.append uu____8043 ftvs  in
                              (env1, uu____8040)
                          | FStar_Parser_AST.PatAscribed
                              (uu____8048,(t,FStar_Pervasives_Native.Some
                                           tac))
                              ->
                              let uu____8059 =
                                let uu____8062 = free_type_vars env1 t  in
                                let uu____8065 =
                                  let uu____8068 = free_type_vars env1 tac
                                     in
                                  FStar_List.append uu____8068 ftvs  in
                                FStar_List.append uu____8062 uu____8065  in
                              (env1, uu____8059)
                          | uu____8073 -> (env1, ftvs))) (env, []) binders1
               in
            (match uu____7984 with
             | (uu____8082,ftv) ->
                 let ftv1 = sort_ftv ftv  in
                 let binders2 =
                   let uu____8094 =
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
                   FStar_List.append uu____8094 binders1  in
                 let rec aux env1 bs sc_pat_opt uu___122_8149 =
                   match uu___122_8149 with
                   | [] ->
                       let uu____8174 = desugar_term_aq env1 body  in
                       (match uu____8174 with
                        | (body1,aq) ->
                            let body2 =
                              match sc_pat_opt with
                              | FStar_Pervasives_Native.Some (sc,pat) ->
                                  let body2 =
                                    let uu____8211 =
                                      let uu____8212 =
                                        FStar_Syntax_Syntax.pat_bvs pat  in
                                      FStar_All.pipe_right uu____8212
                                        (FStar_List.map
                                           FStar_Syntax_Syntax.mk_binder)
                                       in
                                    FStar_Syntax_Subst.close uu____8211 body1
                                     in
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_match
                                       (sc,
                                         [(pat, FStar_Pervasives_Native.None,
                                            body2)]))
                                    FStar_Pervasives_Native.None
                                    body2.FStar_Syntax_Syntax.pos
                              | FStar_Pervasives_Native.None  -> body1  in
                            let uu____8281 =
                              let uu____8284 =
                                no_annot_abs (FStar_List.rev bs) body2  in
                              setpos uu____8284  in
                            (uu____8281, aq))
                   | p::rest ->
                       let uu____8297 = desugar_binding_pat env1 p  in
                       (match uu____8297 with
                        | (env2,b,pat) ->
                            let pat1 =
                              match pat with
                              | [] -> FStar_Pervasives_Native.None
                              | p1::[] -> FStar_Pervasives_Native.Some p1
                              | uu____8331 ->
                                  FStar_Errors.raise_error
                                    (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                      "Disjunctive patterns are not supported in abstractions")
                                    p.FStar_Parser_AST.prange
                               in
                            let uu____8338 =
                              match b with
                              | LetBinder uu____8375 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat1, sc_pat_opt) with
                                    | (FStar_Pervasives_Native.None
                                       ,uu____8441) -> sc_pat_opt
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.None ) ->
                                        let uu____8495 =
                                          let uu____8502 =
                                            FStar_Syntax_Syntax.bv_to_name x
                                             in
                                          (uu____8502, p1)  in
                                        FStar_Pervasives_Native.Some
                                          uu____8495
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.Some
                                       (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____8558,uu____8559) ->
                                             let tup2 =
                                               let uu____8561 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____8561
                                                 FStar_Syntax_Syntax.delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____8565 =
                                                 let uu____8572 =
                                                   let uu____8573 =
                                                     let uu____8588 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2)
                                                        in
                                                     let uu____8591 =
                                                       let uu____8600 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc
                                                          in
                                                       let uu____8607 =
                                                         let uu____8616 =
                                                           let uu____8623 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x
                                                              in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____8623
                                                            in
                                                         [uu____8616]  in
                                                       uu____8600 ::
                                                         uu____8607
                                                        in
                                                     (uu____8588, uu____8591)
                                                      in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____8573
                                                    in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8572
                                                  in
                                               uu____8565
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Parser_AST.range
                                                in
                                             let p2 =
                                               let uu____8658 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p1, false)]))
                                                 uu____8658
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____8701,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____8703,pats)) ->
                                             let tupn =
                                               let uu____8742 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____8742
                                                 FStar_Syntax_Syntax.delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____8752 =
                                                 let uu____8753 =
                                                   let uu____8768 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn)
                                                      in
                                                   let uu____8771 =
                                                     let uu____8780 =
                                                       let uu____8789 =
                                                         let uu____8796 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____8796
                                                          in
                                                       [uu____8789]  in
                                                     FStar_List.append args
                                                       uu____8780
                                                      in
                                                   (uu____8768, uu____8771)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____8753
                                                  in
                                               mk1 uu____8752  in
                                             let p2 =
                                               let uu____8834 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p1, false)])))
                                                 uu____8834
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | uu____8875 ->
                                             failwith "Impossible")
                                     in
                                  ((x, aq), sc_pat_opt1)
                               in
                            (match uu____8338 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest))
                    in
                 aux env [] FStar_Pervasives_Native.None binders2)
        | FStar_Parser_AST.App
            (uu____8956,uu____8957,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____8979 =
                let uu____8980 = unparen e  in uu____8980.FStar_Parser_AST.tm
                 in
              match uu____8979 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____8990 ->
                  let uu____8991 = desugar_term_aq env e  in
                  (match uu____8991 with
                   | (head1,aq) ->
                       let uu____9004 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____9004, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____9011 ->
            let rec aux args aqs e =
              let uu____9070 =
                let uu____9071 = unparen e  in uu____9071.FStar_Parser_AST.tm
                 in
              match uu____9070 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____9091 = desugar_term_aq env t  in
                  (match uu____9091 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____9127 ->
                  let uu____9128 = desugar_term_aq env e  in
                  (match uu____9128 with
                   | (head1,aq) ->
                       let uu____9151 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____9151, (join_aqs (aq :: aqs))))
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
            let uu____9203 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____9203
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
            let uu____9255 = desugar_term_aq env t  in
            (match uu____9255 with
             | (tm,s) ->
                 let uu____9266 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____9266, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____9272 =
              let uu____9285 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____9285 then desugar_typ_aq else desugar_term_aq  in
            uu____9272 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____9340 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____9483  ->
                        match uu____9483 with
                        | (attr_opt,(p,def)) ->
                            let uu____9541 = is_app_pattern p  in
                            if uu____9541
                            then
                              let uu____9572 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____9572, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____9654 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____9654, def1)
                               | uu____9699 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____9737);
                                           FStar_Parser_AST.prange =
                                             uu____9738;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____9786 =
                                            let uu____9807 =
                                              let uu____9812 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____9812  in
                                            (uu____9807, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____9786, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____9903) ->
                                        if top_level
                                        then
                                          let uu____9938 =
                                            let uu____9959 =
                                              let uu____9964 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____9964  in
                                            (uu____9959, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____9938, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____10054 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____10085 =
                FStar_List.fold_left
                  (fun uu____10158  ->
                     fun uu____10159  ->
                       match (uu____10158, uu____10159) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____10267,uu____10268),uu____10269))
                           ->
                           let uu____10386 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____10412 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____10412 with
                                  | (env2,xx) ->
                                      let uu____10431 =
                                        let uu____10434 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____10434 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____10431))
                             | FStar_Util.Inr l ->
                                 let uu____10442 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (uu____10442, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____10386 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____10085 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____10590 =
                    match uu____10590 with
                    | (attrs_opt,(uu____10626,args,result_t),def) ->
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
                                let uu____10714 = is_comp_type env1 t  in
                                if uu____10714
                                then
                                  ((let uu____10716 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____10726 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____10726))
                                       in
                                    match uu____10716 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____10729 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____10731 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____10731))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____10729
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t)
                                 in
                              let uu____10736 =
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range
                                 in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed (def, t1, tacopt))
                                uu____10736 FStar_Parser_AST.Expr
                           in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____10740 ->
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
                              let uu____10755 =
                                let uu____10756 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____10756
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____10755
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
                  let uu____10831 = desugar_term_aq env' body  in
                  (match uu____10831 with
                   | (body1,aq) ->
                       let uu____10844 =
                         let uu____10847 =
                           let uu____10848 =
                             let uu____10861 =
                               FStar_Syntax_Subst.close rec_bindings1 body1
                                in
                             ((is_rec, lbs1), uu____10861)  in
                           FStar_Syntax_Syntax.Tm_let uu____10848  in
                         FStar_All.pipe_left mk1 uu____10847  in
                       (uu____10844, aq))
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
              let uu____10939 =
                desugar_binding_pat_maybe_top top_level env pat is_mutable
                 in
              match uu____10939 with
              | (env1,binder,pat1) ->
                  let uu____10961 =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let uu____10987 = desugar_term_aq env1 t2  in
                        (match uu____10987 with
                         | (body1,aq) ->
                             let fv =
                               let uu____11001 =
                                 FStar_Syntax_Util.incr_delta_qualifier t12
                                  in
                               FStar_Syntax_Syntax.lid_as_fv l uu____11001
                                 FStar_Pervasives_Native.None
                                in
                             let uu____11002 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t12,
                                            (t12.FStar_Syntax_Syntax.pos))]),
                                      body1))
                                in
                             (uu____11002, aq))
                    | LocalBinder (x,uu____11032) ->
                        let uu____11033 = desugar_term_aq env1 t2  in
                        (match uu____11033 with
                         | (body1,aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | {
                                   FStar_Syntax_Syntax.v =
                                     FStar_Syntax_Syntax.Pat_wild uu____11047;
                                   FStar_Syntax_Syntax.p = uu____11048;_}::[]
                                   -> body1
                               | uu____11049 ->
                                   let uu____11052 =
                                     let uu____11059 =
                                       let uu____11060 =
                                         let uu____11083 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         let uu____11086 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1
                                            in
                                         (uu____11083, uu____11086)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____11060
                                        in
                                     FStar_Syntax_Syntax.mk uu____11059  in
                                   uu____11052 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range
                                in
                             let uu____11126 =
                               let uu____11129 =
                                 let uu____11130 =
                                   let uu____11143 =
                                     let uu____11146 =
                                       let uu____11147 =
                                         FStar_Syntax_Syntax.mk_binder x  in
                                       [uu____11147]  in
                                     FStar_Syntax_Subst.close uu____11146
                                       body2
                                      in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t12,
                                           (t12.FStar_Syntax_Syntax.pos))]),
                                     uu____11143)
                                    in
                                 FStar_Syntax_Syntax.Tm_let uu____11130  in
                               FStar_All.pipe_left mk1 uu____11129  in
                             (uu____11126, aq))
                     in
                  (match uu____10961 with
                   | (tm,aq) ->
                       if is_mutable
                       then
                         let uu____11204 =
                           FStar_All.pipe_left mk1
                             (FStar_Syntax_Syntax.Tm_meta
                                (tm,
                                  (FStar_Syntax_Syntax.Meta_desugared
                                     FStar_Syntax_Syntax.Mutable_alloc)))
                            in
                         (uu____11204, aq)
                       else (tm, aq))
               in
            let uu____11216 = FStar_List.hd lbs  in
            (match uu____11216 with
             | (attrs,(head_pat,defn)) ->
                 let uu____11260 = is_rec || (is_app_pattern head_pat)  in
                 if uu____11260
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____11273 =
                let uu____11274 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____11274  in
              mk1 uu____11273  in
            let uu____11275 = desugar_term_aq env t1  in
            (match uu____11275 with
             | (t1',aq1) ->
                 let uu____11286 = desugar_term_aq env t2  in
                 (match uu____11286 with
                  | (t2',aq2) ->
                      let uu____11297 = desugar_term_aq env t3  in
                      (match uu____11297 with
                       | (t3',aq3) ->
                           let uu____11308 =
                             let uu____11309 =
                               let uu____11310 =
                                 let uu____11333 =
                                   let uu____11350 =
                                     let uu____11365 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t2.FStar_Parser_AST.range
                                        in
                                     (uu____11365,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____11378 =
                                     let uu____11395 =
                                       let uu____11410 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t3.FStar_Parser_AST.range
                                          in
                                       (uu____11410,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____11395]  in
                                   uu____11350 :: uu____11378  in
                                 (t1', uu____11333)  in
                               FStar_Syntax_Syntax.Tm_match uu____11310  in
                             mk1 uu____11309  in
                           (uu____11308, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____11609 =
              match uu____11609 with
              | (pat,wopt,b) ->
                  let uu____11631 = desugar_match_pat env pat  in
                  (match uu____11631 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____11662 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____11662
                          in
                       let uu____11663 = desugar_term_aq env1 b  in
                       (match uu____11663 with
                        | (b1,aq) ->
                            let uu____11676 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____11676, aq)))
               in
            let uu____11681 = desugar_term_aq env e  in
            (match uu____11681 with
             | (e1,aq) ->
                 let uu____11692 =
                   let uu____11715 =
                     let uu____11740 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____11740 FStar_List.unzip  in
                   FStar_All.pipe_right uu____11715
                     (fun uu____11846  ->
                        match uu____11846 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____11692 with
                  | (brs,aqs) ->
                      let uu____12009 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____12009, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____12054 = is_comp_type env t  in
              if uu____12054
              then
                let uu____12063 = desugar_comp t.FStar_Parser_AST.range env t
                   in
                FStar_Util.Inr uu____12063
              else
                (let uu____12071 = desugar_term env t  in
                 FStar_Util.Inl uu____12071)
               in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)  in
            let uu____12081 = desugar_term_aq env e  in
            (match uu____12081 with
             | (e1,aq) ->
                 let uu____12092 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_ascribed
                        (e1, (annot, tac_opt1), FStar_Pervasives_Native.None))
                    in
                 (uu____12092, aq))
        | FStar_Parser_AST.Record (uu____12125,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____12166 = FStar_List.hd fields  in
              match uu____12166 with | (f,uu____12178) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____12224  ->
                        match uu____12224 with
                        | (g,uu____12230) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____12236,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____12250 =
                         let uu____12255 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____12255)
                          in
                       FStar_Errors.raise_error uu____12250
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
                  let uu____12263 =
                    let uu____12274 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____12305  ->
                              match uu____12305 with
                              | (f,uu____12315) ->
                                  let uu____12316 =
                                    let uu____12317 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____12317
                                     in
                                  (uu____12316, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____12274)  in
                  FStar_Parser_AST.Construct uu____12263
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____12335 =
                      let uu____12336 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____12336  in
                    FStar_Parser_AST.mk_term uu____12335
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____12338 =
                      let uu____12351 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____12381  ->
                                match uu____12381 with
                                | (f,uu____12391) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____12351)  in
                    FStar_Parser_AST.Record uu____12338  in
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
            let uu____12451 = desugar_term_aq env recterm1  in
            (match uu____12451 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____12467;
                         FStar_Syntax_Syntax.vars = uu____12468;_},args)
                      ->
                      let uu____12490 =
                        let uu____12491 =
                          let uu____12492 =
                            let uu____12507 =
                              let uu____12510 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____12511 =
                                let uu____12514 =
                                  let uu____12515 =
                                    let uu____12522 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____12522)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____12515
                                   in
                                FStar_Pervasives_Native.Some uu____12514  in
                              FStar_Syntax_Syntax.fvar uu____12510
                                FStar_Syntax_Syntax.delta_constant
                                uu____12511
                               in
                            (uu____12507, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____12492  in
                        FStar_All.pipe_left mk1 uu____12491  in
                      (uu____12490, s)
                  | uu____12549 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____12553 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____12553 with
              | (constrname,is_rec) ->
                  let uu____12568 = desugar_term_aq env e  in
                  (match uu____12568 with
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
                       let uu____12586 =
                         let uu____12587 =
                           let uu____12588 =
                             let uu____12603 =
                               let uu____12606 =
                                 let uu____12607 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____12607
                                  in
                               FStar_Syntax_Syntax.fvar uu____12606
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1")) qual
                                in
                             let uu____12608 =
                               let uu____12617 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____12617]  in
                             (uu____12603, uu____12608)  in
                           FStar_Syntax_Syntax.Tm_app uu____12588  in
                         FStar_All.pipe_left mk1 uu____12587  in
                       (uu____12586, s))))
        | FStar_Parser_AST.NamedTyp (uu____12646,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____12655 =
              let uu____12656 = FStar_Syntax_Subst.compress tm  in
              uu____12656.FStar_Syntax_Syntax.n  in
            (match uu____12655 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____12664 =
                   let uu___164_12665 =
                     let uu____12666 =
                       let uu____12667 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____12667  in
                     FStar_Syntax_Util.exp_string uu____12666  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___164_12665.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___164_12665.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____12664, noaqs)
             | uu____12668 ->
                 let uu____12669 =
                   let uu____12674 =
                     let uu____12675 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.strcat "VQuote, expected an fvar, got: "
                       uu____12675
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____12674)  in
                 FStar_Errors.raise_error uu____12669
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____12681 = desugar_term_aq env e  in
            (match uu____12681 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____12693 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____12693, noaqs))
        | FStar_Parser_AST.Antiquote (b,e) ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____12699 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____12700 =
              let uu____12701 =
                let uu____12710 = desugar_term env e  in (bv, b, uu____12710)
                 in
              [uu____12701]  in
            (uu____12699, uu____12700)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____12741 =
              let uu____12742 =
                let uu____12743 =
                  let uu____12750 = desugar_term env e  in (uu____12750, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____12743  in
              FStar_All.pipe_left mk1 uu____12742  in
            (uu____12741, noaqs)
        | uu____12755 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____12756 = desugar_formula env top  in
            (uu____12756, noaqs)
        | uu____12757 ->
            let uu____12758 =
              let uu____12763 =
                let uu____12764 = FStar_Parser_AST.term_to_string top  in
                Prims.strcat "Unexpected term: " uu____12764  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____12763)  in
            FStar_Errors.raise_error uu____12758 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____12770 -> false
    | uu____12779 -> true

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
           (fun uu____12816  ->
              match uu____12816 with
              | (a,imp) ->
                  let uu____12829 = desugar_term env a  in
                  arg_withimp_e imp uu____12829))

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
        let is_requires uu____12861 =
          match uu____12861 with
          | (t1,uu____12867) ->
              let uu____12868 =
                let uu____12869 = unparen t1  in
                uu____12869.FStar_Parser_AST.tm  in
              (match uu____12868 with
               | FStar_Parser_AST.Requires uu____12870 -> true
               | uu____12877 -> false)
           in
        let is_ensures uu____12887 =
          match uu____12887 with
          | (t1,uu____12893) ->
              let uu____12894 =
                let uu____12895 = unparen t1  in
                uu____12895.FStar_Parser_AST.tm  in
              (match uu____12894 with
               | FStar_Parser_AST.Ensures uu____12896 -> true
               | uu____12903 -> false)
           in
        let is_app head1 uu____12918 =
          match uu____12918 with
          | (t1,uu____12924) ->
              let uu____12925 =
                let uu____12926 = unparen t1  in
                uu____12926.FStar_Parser_AST.tm  in
              (match uu____12925 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____12928;
                      FStar_Parser_AST.level = uu____12929;_},uu____12930,uu____12931)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____12932 -> false)
           in
        let is_smt_pat uu____12942 =
          match uu____12942 with
          | (t1,uu____12948) ->
              let uu____12949 =
                let uu____12950 = unparen t1  in
                uu____12950.FStar_Parser_AST.tm  in
              (match uu____12949 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____12953);
                             FStar_Parser_AST.range = uu____12954;
                             FStar_Parser_AST.level = uu____12955;_},uu____12956)::uu____12957::[])
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
                             FStar_Parser_AST.range = uu____12996;
                             FStar_Parser_AST.level = uu____12997;_},uu____12998)::uu____12999::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
               | uu____13024 -> false)
           in
        let is_decreases = is_app "decreases"  in
        let pre_process_comp_typ t1 =
          let uu____13056 = head_and_args t1  in
          match uu____13056 with
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
                   let thunk_ens uu____13154 =
                     match uu____13154 with
                     | (e,i) ->
                         let uu____13165 = thunk_ens_ e  in (uu____13165, i)
                      in
                   let fail_lemma uu____13177 =
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
                         let uu____13257 =
                           let uu____13264 =
                             let uu____13271 = thunk_ens ens  in
                             [uu____13271; nil_pat]  in
                           req_true :: uu____13264  in
                         unit_tm :: uu____13257
                     | req::ens::[] when
                         (is_requires req) && (is_ensures ens) ->
                         let uu____13318 =
                           let uu____13325 =
                             let uu____13332 = thunk_ens ens  in
                             [uu____13332; nil_pat]  in
                           req :: uu____13325  in
                         unit_tm :: uu____13318
                     | ens::smtpat::[] when
                         (((let uu____13381 = is_requires ens  in
                            Prims.op_Negation uu____13381) &&
                             (let uu____13383 = is_smt_pat ens  in
                              Prims.op_Negation uu____13383))
                            &&
                            (let uu____13385 = is_decreases ens  in
                             Prims.op_Negation uu____13385))
                           && (is_smt_pat smtpat)
                         ->
                         let uu____13386 =
                           let uu____13393 =
                             let uu____13400 = thunk_ens ens  in
                             [uu____13400; smtpat]  in
                           req_true :: uu____13393  in
                         unit_tm :: uu____13386
                     | ens::dec::[] when
                         (is_ensures ens) && (is_decreases dec) ->
                         let uu____13447 =
                           let uu____13454 =
                             let uu____13461 = thunk_ens ens  in
                             [uu____13461; nil_pat; dec]  in
                           req_true :: uu____13454  in
                         unit_tm :: uu____13447
                     | ens::dec::smtpat::[] when
                         ((is_ensures ens) && (is_decreases dec)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____13521 =
                           let uu____13528 =
                             let uu____13535 = thunk_ens ens  in
                             [uu____13535; smtpat; dec]  in
                           req_true :: uu____13528  in
                         unit_tm :: uu____13521
                     | req::ens::dec::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_decreases dec)
                         ->
                         let uu____13595 =
                           let uu____13602 =
                             let uu____13609 = thunk_ens ens  in
                             [uu____13609; nil_pat; dec]  in
                           req :: uu____13602  in
                         unit_tm :: uu____13595
                     | req::ens::smtpat::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____13669 =
                           let uu____13676 =
                             let uu____13683 = thunk_ens ens  in
                             [uu____13683; smtpat]  in
                           req :: uu____13676  in
                         unit_tm :: uu____13669
                     | req::ens::dec::smtpat::[] when
                         (((is_requires req) && (is_ensures ens)) &&
                            (is_smt_pat smtpat))
                           && (is_decreases dec)
                         ->
                         let uu____13748 =
                           let uu____13755 =
                             let uu____13762 = thunk_ens ens  in
                             [uu____13762; dec; smtpat]  in
                           req :: uu____13755  in
                         unit_tm :: uu____13748
                     | _other -> fail_lemma ()  in
                   let head_and_attributes =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) lemma
                      in
                   (head_and_attributes, args1)
               | FStar_Parser_AST.Name l when
                   FStar_Syntax_DsEnv.is_effect_name env l ->
                   let uu____13824 =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) l
                      in
                   (uu____13824, args)
               | FStar_Parser_AST.Name l when
                   (let uu____13852 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____13852
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   let uu____13853 =
                     let uu____13860 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_Tot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____13860, [])  in
                   (uu____13853, args)
               | FStar_Parser_AST.Name l when
                   (let uu____13878 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____13878
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                   ->
                   let uu____13879 =
                     let uu____13886 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_GTot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____13886, [])  in
                   (uu____13879, args)
               | FStar_Parser_AST.Name l when
                   (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                      ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                     || ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                   ->
                   let uu____13902 =
                     let uu____13909 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_Tot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____13909, [])  in
                   (uu____13902, [(t1, FStar_Parser_AST.Nothing)])
               | uu____13932 ->
                   let default_effect =
                     let uu____13934 = FStar_Options.ml_ish ()  in
                     if uu____13934
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____13937 =
                           FStar_Options.warn_default_effects ()  in
                         if uu____13937
                         then
                           FStar_Errors.log_issue
                             head1.FStar_Parser_AST.range
                             (FStar_Errors.Warning_UseDefaultEffect,
                               "Using default effect Tot")
                         else ());
                        FStar_Parser_Const.effect_Tot_lid)
                      in
                   let uu____13939 =
                     let uu____13946 =
                       FStar_Ident.set_lid_range default_effect
                         head1.FStar_Parser_AST.range
                        in
                     (uu____13946, [])  in
                   (uu____13939, [(t1, FStar_Parser_AST.Nothing)]))
           in
        let uu____13969 = pre_process_comp_typ t  in
        match uu____13969 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____14019 =
                  let uu____14024 =
                    let uu____14025 = FStar_Syntax_Print.lid_to_string eff
                       in
                    FStar_Util.format1 "Not enough args to effect %s"
                      uu____14025
                     in
                  (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____14024)  in
                fail1 uu____14019)
             else ();
             (let is_universe uu____14036 =
                match uu____14036 with
                | (uu____14041,imp) -> imp = FStar_Parser_AST.UnivApp  in
              let uu____14043 = FStar_Util.take is_universe args  in
              match uu____14043 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____14102  ->
                         match uu____14102 with
                         | (u,imp) -> desugar_universe u) universes
                     in
                  let uu____14109 =
                    let uu____14124 = FStar_List.hd args1  in
                    let uu____14133 = FStar_List.tl args1  in
                    (uu____14124, uu____14133)  in
                  (match uu____14109 with
                   | (result_arg,rest) ->
                       let result_typ =
                         desugar_typ env
                           (FStar_Pervasives_Native.fst result_arg)
                          in
                       let rest1 = desugar_args env rest  in
                       let uu____14188 =
                         let is_decrease uu____14226 =
                           match uu____14226 with
                           | (t1,uu____14236) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.pos = uu____14246;
                                       FStar_Syntax_Syntax.vars = uu____14247;_},uu____14248::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.decreases_lid
                                | uu____14279 -> false)
                            in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease)
                          in
                       (match uu____14188 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____14395  ->
                                      match uu____14395 with
                                      | (t1,uu____14405) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____14414,(arg,uu____14416)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____14445 -> failwith "impos")))
                               in
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
                                | uu____14462 -> false  in
                              (((is_empty decreases_clause) &&
                                  (is_empty rest2))
                                 && (is_empty cattributes))
                                && (is_empty universes1)
                               in
                            let uu____14473 =
                              no_additional_args &&
                                (FStar_Ident.lid_equals eff
                                   FStar_Parser_Const.effect_Tot_lid)
                               in
                            if uu____14473
                            then FStar_Syntax_Syntax.mk_Total result_typ
                            else
                              (let uu____14477 =
                                 no_additional_args &&
                                   (FStar_Ident.lid_equals eff
                                      FStar_Parser_Const.effect_GTot_lid)
                                  in
                               if uu____14477
                               then FStar_Syntax_Syntax.mk_GTotal result_typ
                               else
                                 (let flags1 =
                                    let uu____14484 =
                                      FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_Lemma_lid
                                       in
                                    if uu____14484
                                    then [FStar_Syntax_Syntax.LEMMA]
                                    else
                                      (let uu____14488 =
                                         FStar_Ident.lid_equals eff
                                           FStar_Parser_Const.effect_Tot_lid
                                          in
                                       if uu____14488
                                       then [FStar_Syntax_Syntax.TOTAL]
                                       else
                                         (let uu____14492 =
                                            FStar_Ident.lid_equals eff
                                              FStar_Parser_Const.effect_ML_lid
                                             in
                                          if uu____14492
                                          then [FStar_Syntax_Syntax.MLEFFECT]
                                          else
                                            (let uu____14496 =
                                               FStar_Ident.lid_equals eff
                                                 FStar_Parser_Const.effect_GTot_lid
                                                in
                                             if uu____14496
                                             then
                                               [FStar_Syntax_Syntax.SOMETRIVIAL]
                                             else [])))
                                     in
                                  let flags2 =
                                    FStar_List.append flags1 cattributes  in
                                  let rest3 =
                                    let uu____14512 =
                                      FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_Lemma_lid
                                       in
                                    if uu____14512
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
                                                  let uu____14597 =
                                                    FStar_Ident.set_lid_range
                                                      FStar_Parser_Const.pattern_lid
                                                      pat.FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_Syntax.fvar
                                                    uu____14597
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
                                            | uu____14612 -> pat  in
                                          let uu____14613 =
                                            let uu____14624 =
                                              let uu____14635 =
                                                let uu____14644 =
                                                  FStar_Syntax_Syntax.mk
                                                    (FStar_Syntax_Syntax.Tm_meta
                                                       (pat1,
                                                         (FStar_Syntax_Syntax.Meta_desugared
                                                            FStar_Syntax_Syntax.Meta_smt_pat)))
                                                    FStar_Pervasives_Native.None
                                                    pat1.FStar_Syntax_Syntax.pos
                                                   in
                                                (uu____14644, aq)  in
                                              [uu____14635]  in
                                            ens :: uu____14624  in
                                          req :: uu____14613
                                      | uu____14685 -> rest2
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
        | uu____14709 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___165_14730 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___165_14730.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___165_14730.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___166_14772 = b  in
             {
               FStar_Parser_AST.b = (uu___166_14772.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___166_14772.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___166_14772.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____14835 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____14835)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____14848 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____14848 with
             | (env1,a1) ->
                 let a2 =
                   let uu___167_14858 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___167_14858.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___167_14858.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____14884 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____14898 =
                     let uu____14901 =
                       let uu____14902 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____14902]  in
                     no_annot_abs uu____14901 body2  in
                   FStar_All.pipe_left setpos uu____14898  in
                 let uu____14917 =
                   let uu____14918 =
                     let uu____14933 =
                       let uu____14936 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____14936
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____14937 =
                       let uu____14946 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____14946]  in
                     (uu____14933, uu____14937)  in
                   FStar_Syntax_Syntax.Tm_app uu____14918  in
                 FStar_All.pipe_left mk1 uu____14917)
        | uu____14977 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____15057 = q (rest, pats, body)  in
              let uu____15064 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____15057 uu____15064
                FStar_Parser_AST.Formula
               in
            let uu____15065 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____15065 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____15074 -> failwith "impossible"  in
      let uu____15077 =
        let uu____15078 = unparen f  in uu____15078.FStar_Parser_AST.tm  in
      match uu____15077 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____15085,uu____15086) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____15097,uu____15098) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____15129 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____15129
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____15165 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____15165
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____15208 -> desugar_term env f

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
      let uu____15213 =
        FStar_List.fold_left
          (fun uu____15249  ->
             fun b  ->
               match uu____15249 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___168_15301 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___168_15301.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___168_15301.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___168_15301.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____15318 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____15318 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___169_15338 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___169_15338.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___169_15338.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____15355 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____15213 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

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
          let uu____15442 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____15442)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____15447 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____15447)
      | FStar_Parser_AST.TVariable x ->
          let uu____15451 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____15451)
      | FStar_Parser_AST.NoName t ->
          let uu____15455 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____15455)
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
               (fun uu___123_15494  ->
                  match uu___123_15494 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____15495 -> false))
           in
        let quals2 q =
          let uu____15508 =
            (let uu____15511 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____15511) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____15508
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____15525 = FStar_Ident.range_of_lid disc_name  in
                let uu____15526 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____15525;
                  FStar_Syntax_Syntax.sigquals = uu____15526;
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
            let uu____15565 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____15599  ->
                        match uu____15599 with
                        | (x,uu____15607) ->
                            let uu____15608 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____15608 with
                             | (field_name,uu____15616) ->
                                 let only_decl =
                                   ((let uu____15620 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____15620)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____15622 =
                                        let uu____15623 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____15623.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____15622)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____15639 =
                                       FStar_List.filter
                                         (fun uu___124_15643  ->
                                            match uu___124_15643 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____15644 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____15639
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___125_15657  ->
                                             match uu___125_15657 with
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____15658 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____15660 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____15660;
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____15665 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____15665
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          (FStar_Syntax_Syntax.Delta_equational_at_level
                                             (Prims.parse_int "1"))
                                      else
                                        FStar_Syntax_Syntax.Delta_equational_at_level
                                          (Prims.parse_int "1")
                                       in
                                    let lb =
                                      let uu____15670 =
                                        let uu____15675 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____15675  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____15670;
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
                                      let uu____15679 =
                                        let uu____15680 =
                                          let uu____15687 =
                                            let uu____15690 =
                                              let uu____15691 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____15691
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____15690]  in
                                          ((false, [lb]), uu____15687)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____15680
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____15679;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____15565 FStar_List.flatten
  
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
            (lid,uu____15735,t,uu____15737,n1,uu____15739) when
            let uu____15744 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____15744 ->
            let uu____15745 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____15745 with
             | (formals,uu____15761) ->
                 (match formals with
                  | [] -> []
                  | uu____15784 ->
                      let filter_records uu___126_15798 =
                        match uu___126_15798 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____15801,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____15813 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____15815 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____15815 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Syntax_Syntax.Data_ctor
                        | FStar_Pervasives_Native.Some q -> q  in
                      let iquals1 =
                        if
                          FStar_List.contains FStar_Syntax_Syntax.Abstract
                            iquals
                        then FStar_Syntax_Syntax.Private :: iquals
                        else iquals  in
                      let uu____15825 = FStar_Util.first_N n1 formals  in
                      (match uu____15825 with
                       | (uu____15848,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____15874 -> []
  
let (mk_typ_abbrev :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.typ ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
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
                    let uu____15944 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____15944
                    then
                      let uu____15947 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____15947
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____15950 =
                      let uu____15955 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____15955  in
                    let uu____15956 =
                      let uu____15959 = FStar_Syntax_Syntax.mk_Total k  in
                      FStar_Syntax_Util.arrow typars uu____15959  in
                    let uu____15962 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____15950;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____15956;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____15962;
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
          let tycon_id uu___127_16013 =
            match uu___127_16013 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____16015,uu____16016) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____16026,uu____16027,uu____16028) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____16038,uu____16039,uu____16040) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____16070,uu____16071,uu____16072) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____16116) ->
                let uu____16117 =
                  let uu____16118 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____16118  in
                FStar_Parser_AST.mk_term uu____16117 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____16120 =
                  let uu____16121 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____16121  in
                FStar_Parser_AST.mk_term uu____16120 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____16123) ->
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
              | uu____16154 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____16160 =
                     let uu____16161 =
                       let uu____16168 = binder_to_term b  in
                       (out, uu____16168, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____16161  in
                   FStar_Parser_AST.mk_term uu____16160
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___128_16180 =
            match uu___128_16180 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____16236  ->
                       match uu____16236 with
                       | (x,t,uu____16247) ->
                           let uu____16252 =
                             let uu____16253 =
                               let uu____16258 =
                                 FStar_Syntax_Util.mangle_field_name x  in
                               (uu____16258, t)  in
                             FStar_Parser_AST.Annotated uu____16253  in
                           FStar_Parser_AST.mk_binder uu____16252
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____16260 =
                    let uu____16261 =
                      let uu____16262 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____16262  in
                    FStar_Parser_AST.mk_term uu____16261
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____16260 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let uu____16266 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____16293  ->
                          match uu____16293 with
                          | (x,uu____16303,uu____16304) ->
                              FStar_Syntax_Util.unmangle_field_name x))
                   in
                ((FStar_Parser_AST.TyconVariant
                    (id1, parms, kopt,
                      [(constrName, (FStar_Pervasives_Native.Some constrTyp),
                         FStar_Pervasives_Native.None, false)])),
                  uu____16266)
            | uu____16357 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___129_16396 =
            match uu___129_16396 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____16420 = typars_of_binders _env binders  in
                (match uu____16420 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____16462 =
                         let uu____16463 =
                           let uu____16464 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____16464  in
                         FStar_Parser_AST.mk_term uu____16463
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____16462 binders  in
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
            | uu____16475 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____16523 =
              FStar_List.fold_left
                (fun uu____16563  ->
                   fun uu____16564  ->
                     match (uu____16563, uu____16564) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____16655 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____16655 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____16523 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____16768 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____16768
                | uu____16769 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____16777 = desugar_abstract_tc quals env [] tc  in
              (match uu____16777 with
               | (uu____16790,uu____16791,se,uu____16793) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____16796,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____16813 =
                                 let uu____16814 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____16814  in
                               if uu____16813
                               then
                                 let uu____16815 =
                                   let uu____16820 =
                                     let uu____16821 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____16821
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____16820)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____16815
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
                           | uu____16828 ->
                               let uu____16829 =
                                 let uu____16836 =
                                   let uu____16837 =
                                     let uu____16850 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____16850)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____16837
                                    in
                                 FStar_Syntax_Syntax.mk uu____16836  in
                               uu____16829 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___170_16864 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___170_16864.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___170_16864.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___170_16864.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____16865 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____16868 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____16868
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____16881 = typars_of_binders env binders  in
              (match uu____16881 with
               | (env',typars) ->
                   let k =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____16917 =
                           FStar_Util.for_some
                             (fun uu___130_16919  ->
                                match uu___130_16919 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____16920 -> false) quals
                            in
                         if uu____16917
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Util.ktype
                     | FStar_Pervasives_Native.Some k -> desugar_term env' k
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____16927 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___131_16931  ->
                               match uu___131_16931 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____16932 -> false))
                        in
                     if uu____16927
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____16941 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____16941
                     then
                       let uu____16944 =
                         let uu____16951 =
                           let uu____16952 = unparen t  in
                           uu____16952.FStar_Parser_AST.tm  in
                         match uu____16951 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____16973 =
                               match FStar_List.rev args with
                               | (last_arg,uu____17003)::args_rev ->
                                   let uu____17015 =
                                     let uu____17016 = unparen last_arg  in
                                     uu____17016.FStar_Parser_AST.tm  in
                                   (match uu____17015 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____17044 -> ([], args))
                               | uu____17053 -> ([], args)  in
                             (match uu____16973 with
                              | (cattributes,args1) ->
                                  let uu____17092 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____17092))
                         | uu____17103 -> (t, [])  in
                       match uu____16944 with
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
                                  (fun uu___132_17125  ->
                                     match uu___132_17125 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____17126 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____17133)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____17157 = tycon_record_as_variant trec  in
              (match uu____17157 with
               | (t,fs) ->
                   let uu____17174 =
                     let uu____17177 =
                       let uu____17178 =
                         let uu____17187 =
                           let uu____17190 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____17190  in
                         (uu____17187, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____17178  in
                     uu____17177 :: quals  in
                   desugar_tycon env d uu____17174 [t])
          | uu____17195::uu____17196 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____17363 = et  in
                match uu____17363 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____17588 ->
                         let trec = tc  in
                         let uu____17612 = tycon_record_as_variant trec  in
                         (match uu____17612 with
                          | (t,fs) ->
                              let uu____17671 =
                                let uu____17674 =
                                  let uu____17675 =
                                    let uu____17684 =
                                      let uu____17687 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____17687  in
                                    (uu____17684, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____17675
                                   in
                                uu____17674 :: quals1  in
                              collect_tcs uu____17671 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____17774 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____17774 with
                          | (env2,uu____17834,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____17983 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____17983 with
                          | (env2,uu____18043,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____18168 ->
                         failwith "Unrecognized mutual type definition")
                 in
              let uu____18215 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____18215 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___134_18726  ->
                             match uu___134_18726 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____18793,uu____18794);
                                    FStar_Syntax_Syntax.sigrng = uu____18795;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____18796;
                                    FStar_Syntax_Syntax.sigmeta = uu____18797;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____18798;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____18859 =
                                     typars_of_binders env1 binders  in
                                   match uu____18859 with
                                   | (env2,tpars1) ->
                                       let uu____18890 =
                                         push_tparams env2 tpars1  in
                                       (match uu____18890 with
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
                                 let uu____18923 =
                                   let uu____18944 =
                                     mk_typ_abbrev id1 uvs tpars k t1 
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____18944)
                                    in
                                 [uu____18923]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____19012);
                                    FStar_Syntax_Syntax.sigrng = uu____19013;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____19015;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____19016;_},constrs,tconstr,quals1)
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
                                 let uu____19114 = push_tparams env1 tpars
                                    in
                                 (match uu____19114 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____19191  ->
                                             match uu____19191 with
                                             | (x,uu____19205) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____19213 =
                                        let uu____19242 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____19356  ->
                                                  match uu____19356 with
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
                                                        let uu____19412 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____19412
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
                                                                uu___133_19423
                                                                 ->
                                                                match uu___133_19423
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____19435
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____19443 =
                                                        let uu____19464 =
                                                          let uu____19465 =
                                                            let uu____19466 =
                                                              let uu____19481
                                                                =
                                                                let uu____19482
                                                                  =
                                                                  let uu____19485
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____19485
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____19482
                                                                 in
                                                              (name, univs1,
                                                                uu____19481,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____19466
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____19465;
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
                                                          uu____19464)
                                                         in
                                                      (name, uu____19443)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____19242
                                         in
                                      (match uu____19213 with
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
                             | uu____19722 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____19854  ->
                             match uu____19854 with
                             | (name_doc,uu____19882,uu____19883) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____19963  ->
                             match uu____19963 with
                             | (uu____19984,uu____19985,se) -> se))
                      in
                   let uu____20015 =
                     let uu____20022 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____20022 rng
                      in
                   (match uu____20015 with
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
                               (fun uu____20088  ->
                                  match uu____20088 with
                                  | (uu____20111,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____20162,tps,k,uu____20165,constrs)
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
                                  | uu____20184 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____20201  ->
                                 match uu____20201 with
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
      let uu____20244 =
        FStar_List.fold_left
          (fun uu____20279  ->
             fun b  ->
               match uu____20279 with
               | (env1,binders1) ->
                   let uu____20323 = desugar_binder env1 b  in
                   (match uu____20323 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____20346 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____20346 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____20401 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____20244 with
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
          let uu____20502 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___135_20507  ->
                    match uu___135_20507 with
                    | FStar_Syntax_Syntax.Reflectable uu____20508 -> true
                    | uu____20509 -> false))
             in
          if uu____20502
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____20512 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____20512
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
      let uu____20544 = FStar_Syntax_Util.head_and_args at1  in
      match uu____20544 with
      | (hd1,args) ->
          let uu____20589 =
            let uu____20602 =
              let uu____20603 = FStar_Syntax_Subst.compress hd1  in
              uu____20603.FStar_Syntax_Syntax.n  in
            (uu____20602, args)  in
          (match uu____20589 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(a1,uu____20624)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr
               ->
               let uu____20649 =
                 let uu____20654 =
                   FStar_Syntax_Embeddings.e_list
                     FStar_Syntax_Embeddings.e_int
                    in
                 FStar_Syntax_Embeddings.unembed uu____20654 a1  in
               (match uu____20649 with
                | FStar_Pervasives_Native.Some [] ->
                    FStar_Errors.raise_error
                      (FStar_Errors.Error_EmptyFailErrs,
                        "Found ill-applied fail, argument should be a non-empty list of integers")
                      at1.FStar_Syntax_Syntax.pos
                | FStar_Pervasives_Native.Some es ->
                    let uu____20684 =
                      let uu____20691 =
                        FStar_List.map FStar_BigInt.to_int_fs es  in
                      (uu____20691, false)  in
                    FStar_Pervasives_Native.Some uu____20684
                | FStar_Pervasives_Native.None  ->
                    (if warn
                     then
                       FStar_Errors.log_issue at1.FStar_Syntax_Syntax.pos
                         (FStar_Errors.Warning_UnappliedFail,
                           "Found ill-applied fail, argument should be a non-empty list of integer literals")
                     else ();
                     FStar_Pervasives_Native.None))
           | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr
               -> FStar_Pervasives_Native.Some ([], false)
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____20736) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr
               ->
               (if warn
                then
                  FStar_Errors.log_issue at1.FStar_Syntax_Syntax.pos
                    (FStar_Errors.Warning_UnappliedFail,
                      "Found ill-applied fail, argument should be a non-empty list of integer literals")
                else ();
                FStar_Pervasives_Native.None)
           | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.fail_lax_attr
               -> FStar_Pervasives_Native.Some ([], true)
           | uu____20784 -> FStar_Pervasives_Native.None)
  
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
                  let uu____20951 = desugar_binders monad_env eff_binders  in
                  match uu____20951 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let for_free =
                        let uu____20990 =
                          let uu____20992 =
                            let uu____20999 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____20999  in
                          FStar_List.length uu____20992  in
                        uu____20990 = (Prims.parse_int "1")  in
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
                            (uu____21040,(FStar_Parser_AST.TyconAbbrev
                                          (name,uu____21042,uu____21043,uu____21044),uu____21045)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____21078 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____21079 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____21091 = name_of_eff_decl decl  in
                             FStar_List.mem uu____21091 mandatory_members)
                          eff_decls
                         in
                      (match uu____21079 with
                       | (mandatory_members_decls,actions) ->
                           let uu____21108 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____21137  ->
                                     fun decl  ->
                                       match uu____21137 with
                                       | (env2,out) ->
                                           let uu____21157 =
                                             desugar_decl env2 decl  in
                                           (match uu____21157 with
                                            | (env3,ses) ->
                                                let uu____21170 =
                                                  let uu____21173 =
                                                    FStar_List.hd ses  in
                                                  uu____21173 :: out  in
                                                (env3, uu____21170)))
                                  (env1, []))
                              in
                           (match uu____21108 with
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
                                              (uu____21241,(FStar_Parser_AST.TyconAbbrev
                                                            (name,action_params,uu____21244,
                                                             {
                                                               FStar_Parser_AST.tm
                                                                 =
                                                                 FStar_Parser_AST.Construct
                                                                 (uu____21245,
                                                                  (def,uu____21247)::
                                                                  (cps_type,uu____21249)::[]);
                                                               FStar_Parser_AST.range
                                                                 =
                                                                 uu____21250;
                                                               FStar_Parser_AST.level
                                                                 =
                                                                 uu____21251;_}),doc1)::[])
                                              when Prims.op_Negation for_free
                                              ->
                                              let uu____21303 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____21303 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____21341 =
                                                     let uu____21342 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____21343 =
                                                       let uu____21344 =
                                                         desugar_term env3
                                                           def
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____21344
                                                        in
                                                     let uu____21349 =
                                                       let uu____21350 =
                                                         desugar_typ env3
                                                           cps_type
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____21350
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____21342;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____21343;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____21349
                                                     }  in
                                                   (uu____21341, doc1))
                                          | FStar_Parser_AST.Tycon
                                              (uu____21357,(FStar_Parser_AST.TyconAbbrev
                                                            (name,action_params,uu____21360,defn),doc1)::[])
                                              when for_free ->
                                              let uu____21395 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____21395 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____21433 =
                                                     let uu____21434 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____21435 =
                                                       let uu____21436 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____21436
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____21434;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____21435;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____21433, doc1))
                                          | uu____21443 ->
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
                                    let uu____21475 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____21475
                                     in
                                  let uu____21476 =
                                    let uu____21477 =
                                      FStar_Syntax_DsEnv.fail_or env2
                                        (FStar_Syntax_DsEnv.try_lookup_definition
                                           env2) l
                                       in
                                    FStar_All.pipe_left
                                      (FStar_Syntax_Subst.close binders1)
                                      uu____21477
                                     in
                                  ([], uu____21476)  in
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
                                      let uu____21494 =
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      ([], uu____21494)  in
                                    let uu____21501 =
                                      let uu____21502 =
                                        let uu____21503 =
                                          let uu____21504 = lookup1 "repr"
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____21504
                                           in
                                        let uu____21513 = lookup1 "return"
                                           in
                                        let uu____21514 = lookup1 "bind"  in
                                        let uu____21515 =
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
                                            uu____21503;
                                          FStar_Syntax_Syntax.return_repr =
                                            uu____21513;
                                          FStar_Syntax_Syntax.bind_repr =
                                            uu____21514;
                                          FStar_Syntax_Syntax.actions =
                                            actions1;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            uu____21515
                                        }  in
                                      FStar_Syntax_Syntax.Sig_new_effect_for_free
                                        uu____21502
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____21501;
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
                                         (fun uu___136_21521  ->
                                            match uu___136_21521 with
                                            | FStar_Syntax_Syntax.Reifiable 
                                                -> true
                                            | FStar_Syntax_Syntax.Reflectable
                                                uu____21522 -> true
                                            | uu____21523 -> false)
                                         qualifiers
                                        in
                                     let un_ts =
                                       ([], FStar_Syntax_Syntax.tun)  in
                                     let uu____21537 =
                                       let uu____21538 =
                                         let uu____21539 =
                                           lookup1 "return_wp"  in
                                         let uu____21540 = lookup1 "bind_wp"
                                            in
                                         let uu____21541 =
                                           lookup1 "if_then_else"  in
                                         let uu____21542 = lookup1 "ite_wp"
                                            in
                                         let uu____21543 = lookup1 "stronger"
                                            in
                                         let uu____21544 = lookup1 "close_wp"
                                            in
                                         let uu____21545 = lookup1 "assert_p"
                                            in
                                         let uu____21546 = lookup1 "assume_p"
                                            in
                                         let uu____21547 = lookup1 "null_wp"
                                            in
                                         let uu____21548 = lookup1 "trivial"
                                            in
                                         let uu____21549 =
                                           if rr
                                           then
                                             let uu____21550 = lookup1 "repr"
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.snd
                                               uu____21550
                                           else FStar_Syntax_Syntax.tun  in
                                         let uu____21566 =
                                           if rr
                                           then lookup1 "return"
                                           else un_ts  in
                                         let uu____21568 =
                                           if rr
                                           then lookup1 "bind"
                                           else un_ts  in
                                         let uu____21570 =
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
                                             uu____21539;
                                           FStar_Syntax_Syntax.bind_wp =
                                             uu____21540;
                                           FStar_Syntax_Syntax.if_then_else =
                                             uu____21541;
                                           FStar_Syntax_Syntax.ite_wp =
                                             uu____21542;
                                           FStar_Syntax_Syntax.stronger =
                                             uu____21543;
                                           FStar_Syntax_Syntax.close_wp =
                                             uu____21544;
                                           FStar_Syntax_Syntax.assert_p =
                                             uu____21545;
                                           FStar_Syntax_Syntax.assume_p =
                                             uu____21546;
                                           FStar_Syntax_Syntax.null_wp =
                                             uu____21547;
                                           FStar_Syntax_Syntax.trivial =
                                             uu____21548;
                                           FStar_Syntax_Syntax.repr =
                                             uu____21549;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____21566;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____21568;
                                           FStar_Syntax_Syntax.actions =
                                             actions1;
                                           FStar_Syntax_Syntax.eff_attrs =
                                             uu____21570
                                         }  in
                                       FStar_Syntax_Syntax.Sig_new_effect
                                         uu____21538
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         uu____21537;
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
                                          fun uu____21596  ->
                                            match uu____21596 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____21610 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____21610
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
                let uu____21634 = desugar_binders env1 eff_binders  in
                match uu____21634 with
                | (env2,binders) ->
                    let uu____21671 =
                      let uu____21690 = head_and_args defn  in
                      match uu____21690 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____21735 ->
                                let uu____21736 =
                                  let uu____21741 =
                                    let uu____21742 =
                                      let uu____21743 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.strcat uu____21743 " not found"
                                       in
                                    Prims.strcat "Effect " uu____21742  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____21741)
                                   in
                                FStar_Errors.raise_error uu____21736
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____21745 =
                            match FStar_List.rev args with
                            | (last_arg,uu____21775)::args_rev ->
                                let uu____21787 =
                                  let uu____21788 = unparen last_arg  in
                                  uu____21788.FStar_Parser_AST.tm  in
                                (match uu____21787 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____21816 -> ([], args))
                            | uu____21825 -> ([], args)  in
                          (match uu____21745 with
                           | (cattributes,args1) ->
                               let uu____21876 = desugar_args env2 args1  in
                               let uu____21885 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____21876, uu____21885))
                       in
                    (match uu____21671 with
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
                          (let uu____21941 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____21941 with
                           | (ed_binders,uu____21955,ed_binders_opening) ->
                               let sub1 uu____21968 =
                                 match uu____21968 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____21982 =
                                         FStar_Syntax_Subst.shift_subst
                                           (FStar_List.length us)
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____21982 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____21986 =
                                       let uu____21987 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____21987)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____21986
                                  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____21996 =
                                   let uu____21997 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____21997
                                    in
                                 let uu____22012 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____22013 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____22014 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____22015 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____22016 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____22017 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____22018 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____22019 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____22020 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____22021 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____22022 =
                                   let uu____22023 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____22023
                                    in
                                 let uu____22038 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____22039 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____22040 =
                                   FStar_List.map
                                     (fun action  ->
                                        let uu____22048 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____22049 =
                                          let uu____22050 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____22050
                                           in
                                        let uu____22065 =
                                          let uu____22066 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____22066
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____22048;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____22049;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____22065
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
                                     uu____21996;
                                   FStar_Syntax_Syntax.ret_wp = uu____22012;
                                   FStar_Syntax_Syntax.bind_wp = uu____22013;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____22014;
                                   FStar_Syntax_Syntax.ite_wp = uu____22015;
                                   FStar_Syntax_Syntax.stronger = uu____22016;
                                   FStar_Syntax_Syntax.close_wp = uu____22017;
                                   FStar_Syntax_Syntax.assert_p = uu____22018;
                                   FStar_Syntax_Syntax.assume_p = uu____22019;
                                   FStar_Syntax_Syntax.null_wp = uu____22020;
                                   FStar_Syntax_Syntax.trivial = uu____22021;
                                   FStar_Syntax_Syntax.repr = uu____22022;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____22038;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____22039;
                                   FStar_Syntax_Syntax.actions = uu____22040;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____22083 =
                                     let uu____22085 =
                                       let uu____22092 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____22092
                                        in
                                     FStar_List.length uu____22085  in
                                   uu____22083 = (Prims.parse_int "1")  in
                                 let uu____22118 =
                                   let uu____22121 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____22121 quals  in
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
                                   FStar_Syntax_Syntax.sigquals = uu____22118;
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
                                             let uu____22143 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____22143
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____22145 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____22145
                                 then
                                   let reflect_lid =
                                     let uu____22149 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____22149
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
    let uu____22159 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____22159 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.strcat "  " (Prims.strcat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____22210 ->
              let uu____22211 =
                let uu____22212 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____22212
                 in
              Prims.strcat "\n  " uu____22211
          | uu____22213 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____22226  ->
               match uu____22226 with
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
          let uu____22244 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____22244
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____22246 =
          let uu____22255 = FStar_Syntax_Syntax.as_arg arg  in [uu____22255]
           in
        FStar_Syntax_Util.mk_app fv uu____22246

and (desugar_decl_aux :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      let uu____22280 = desugar_decl_noattrs env d  in
      match uu____22280 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____22298 = mk_comment_attr d  in uu____22298 :: attrs1  in
          let uu____22299 =
            FStar_List.mapi
              (fun i  ->
                 fun sigelt  ->
                   if i = (Prims.parse_int "0")
                   then
                     let uu___171_22305 = sigelt  in
                     {
                       FStar_Syntax_Syntax.sigel =
                         (uu___171_22305.FStar_Syntax_Syntax.sigel);
                       FStar_Syntax_Syntax.sigrng =
                         (uu___171_22305.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___171_22305.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___171_22305.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs = attrs2
                     }
                   else
                     (let uu___172_22307 = sigelt  in
                      let uu____22308 =
                        FStar_List.filter
                          (fun at1  ->
                             let uu____22314 = get_fail_attr false at1  in
                             FStar_Option.isNone uu____22314) attrs2
                         in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___172_22307.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___172_22307.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___172_22307.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___172_22307.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs = uu____22308
                      })) sigelts
             in
          (env1, uu____22299)

and (desugar_decl :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      let uu____22335 = desugar_decl_aux env d  in
      match uu____22335 with
      | (env1,ses) ->
          let uu____22346 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____22346)

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
          (if p = FStar_Parser_AST.LightOff
           then FStar_Options.set_ml_ish ()
           else ();
           (env, [se]))
      | FStar_Parser_AST.Fsdoc uu____22374 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____22382 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____22382, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals  in
          let tcs1 =
            FStar_List.map
              (fun uu____22419  ->
                 match uu____22419 with | (x,uu____22427) -> x) tcs
             in
          let uu____22432 =
            FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals
             in
          desugar_tycon env d uu____22432 tcs1
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals  in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____22454;
                    FStar_Parser_AST.prange = uu____22455;_},uu____22456)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____22465;
                    FStar_Parser_AST.prange = uu____22466;_},uu____22467)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____22482;
                         FStar_Parser_AST.prange = uu____22483;_},uu____22484);
                    FStar_Parser_AST.prange = uu____22485;_},uu____22486)::[]
                   -> false
               | (p,uu____22514)::[] ->
                   let uu____22523 = is_app_pattern p  in
                   Prims.op_Negation uu____22523
               | uu____22524 -> false)
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
            let uu____22597 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____22597 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____22609 =
                     let uu____22610 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____22610.FStar_Syntax_Syntax.n  in
                   match uu____22609 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____22620) ->
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
                         | uu____22653::uu____22654 ->
                             FStar_List.map
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____22657 ->
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.collect
                                  (fun uu___137_22672  ->
                                     match uu___137_22672 with
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inl uu____22675;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____22676;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____22677;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____22678;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____22679;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____22680;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____22681;_}
                                         -> []
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____22693;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____22694;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____22695;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____22696;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____22697;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____22698;_}
                                         ->
                                         FStar_Syntax_DsEnv.lookup_letbinding_quals
                                           env
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                          in
                       let quals2 =
                         let uu____22712 =
                           FStar_All.pipe_right lets1
                             (FStar_Util.for_some
                                (fun uu____22743  ->
                                   match uu____22743 with
                                   | (uu____22756,(uu____22757,t)) ->
                                       t.FStar_Parser_AST.level =
                                         FStar_Parser_AST.Formula))
                            in
                         if uu____22712
                         then FStar_Syntax_Syntax.Logic :: quals1
                         else quals1  in
                       let lbs1 =
                         let uu____22775 =
                           FStar_All.pipe_right quals2
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract)
                            in
                         if uu____22775
                         then
                           let uu____22778 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu___173_22792 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___174_22794 = fv  in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___174_22794.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___174_22794.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___173_22792.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___173_22792.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___173_22792.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___173_22792.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___173_22792.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___173_22792.FStar_Syntax_Syntax.lbpos)
                                     }))
                              in
                           ((FStar_Pervasives_Native.fst lbs), uu____22778)
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
                   | uu____22821 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____22827 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____22846 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____22827 with
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
                       let uu___175_22882 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___175_22882.FStar_Parser_AST.prange)
                       }
                   | uu____22889 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___176_22896 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___176_22896.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___176_22896.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___176_22896.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____22932 id1 =
                   match uu____22932 with
                   | (env1,ses) ->
                       let main =
                         let uu____22953 =
                           let uu____22954 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____22954  in
                         FStar_Parser_AST.mk_term uu____22953
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
                       let uu____23004 = desugar_decl env1 id_decl  in
                       (match uu____23004 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____23022 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____23022 FStar_Util.set_elements
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
            let uu____23047 = close_fun env t  in
            desugar_term env uu____23047  in
          let quals1 =
            let uu____23051 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____23051
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let se =
            let uu____23057 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____23057;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in
          let env2 =
            FStar_Syntax_DsEnv.push_doc env1 lid d.FStar_Parser_AST.doc  in
          (env2, [se])
      | FStar_Parser_AST.Exception (id1,FStar_Pervasives_Native.None ) ->
          let uu____23065 =
            FStar_Syntax_DsEnv.fail_or env
              (FStar_Syntax_DsEnv.try_lookup_lid env)
              FStar_Parser_Const.exn_lid
             in
          (match uu____23065 with
           | (t,uu____23079) ->
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
            let uu____23109 =
              let uu____23116 = FStar_Syntax_Syntax.null_binder t  in
              [uu____23116]  in
            let uu____23129 =
              let uu____23132 =
                let uu____23133 =
                  FStar_Syntax_DsEnv.fail_or env
                    (FStar_Syntax_DsEnv.try_lookup_lid env)
                    FStar_Parser_Const.exn_lid
                   in
                FStar_Pervasives_Native.fst uu____23133  in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____23132
               in
            FStar_Syntax_Util.arrow uu____23109 uu____23129  in
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
            let uu____23194 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____23194 with
            | FStar_Pervasives_Native.None  ->
                let uu____23197 =
                  let uu____23202 =
                    let uu____23203 =
                      let uu____23204 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.strcat uu____23204 " not found"  in
                    Prims.strcat "Effect name " uu____23203  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____23202)  in
                FStar_Errors.raise_error uu____23197
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____23208 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____23250 =
                  let uu____23259 =
                    let uu____23266 = desugar_term env t  in
                    ([], uu____23266)  in
                  FStar_Pervasives_Native.Some uu____23259  in
                (uu____23250, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____23299 =
                  let uu____23308 =
                    let uu____23315 = desugar_term env wp  in
                    ([], uu____23315)  in
                  FStar_Pervasives_Native.Some uu____23308  in
                let uu____23324 =
                  let uu____23333 =
                    let uu____23340 = desugar_term env t  in
                    ([], uu____23340)  in
                  FStar_Pervasives_Native.Some uu____23333  in
                (uu____23299, uu____23324)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____23366 =
                  let uu____23375 =
                    let uu____23382 = desugar_term env t  in
                    ([], uu____23382)  in
                  FStar_Pervasives_Native.Some uu____23375  in
                (FStar_Pervasives_Native.None, uu____23366)
             in
          (match uu____23208 with
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
            let uu____23460 =
              let uu____23461 =
                let uu____23468 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____23468, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____23461  in
            {
              FStar_Syntax_Syntax.sigel = uu____23460;
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
      let uu____23494 =
        FStar_List.fold_left
          (fun uu____23514  ->
             fun d  ->
               match uu____23514 with
               | (env1,sigelts) ->
                   let uu____23534 = desugar_decl env1 d  in
                   (match uu____23534 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____23494 with
      | (env1,sigelts) ->
          let rec forward acc uu___139_23579 =
            match uu___139_23579 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____23593,FStar_Syntax_Syntax.Sig_let uu____23594) ->
                     let uu____23607 =
                       let uu____23610 =
                         let uu___177_23611 = se2  in
                         let uu____23612 =
                           let uu____23615 =
                             FStar_List.filter
                               (fun uu___138_23629  ->
                                  match uu___138_23629 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____23633;
                                           FStar_Syntax_Syntax.vars =
                                             uu____23634;_},uu____23635);
                                      FStar_Syntax_Syntax.pos = uu____23636;
                                      FStar_Syntax_Syntax.vars = uu____23637;_}
                                      when
                                      let uu____23660 =
                                        let uu____23661 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____23661
                                         in
                                      uu____23660 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____23662 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____23615
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___177_23611.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___177_23611.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___177_23611.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___177_23611.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____23612
                         }  in
                       uu____23610 :: se1 :: acc  in
                     forward uu____23607 sigelts1
                 | uu____23667 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____23675 = forward [] sigelts  in (env1, uu____23675)
  
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
          | (FStar_Pervasives_Native.None ,uu____23736) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____23740;
               FStar_Syntax_Syntax.exports = uu____23741;
               FStar_Syntax_Syntax.is_interface = uu____23742;_},FStar_Parser_AST.Module
             (current_lid,uu____23744)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____23752) ->
              let uu____23755 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____23755
           in
        let uu____23760 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____23796 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____23796, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____23813 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____23813, mname, decls, false)
           in
        match uu____23760 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____23843 = desugar_decls env2 decls  in
            (match uu____23843 with
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
          let uu____23905 =
            (FStar_Options.interactive ()) &&
              (let uu____23907 =
                 let uu____23908 =
                   let uu____23909 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____23909  in
                 FStar_Util.get_file_extension uu____23908  in
               FStar_List.mem uu____23907 ["fsti"; "fsi"])
             in
          if uu____23905 then as_interface m else m  in
        let uu____23913 = desugar_modul_common curmod env m1  in
        match uu____23913 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____23931 = FStar_Syntax_DsEnv.pop ()  in
              (uu____23931, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul ->
      (env_t,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun m  ->
      let uu____23951 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____23951 with
      | (env1,modul,pop_when_done) ->
          let uu____23965 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____23965 with
           | (env2,modul1) ->
               ((let uu____23977 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____23977
                 then
                   let uu____23978 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____23978
                 else ());
                (let uu____23980 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____23980, modul1))))
  
let (ast_modul_to_modul :
  FStar_Parser_AST.modul ->
    FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun env  ->
      let uu____23998 = desugar_modul env modul  in
      match uu____23998 with | (env1,modul1) -> (modul1, env1)
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      let uu____24029 = desugar_decls env decls  in
      match uu____24029 with | (env1,sigelts) -> (sigelts, env1)
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        let uu____24071 = desugar_partial_modul modul env a_modul  in
        match uu____24071 with | (env1,modul1) -> (modul1, env1)
  
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
              | uu____24157 ->
                  let t =
                    let uu____24165 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____24165  in
                  let uu____24176 =
                    let uu____24177 = FStar_Syntax_Subst.compress t  in
                    uu____24177.FStar_Syntax_Syntax.n  in
                  (match uu____24176 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____24187,uu____24188)
                       -> bs1
                   | uu____24209 -> failwith "Impossible")
               in
            let uu____24216 =
              let uu____24223 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____24223
                FStar_Syntax_Syntax.t_unit
               in
            match uu____24216 with
            | (binders,uu____24225,binders_opening) ->
                let erase_term t =
                  let uu____24233 =
                    let uu____24234 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____24234  in
                  FStar_Syntax_Subst.close binders uu____24233  in
                let erase_tscheme uu____24252 =
                  match uu____24252 with
                  | (us,t) ->
                      let t1 =
                        let uu____24272 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____24272 t  in
                      let uu____24275 =
                        let uu____24276 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____24276  in
                      ([], uu____24275)
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
                    | uu____24295 ->
                        let bs =
                          let uu____24303 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____24303  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____24335 =
                          let uu____24336 =
                            let uu____24339 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____24339  in
                          uu____24336.FStar_Syntax_Syntax.n  in
                        (match uu____24335 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____24341,uu____24342) -> bs1
                         | uu____24363 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____24370 =
                      let uu____24371 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____24371  in
                    FStar_Syntax_Subst.close binders uu____24370  in
                  let uu___178_24372 = action  in
                  let uu____24373 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____24374 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___178_24372.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___178_24372.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____24373;
                    FStar_Syntax_Syntax.action_typ = uu____24374
                  }  in
                let uu___179_24375 = ed  in
                let uu____24376 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____24377 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____24378 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____24379 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____24380 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____24381 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____24382 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____24383 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____24384 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____24385 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____24386 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____24387 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____24388 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____24389 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____24390 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____24391 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___179_24375.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___179_24375.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____24376;
                  FStar_Syntax_Syntax.signature = uu____24377;
                  FStar_Syntax_Syntax.ret_wp = uu____24378;
                  FStar_Syntax_Syntax.bind_wp = uu____24379;
                  FStar_Syntax_Syntax.if_then_else = uu____24380;
                  FStar_Syntax_Syntax.ite_wp = uu____24381;
                  FStar_Syntax_Syntax.stronger = uu____24382;
                  FStar_Syntax_Syntax.close_wp = uu____24383;
                  FStar_Syntax_Syntax.assert_p = uu____24384;
                  FStar_Syntax_Syntax.assume_p = uu____24385;
                  FStar_Syntax_Syntax.null_wp = uu____24386;
                  FStar_Syntax_Syntax.trivial = uu____24387;
                  FStar_Syntax_Syntax.repr = uu____24388;
                  FStar_Syntax_Syntax.return_repr = uu____24389;
                  FStar_Syntax_Syntax.bind_repr = uu____24390;
                  FStar_Syntax_Syntax.actions = uu____24391;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___179_24375.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___180_24407 = se  in
                  let uu____24408 =
                    let uu____24409 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____24409  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____24408;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___180_24407.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___180_24407.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___180_24407.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___180_24407.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___181_24413 = se  in
                  let uu____24414 =
                    let uu____24415 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____24415
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____24414;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___181_24413.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___181_24413.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___181_24413.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___181_24413.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____24417 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____24418 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____24418 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____24430 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____24430
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____24432 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____24432)
  