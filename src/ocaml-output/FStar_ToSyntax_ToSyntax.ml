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
  fun uu___110_66  ->
    match uu___110_66 with
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
      fun uu___111_90  ->
        match uu___111_90 with
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
  fun uu___112_99  ->
    match uu___112_99 with
    | FStar_Parser_AST.SetOptions s -> FStar_Syntax_Syntax.SetOptions s
    | FStar_Parser_AST.ResetOptions sopt ->
        FStar_Syntax_Syntax.ResetOptions sopt
    | FStar_Parser_AST.LightOff  -> FStar_Syntax_Syntax.LightOff
  
let (as_imp :
  FStar_Parser_AST.imp ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
  =
  fun uu___113_110  ->
    match uu___113_110 with
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
  FStar_Pervasives_Native.tuple2 [@@deriving show]
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
  fun uu___114_1710  ->
    match uu___114_1710 with
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
      fun uu___115_1756  ->
        match uu___115_1756 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____1784 = FStar_Syntax_Syntax.null_binder k  in
            (uu____1784, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____1793 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____1793 with
             | (env1,a1) ->
                 (((let uu___139_1819 = a1  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___139_1819.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___139_1819.FStar_Syntax_Syntax.index);
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
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___116_2175  ->
    match uu___116_2175 with
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
    | uu____2176 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____2188 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____2188)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____2207 =
      let uu____2208 = unparen t  in uu____2208.FStar_Parser_AST.tm  in
    match uu____2207 with
    | FStar_Parser_AST.Wild  ->
        let uu____2213 =
          let uu____2214 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____2214  in
        FStar_Util.Inr uu____2213
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____2225)) ->
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
             let uu____2290 = sum_to_universe u n1  in
             FStar_Util.Inr uu____2290
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____2301 = sum_to_universe u n1  in
             FStar_Util.Inr uu____2301
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____2312 =
               let uu____2317 =
                 let uu____2318 = FStar_Parser_AST.term_to_string t  in
                 Prims.strcat
                   "This universe might contain a sum of two universe variables "
                   uu____2318
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____2317)
                in
             FStar_Errors.raise_error uu____2312 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____2323 ->
        let rec aux t1 univargs =
          let uu____2357 =
            let uu____2358 = unparen t1  in uu____2358.FStar_Parser_AST.tm
             in
          match uu____2357 with
          | FStar_Parser_AST.App (t2,targ,uu____2365) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___117_2388  ->
                     match uu___117_2388 with
                     | FStar_Util.Inr uu____2393 -> true
                     | uu____2394 -> false) univargs
              then
                let uu____2399 =
                  let uu____2400 =
                    FStar_List.map
                      (fun uu___118_2409  ->
                         match uu___118_2409 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____2400  in
                FStar_Util.Inr uu____2399
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___119_2426  ->
                        match uu___119_2426 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____2432 -> failwith "impossible")
                     univargs
                    in
                 let uu____2433 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____2433)
          | uu____2439 ->
              let uu____2440 =
                let uu____2445 =
                  let uu____2446 =
                    let uu____2447 = FStar_Parser_AST.term_to_string t1  in
                    Prims.strcat uu____2447 " in universe context"  in
                  Prims.strcat "Unexpected term " uu____2446  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____2445)  in
              FStar_Errors.raise_error uu____2440 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____2456 ->
        let uu____2457 =
          let uu____2462 =
            let uu____2463 =
              let uu____2464 = FStar_Parser_AST.term_to_string t  in
              Prims.strcat uu____2464 " in universe context"  in
            Prims.strcat "Unexpected term " uu____2463  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____2462)  in
        FStar_Errors.raise_error uu____2457 t.FStar_Parser_AST.range
  
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
    | (bv,b,e)::uu____2497 ->
        let uu____2520 =
          let uu____2525 =
            let uu____2526 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format2 "Unexpected antiquotation: %s(%s)"
              (if b then "`@" else "`#") uu____2526
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____2525)  in
        FStar_Errors.raise_error uu____2520 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'Auu____2536 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident,'Auu____2536) FStar_Pervasives_Native.tuple2
        Prims.list -> FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____2564 = FStar_List.hd fields  in
        match uu____2564 with
        | (f,uu____2574) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____2586 =
                match uu____2586 with
                | (f',uu____2592) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____2594 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____2594
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
              (let uu____2598 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____2598);
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
            | FStar_Syntax_Syntax.Pat_dot_term uu____2957 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_wild uu____2964 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_constant uu____2965 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_var x ->
                FStar_Util.set_add x FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_cons (uu____2967,pats1) ->
                let aux out uu____3005 =
                  match uu____3005 with
                  | (p2,uu____3017) ->
                      let intersection =
                        let uu____3025 = pat_vars p2  in
                        FStar_Util.set_intersect uu____3025 out  in
                      let uu____3028 = FStar_Util.set_is_empty intersection
                         in
                      if uu____3028
                      then
                        let uu____3031 = pat_vars p2  in
                        FStar_Util.set_union out uu____3031
                      else
                        (let duplicate_bv =
                           let uu____3036 =
                             FStar_Util.set_elements intersection  in
                           FStar_List.hd uu____3036  in
                         let uu____3039 =
                           let uu____3044 =
                             FStar_Util.format1
                               "Non-linear patterns are not permitted. %s appears more than once in this pattern."
                               (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                              in
                           (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                             uu____3044)
                            in
                         FStar_Errors.raise_error uu____3039 r)
                   in
                FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
             in
          match pats with
          | [] -> ()
          | p1::[] ->
              let uu____3064 = pat_vars p1  in
              FStar_All.pipe_right uu____3064 (fun a238  -> ())
          | p1::ps ->
              let pvars = pat_vars p1  in
              let aux p2 =
                let uu____3092 =
                  let uu____3093 = pat_vars p2  in
                  FStar_Util.set_eq pvars uu____3093  in
                if uu____3092
                then ()
                else
                  (let nonlinear_vars =
                     let uu____3100 = pat_vars p2  in
                     FStar_Util.set_symmetric_difference pvars uu____3100  in
                   let first_nonlinear_var =
                     let uu____3104 = FStar_Util.set_elements nonlinear_vars
                        in
                     FStar_List.hd uu____3104  in
                   let uu____3107 =
                     let uu____3112 =
                       FStar_Util.format1
                         "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                         (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                        in
                     (FStar_Errors.Fatal_IncoherentPatterns, uu____3112)  in
                   FStar_Errors.raise_error uu____3107 r)
                 in
              FStar_List.iter aux ps
           in
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false ,uu____3116) -> ()
         | (true ,FStar_Parser_AST.PatVar uu____3117) -> ()
         | (true ,uu____3124) ->
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_LetMutableForVariablesOnly,
                 "let-mutable is for variables only")
               p.FStar_Parser_AST.prange);
        (let resolvex l e x =
           let uu____3147 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText))
              in
           match uu____3147 with
           | FStar_Pervasives_Native.Some y -> (l, e, y)
           | uu____3163 ->
               let uu____3166 =
                 if is_mut
                 then FStar_Syntax_DsEnv.push_bv_mutable e x
                 else FStar_Syntax_DsEnv.push_bv e x  in
               (match uu____3166 with | (e1,x1) -> ((x1 :: l), e1, x1))
            in
         let rec aux' top loc env1 p1 =
           let pos q =
             FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange  in
           let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
           let orig = p1  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr uu____3278 -> failwith "impossible"
           | FStar_Parser_AST.PatOp op ->
               let uu____3294 =
                 let uu____3295 =
                   let uu____3296 =
                     let uu____3303 =
                       let uu____3304 =
                         let uu____3309 =
                           FStar_Parser_AST.compile_op (Prims.parse_int "0")
                             op.FStar_Ident.idText op.FStar_Ident.idRange
                            in
                         (uu____3309, (op.FStar_Ident.idRange))  in
                       FStar_Ident.mk_ident uu____3304  in
                     (uu____3303, FStar_Pervasives_Native.None)  in
                   FStar_Parser_AST.PatVar uu____3296  in
                 {
                   FStar_Parser_AST.pat = uu____3295;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 }  in
               aux loc env1 uu____3294
           | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
               ((match tacopt with
                 | FStar_Pervasives_Native.None  -> ()
                 | FStar_Pervasives_Native.Some uu____3326 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                         "Type ascriptions within patterns are cannot be associated with a tactic")
                       orig.FStar_Parser_AST.prange);
                (let uu____3327 = aux loc env1 p2  in
                 match uu____3327 with
                 | (loc1,env',binder,p3,imp) ->
                     let annot_pat_var p4 t1 =
                       match p4.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let uu___140_3385 = p4  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var
                                  (let uu___141_3390 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___141_3390.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___141_3390.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }));
                             FStar_Syntax_Syntax.p =
                               (uu___140_3385.FStar_Syntax_Syntax.p)
                           }
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let uu___142_3392 = p4  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild
                                  (let uu___143_3397 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___143_3397.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___143_3397.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }));
                             FStar_Syntax_Syntax.p =
                               (uu___142_3392.FStar_Syntax_Syntax.p)
                           }
                       | uu____3398 when top -> p4
                       | uu____3399 ->
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                               "Type ascriptions within patterns are only allowed on variables")
                             orig.FStar_Parser_AST.prange
                        in
                     let uu____3402 =
                       match binder with
                       | LetBinder uu____3415 -> failwith "impossible"
                       | LocalBinder (x,aq) ->
                           let t1 =
                             let uu____3435 = close_fun env1 t  in
                             desugar_term env1 uu____3435  in
                           (if
                              (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                               with
                               | FStar_Syntax_Syntax.Tm_unknown  -> false
                               | uu____3437 -> true)
                            then
                              (let uu____3438 =
                                 let uu____3443 =
                                   let uu____3444 =
                                     FStar_Syntax_Print.bv_to_string x  in
                                   let uu____3445 =
                                     FStar_Syntax_Print.term_to_string
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____3446 =
                                     FStar_Syntax_Print.term_to_string t1  in
                                   FStar_Util.format3
                                     "Multiple ascriptions for %s in pattern, type %s was shadowed by %s\n"
                                     uu____3444 uu____3445 uu____3446
                                    in
                                 (FStar_Errors.Warning_MultipleAscriptions,
                                   uu____3443)
                                  in
                               FStar_Errors.log_issue
                                 orig.FStar_Parser_AST.prange uu____3438)
                            else ();
                            (let uu____3448 = annot_pat_var p3 t1  in
                             (uu____3448,
                               (LocalBinder
                                  ((let uu___144_3454 = x  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___144_3454.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___144_3454.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    }), aq)))))
                        in
                     (match uu____3402 with
                      | (p4,binder1) -> (loc1, env', binder1, p4, imp))))
           | FStar_Parser_AST.PatWild  ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____3476 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____3476, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____3485 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____3485, false)
           | FStar_Parser_AST.PatTvar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual aq  in
               let uu____3504 = resolvex loc env1 x  in
               (match uu____3504 with
                | (loc1,env2,xbv) ->
                    let uu____3526 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____3526, imp))
           | FStar_Parser_AST.PatVar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual aq  in
               let uu____3545 = resolvex loc env1 x  in
               (match uu____3545 with
                | (loc1,env2,xbv) ->
                    let uu____3567 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____3567, imp))
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
               let uu____3577 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, []))
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____3577, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____3599;_},args)
               ->
               let uu____3605 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____3646  ->
                        match uu____3646 with
                        | (loc1,env2,args1) ->
                            let uu____3694 = aux loc1 env2 arg  in
                            (match uu____3694 with
                             | (loc2,env3,uu____3723,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, [])
                  in
               (match uu____3605 with
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
                    let uu____3793 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                       in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)),
                      uu____3793, false))
           | FStar_Parser_AST.PatApp uu____3808 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                 p1.FStar_Parser_AST.prange
           | FStar_Parser_AST.PatList pats ->
               let uu____3830 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____3863  ->
                        match uu____3863 with
                        | (loc1,env2,pats1) ->
                            let uu____3895 = aux loc1 env2 pat  in
                            (match uu____3895 with
                             | (loc2,env3,uu____3920,pat1,uu____3922) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, [])
                  in
               (match uu____3830 with
                | (loc1,env2,pats1) ->
                    let pat =
                      let uu____3965 =
                        let uu____3968 =
                          let uu____3975 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange
                             in
                          pos_r uu____3975  in
                        let uu____3976 =
                          let uu____3977 =
                            let uu____3990 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Parser_Const.nil_lid
                                FStar_Syntax_Syntax.delta_constant
                                (FStar_Pervasives_Native.Some
                                   FStar_Syntax_Syntax.Data_ctor)
                               in
                            (uu____3990, [])  in
                          FStar_Syntax_Syntax.Pat_cons uu____3977  in
                        FStar_All.pipe_left uu____3968 uu____3976  in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p
                                in
                             let uu____4022 =
                               let uu____4023 =
                                 let uu____4036 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.cons_lid
                                     FStar_Syntax_Syntax.delta_constant
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Data_ctor)
                                    in
                                 (uu____4036, [(hd1, false); (tl1, false)])
                                  in
                               FStar_Syntax_Syntax.Pat_cons uu____4023  in
                             FStar_All.pipe_left (pos_r r) uu____4022) pats1
                        uu____3965
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
               let uu____4078 =
                 FStar_List.fold_left
                   (fun uu____4118  ->
                      fun p2  ->
                        match uu____4118 with
                        | (loc1,env2,pats) ->
                            let uu____4167 = aux loc1 env2 p2  in
                            (match uu____4167 with
                             | (loc2,env3,uu____4196,pat,uu____4198) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args
                  in
               (match uu____4078 with
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
                    let uu____4293 =
                      FStar_Syntax_DsEnv.fail_or env2
                        (FStar_Syntax_DsEnv.try_lookup_lid env2) l
                       in
                    (match uu____4293 with
                     | (constr,uu____4315) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____4318 -> failwith "impossible"  in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (FStar_Pervasives_Native.Some
                                (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun
                            in
                         let uu____4320 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                            in
                         (loc1, env2,
                           (LocalBinder (x, FStar_Pervasives_Native.None)),
                           uu____4320, false)))
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
                      (fun uu____4389  ->
                         match uu____4389 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2)))
                  in
               let args =
                 FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                   (FStar_List.map
                      (fun uu____4419  ->
                         match uu____4419 with
                         | (f,uu____4425) ->
                             let uu____4426 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____4452  ->
                                       match uu____4452 with
                                       | (g,uu____4458) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText))
                                in
                             (match uu____4426 with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
                              | FStar_Pervasives_Native.Some (uu____4463,p2)
                                  -> p2)))
                  in
               let app =
                 let uu____4470 =
                   let uu____4471 =
                     let uu____4478 =
                       let uu____4479 =
                         let uu____4480 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                                [record.FStar_Syntax_DsEnv.constrname])
                            in
                         FStar_Parser_AST.PatName uu____4480  in
                       FStar_Parser_AST.mk_pattern uu____4479
                         p1.FStar_Parser_AST.prange
                        in
                     (uu____4478, args)  in
                   FStar_Parser_AST.PatApp uu____4471  in
                 FStar_Parser_AST.mk_pattern uu____4470
                   p1.FStar_Parser_AST.prange
                  in
               let uu____4483 = aux loc env1 app  in
               (match uu____4483 with
                | (env2,e,b,p2,uu____4512) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____4540 =
                            let uu____4541 =
                              let uu____4554 =
                                let uu___145_4555 = fv  in
                                let uu____4556 =
                                  let uu____4559 =
                                    let uu____4560 =
                                      let uu____4567 =
                                        FStar_All.pipe_right
                                          record.FStar_Syntax_DsEnv.fields
                                          (FStar_List.map
                                             FStar_Pervasives_Native.fst)
                                         in
                                      ((record.FStar_Syntax_DsEnv.typename),
                                        uu____4567)
                                       in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____4560
                                     in
                                  FStar_Pervasives_Native.Some uu____4559  in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___145_4555.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___145_4555.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____4556
                                }  in
                              (uu____4554, args1)  in
                            FStar_Syntax_Syntax.Pat_cons uu____4541  in
                          FStar_All.pipe_left pos uu____4540
                      | uu____4594 -> p2  in
                    (env2, e, b, p3, false))
         
         and aux loc env1 p1 = aux' false loc env1 p1
          in
         let aux_maybe_or env1 p1 =
           let loc = []  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____4648 = aux' true loc env1 p2  in
               (match uu____4648 with
                | (loc1,env2,var,p3,uu____4675) ->
                    let uu____4680 =
                      FStar_List.fold_left
                        (fun uu____4712  ->
                           fun p4  ->
                             match uu____4712 with
                             | (loc2,env3,ps1) ->
                                 let uu____4745 = aux' true loc2 env3 p4  in
                                 (match uu____4745 with
                                  | (loc3,env4,uu____4770,p5,uu____4772) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps
                       in
                    (match uu____4680 with
                     | (loc2,env3,ps1) ->
                         let pats = p3 :: (FStar_List.rev ps1)  in
                         (env3, var, pats)))
           | uu____4823 ->
               let uu____4824 = aux' true loc env1 p1  in
               (match uu____4824 with
                | (loc1,env2,vars,pat,b) -> (env2, vars, [pat]))
            in
         let uu____4864 = aux_maybe_or env p  in
         match uu____4864 with
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
            let uu____4923 =
              let uu____4924 =
                let uu____4935 = FStar_Syntax_DsEnv.qualify env x  in
                (uu____4935,
                  (FStar_Syntax_Syntax.tun, FStar_Pervasives_Native.None))
                 in
              LetBinder uu____4924  in
            (env, uu____4923, [])  in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____4963 =
                  let uu____4964 =
                    let uu____4969 =
                      FStar_Parser_AST.compile_op (Prims.parse_int "0")
                        x.FStar_Ident.idText x.FStar_Ident.idRange
                       in
                    (uu____4969, (x.FStar_Ident.idRange))  in
                  FStar_Ident.mk_ident uu____4964  in
                mklet uu____4963
            | FStar_Parser_AST.PatVar (x,uu____4971) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____4977);
                   FStar_Parser_AST.prange = uu____4978;_},(t,tacopt))
                ->
                let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)
                   in
                let uu____4998 =
                  let uu____4999 =
                    let uu____5010 = FStar_Syntax_DsEnv.qualify env x  in
                    let uu____5011 =
                      let uu____5018 = desugar_term env t  in
                      (uu____5018, tacopt1)  in
                    (uu____5010, uu____5011)  in
                  LetBinder uu____4999  in
                (env, uu____4998, [])
            | uu____5029 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_UnexpectedPattern,
                    "Unexpected pattern at the top-level")
                  p.FStar_Parser_AST.prange
          else
            (let uu____5039 = desugar_data_pat env p is_mut  in
             match uu____5039 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1 with
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                         uu____5068;
                       FStar_Syntax_Syntax.p = uu____5069;_}::[] -> []
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                         uu____5070;
                       FStar_Syntax_Syntax.p = uu____5071;_}::[] -> []
                   | uu____5072 -> p1  in
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
  fun uu____5079  ->
    fun env  ->
      fun pat  ->
        let uu____5082 = desugar_data_pat env pat false  in
        match uu____5082 with | (env1,uu____5098,pat1) -> (env1, pat1)

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
      let uu____5117 = desugar_term_aq env e  in
      match uu____5117 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____5134 = desugar_typ_aq env e  in
      match uu____5134 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness,FStar_Const.width)
        FStar_Pervasives_Native.tuple2 ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____5144  ->
        fun range  ->
          match uu____5144 with
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
              ((let uu____5154 =
                  let uu____5155 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____5155  in
                if uu____5154
                then
                  let uu____5156 =
                    let uu____5161 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____5161)  in
                  FStar_Errors.log_issue range uu____5156
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
                  let uu____5166 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____5166 range  in
                let lid1 =
                  let uu____5170 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____5170 with
                  | FStar_Pervasives_Native.Some (intro_term,uu____5180) ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____5189 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____5189 range  in
                           let private_fv =
                             let uu____5191 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____5191 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___146_5192 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___146_5192.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___146_5192.FStar_Syntax_Syntax.vars)
                           }
                       | uu____5193 ->
                           failwith
                             (Prims.strcat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____5200 =
                        let uu____5205 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____5205)
                         in
                      FStar_Errors.raise_error uu____5200 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____5221 =
                  let uu____5228 =
                    let uu____5229 =
                      let uu____5244 =
                        let uu____5253 =
                          let uu____5260 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____5260)  in
                        [uu____5253]  in
                      (lid1, uu____5244)  in
                    FStar_Syntax_Syntax.Tm_app uu____5229  in
                  FStar_Syntax_Syntax.mk uu____5228  in
                uu____5221 FStar_Pervasives_Native.None range))

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
            let uu____5299 =
              let uu____5308 =
                (if resolve
                 then FStar_Syntax_DsEnv.try_lookup_lid_with_attributes
                 else
                   FStar_Syntax_DsEnv.try_lookup_lid_with_attributes_no_resolve)
                  env
                 in
              FStar_Syntax_DsEnv.fail_or env uu____5308 l  in
            match uu____5299 with
            | (tm,mut,attrs) ->
                let warn_if_deprecated attrs1 =
                  FStar_List.iter
                    (fun a  ->
                       match a.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_app
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____5363;
                              FStar_Syntax_Syntax.vars = uu____5364;_},args)
                           when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____5387 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____5387 " is deprecated"  in
                           let msg1 =
                             if
                               (FStar_List.length args) >
                                 (Prims.parse_int "0")
                             then
                               let uu____5395 =
                                 let uu____5396 =
                                   let uu____5399 = FStar_List.hd args  in
                                   FStar_Pervasives_Native.fst uu____5399  in
                                 uu____5396.FStar_Syntax_Syntax.n  in
                               match uu____5395 with
                               | FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_string (s,uu____5415))
                                   when
                                   Prims.op_Negation
                                     ((FStar_Util.trim_string s) = "")
                                   ->
                                   Prims.strcat msg
                                     (Prims.strcat ", use "
                                        (Prims.strcat s " instead"))
                               | uu____5416 -> msg
                             else msg  in
                           let uu____5418 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____5418
                             (FStar_Errors.Warning_DeprecatedDefinition,
                               msg1)
                       | FStar_Syntax_Syntax.Tm_fvar fv when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____5421 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____5421 " is deprecated"  in
                           let uu____5422 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____5422
                             (FStar_Errors.Warning_DeprecatedDefinition, msg)
                       | uu____5423 -> ()) attrs1
                   in
                (warn_if_deprecated attrs;
                 (let tm1 = setpos tm  in
                  if mut
                  then
                    let uu____5428 =
                      let uu____5429 =
                        let uu____5436 = mk_ref_read tm1  in
                        (uu____5436,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Mutable_rval))
                         in
                      FStar_Syntax_Syntax.Tm_meta uu____5429  in
                    FStar_All.pipe_left mk1 uu____5428
                  else tm1))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____5454 =
          let uu____5455 = unparen t  in uu____5455.FStar_Parser_AST.tm  in
        match uu____5454 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____5456; FStar_Ident.ident = uu____5457;
              FStar_Ident.nsstr = uu____5458; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____5461 ->
            let uu____5462 =
              let uu____5467 =
                let uu____5468 = FStar_Parser_AST.term_to_string t  in
                Prims.strcat "Unknown attribute " uu____5468  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____5467)  in
            FStar_Errors.raise_error uu____5462 t.FStar_Parser_AST.range
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
          let uu___147_5563 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___147_5563.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___147_5563.FStar_Syntax_Syntax.vars)
          }  in
        let uu____5566 =
          let uu____5567 = unparen top  in uu____5567.FStar_Parser_AST.tm  in
        match uu____5566 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____5572 ->
            let uu____5579 = desugar_formula env top  in (uu____5579, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____5586 = desugar_formula env t  in (uu____5586, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____5593 = desugar_formula env t  in (uu____5593, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____5617 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____5617, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____5619 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____5619, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____5627 =
                let uu____5628 =
                  let uu____5635 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____5635, args)  in
                FStar_Parser_AST.Op uu____5628  in
              FStar_Parser_AST.mk_term uu____5627 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____5638 =
              let uu____5639 =
                let uu____5640 =
                  let uu____5647 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____5647, [e])  in
                FStar_Parser_AST.Op uu____5640  in
              FStar_Parser_AST.mk_term uu____5639 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____5638
        | FStar_Parser_AST.Op (op_star,uu____5651::uu____5652::[]) when
            (let uu____5657 = FStar_Ident.text_of_id op_star  in
             uu____5657 = "*") &&
              (let uu____5659 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____5659 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____5674;_},t1::t2::[])
                  ->
                  let uu____5679 = flatten1 t1  in
                  FStar_List.append uu____5679 [t2]
              | uu____5682 -> [t]  in
            let uu____5683 =
              let uu____5708 =
                let uu____5731 =
                  let uu____5734 = unparen top  in flatten1 uu____5734  in
                FStar_All.pipe_right uu____5731
                  (FStar_List.map
                     (fun t  ->
                        let uu____5753 = desugar_typ_aq env t  in
                        match uu____5753 with
                        | (t',aq) ->
                            let uu____5764 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____5764, aq)))
                 in
              FStar_All.pipe_right uu____5708 FStar_List.unzip  in
            (match uu____5683 with
             | (targs,aqs) ->
                 let uu____5873 =
                   let uu____5878 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____5878
                    in
                 (match uu____5873 with
                  | (tup,uu____5894) ->
                      let uu____5895 =
                        mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                      (uu____5895, (join_aqs aqs))))
        | FStar_Parser_AST.Tvar a ->
            let uu____5907 =
              let uu____5908 =
                let uu____5911 =
                  FStar_Syntax_DsEnv.fail_or2
                    (FStar_Syntax_DsEnv.try_lookup_id env) a
                   in
                FStar_Pervasives_Native.fst uu____5911  in
              FStar_All.pipe_left setpos uu____5908  in
            (uu____5907, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____5923 =
              let uu____5928 =
                let uu____5929 =
                  let uu____5930 = FStar_Ident.text_of_id u  in
                  Prims.strcat uu____5930 " in non-universe context"  in
                Prims.strcat "Unexpected universe variable " uu____5929  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____5928)  in
            FStar_Errors.raise_error uu____5923 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____5941 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____5941 with
             | FStar_Pervasives_Native.None  ->
                 let uu____5948 =
                   let uu____5953 =
                     let uu____5954 = FStar_Ident.text_of_id s  in
                     Prims.strcat "Unexpected or unbound operator: "
                       uu____5954
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____5953)
                    in
                 FStar_Errors.raise_error uu____5948
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let uu____5964 =
                     let uu____5989 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____6041 = desugar_term_aq env t  in
                               match uu____6041 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____5989 FStar_List.unzip  in
                   (match uu____5964 with
                    | (args1,aqs) ->
                        let uu____6174 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____6174, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____6188)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____6203 =
              let uu___148_6204 = top  in
              let uu____6205 =
                let uu____6206 =
                  let uu____6213 =
                    let uu___149_6214 = top  in
                    let uu____6215 =
                      let uu____6216 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____6216  in
                    {
                      FStar_Parser_AST.tm = uu____6215;
                      FStar_Parser_AST.range =
                        (uu___149_6214.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___149_6214.FStar_Parser_AST.level)
                    }  in
                  (uu____6213, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____6206  in
              {
                FStar_Parser_AST.tm = uu____6205;
                FStar_Parser_AST.range =
                  (uu___148_6204.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___148_6204.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____6203
        | FStar_Parser_AST.Construct (n1,(a,uu____6219)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____6235 =
                let uu___150_6236 = top  in
                let uu____6237 =
                  let uu____6238 =
                    let uu____6245 =
                      let uu___151_6246 = top  in
                      let uu____6247 =
                        let uu____6248 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____6248  in
                      {
                        FStar_Parser_AST.tm = uu____6247;
                        FStar_Parser_AST.range =
                          (uu___151_6246.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___151_6246.FStar_Parser_AST.level)
                      }  in
                    (uu____6245, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____6238  in
                {
                  FStar_Parser_AST.tm = uu____6237;
                  FStar_Parser_AST.range =
                    (uu___150_6236.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___150_6236.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____6235))
        | FStar_Parser_AST.Construct (n1,(a,uu____6251)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____6266 =
              let uu___152_6267 = top  in
              let uu____6268 =
                let uu____6269 =
                  let uu____6276 =
                    let uu___153_6277 = top  in
                    let uu____6278 =
                      let uu____6279 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____6279  in
                    {
                      FStar_Parser_AST.tm = uu____6278;
                      FStar_Parser_AST.range =
                        (uu___153_6277.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___153_6277.FStar_Parser_AST.level)
                    }  in
                  (uu____6276, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____6269  in
              {
                FStar_Parser_AST.tm = uu____6268;
                FStar_Parser_AST.range =
                  (uu___152_6267.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___152_6267.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____6266
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____6280; FStar_Ident.ident = uu____6281;
              FStar_Ident.nsstr = uu____6282; FStar_Ident.str = "Type0";_}
            ->
            let uu____6285 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____6285, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____6286; FStar_Ident.ident = uu____6287;
              FStar_Ident.nsstr = uu____6288; FStar_Ident.str = "Type";_}
            ->
            let uu____6291 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____6291, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____6292; FStar_Ident.ident = uu____6293;
               FStar_Ident.nsstr = uu____6294; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____6312 =
              let uu____6313 =
                let uu____6314 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____6314  in
              mk1 uu____6313  in
            (uu____6312, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____6315; FStar_Ident.ident = uu____6316;
              FStar_Ident.nsstr = uu____6317; FStar_Ident.str = "Effect";_}
            ->
            let uu____6320 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____6320, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____6321; FStar_Ident.ident = uu____6322;
              FStar_Ident.nsstr = uu____6323; FStar_Ident.str = "True";_}
            ->
            let uu____6326 =
              let uu____6327 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____6327
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____6326, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____6328; FStar_Ident.ident = uu____6329;
              FStar_Ident.nsstr = uu____6330; FStar_Ident.str = "False";_}
            ->
            let uu____6333 =
              let uu____6334 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____6334
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____6333, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____6337;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____6339 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____6339 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____6348 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_constant_at_level
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None
                     in
                  (uu____6348, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____6349 =
                    let uu____6350 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____6350 txt
                     in
                  failwith uu____6349))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____6357 = desugar_name mk1 setpos env true l  in
              (uu____6357, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____6360 = desugar_name mk1 setpos env true l  in
              (uu____6360, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____6371 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____6371 with
                | FStar_Pervasives_Native.Some uu____6380 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____6385 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____6385 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____6399 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____6416 =
                    let uu____6417 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____6417  in
                  (uu____6416, noaqs)
              | uu____6418 ->
                  let uu____6425 =
                    let uu____6430 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____6430)  in
                  FStar_Errors.raise_error uu____6425
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____6437 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____6437 with
              | FStar_Pervasives_Native.None  ->
                  let uu____6444 =
                    let uu____6449 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____6449)
                     in
                  FStar_Errors.raise_error uu____6444
                    top.FStar_Parser_AST.range
              | uu____6454 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____6458 = desugar_name mk1 setpos env true lid'  in
                  (uu____6458, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____6474 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____6474 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____6493 ->
                       let uu____6500 =
                         FStar_Util.take
                           (fun uu____6524  ->
                              match uu____6524 with
                              | (uu____6529,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____6500 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____6574 =
                              let uu____6599 =
                                FStar_List.map
                                  (fun uu____6642  ->
                                     match uu____6642 with
                                     | (t,imp) ->
                                         let uu____6659 =
                                           desugar_term_aq env t  in
                                         (match uu____6659 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____6599
                                FStar_List.unzip
                               in
                            (match uu____6574 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____6800 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____6800, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____6816 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____6816 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.strcat "Constructor "
                             (Prims.strcat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____6823 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.strcat "Effect "
                             (Prims.strcat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____6834 =
              FStar_List.fold_left
                (fun uu____6879  ->
                   fun b  ->
                     match uu____6879 with
                     | (env1,tparams,typs) ->
                         let uu____6936 = desugar_binder env1 b  in
                         (match uu____6936 with
                          | (xopt,t1) ->
                              let uu____6965 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____6974 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____6974)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____6965 with
                               | (env2,x) ->
                                   let uu____6994 =
                                     let uu____6997 =
                                       let uu____7000 =
                                         let uu____7001 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____7001
                                          in
                                       [uu____7000]  in
                                     FStar_List.append typs uu____6997  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___154_7027 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___154_7027.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___154_7027.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____6994)))) (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      FStar_Pervasives_Native.None])
               in
            (match uu____6834 with
             | (env1,uu____7055,targs) ->
                 let uu____7077 =
                   let uu____7082 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____7082
                    in
                 (match uu____7077 with
                  | (tup,uu____7092) ->
                      let uu____7093 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_app (tup, targs))
                         in
                      (uu____7093, noaqs)))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____7110 = uncurry binders t  in
            (match uu____7110 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___120_7152 =
                   match uu___120_7152 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1  in
                       let uu____7166 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____7166
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____7188 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____7188 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____7221 = aux env [] bs  in (uu____7221, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____7228 = desugar_binder env b  in
            (match uu____7228 with
             | (FStar_Pervasives_Native.None ,uu____7239) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____7253 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____7253 with
                  | ((x,uu____7269),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____7282 =
                        let uu____7283 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____7283  in
                      (uu____7282, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern)
               in
            let uu____7301 =
              FStar_List.fold_left
                (fun uu____7321  ->
                   fun pat  ->
                     match uu____7321 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed
                              (uu____7347,(t,FStar_Pervasives_Native.None ))
                              ->
                              let uu____7357 =
                                let uu____7360 = free_type_vars env1 t  in
                                FStar_List.append uu____7360 ftvs  in
                              (env1, uu____7357)
                          | FStar_Parser_AST.PatAscribed
                              (uu____7365,(t,FStar_Pervasives_Native.Some
                                           tac))
                              ->
                              let uu____7376 =
                                let uu____7379 = free_type_vars env1 t  in
                                let uu____7382 =
                                  let uu____7385 = free_type_vars env1 tac
                                     in
                                  FStar_List.append uu____7385 ftvs  in
                                FStar_List.append uu____7379 uu____7382  in
                              (env1, uu____7376)
                          | uu____7390 -> (env1, ftvs))) (env, []) binders1
               in
            (match uu____7301 with
             | (uu____7399,ftv) ->
                 let ftv1 = sort_ftv ftv  in
                 let binders2 =
                   let uu____7411 =
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
                   FStar_List.append uu____7411 binders1  in
                 let rec aux env1 bs sc_pat_opt uu___121_7466 =
                   match uu___121_7466 with
                   | [] ->
                       let uu____7491 = desugar_term_aq env1 body  in
                       (match uu____7491 with
                        | (body1,aq) ->
                            let body2 =
                              match sc_pat_opt with
                              | FStar_Pervasives_Native.Some (sc,pat) ->
                                  let body2 =
                                    let uu____7528 =
                                      let uu____7529 =
                                        FStar_Syntax_Syntax.pat_bvs pat  in
                                      FStar_All.pipe_right uu____7529
                                        (FStar_List.map
                                           FStar_Syntax_Syntax.mk_binder)
                                       in
                                    FStar_Syntax_Subst.close uu____7528 body1
                                     in
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_match
                                       (sc,
                                         [(pat, FStar_Pervasives_Native.None,
                                            body2)]))
                                    FStar_Pervasives_Native.None
                                    body2.FStar_Syntax_Syntax.pos
                              | FStar_Pervasives_Native.None  -> body1  in
                            let uu____7598 =
                              let uu____7601 =
                                no_annot_abs (FStar_List.rev bs) body2  in
                              setpos uu____7601  in
                            (uu____7598, aq))
                   | p::rest ->
                       let uu____7614 = desugar_binding_pat env1 p  in
                       (match uu____7614 with
                        | (env2,b,pat) ->
                            let pat1 =
                              match pat with
                              | [] -> FStar_Pervasives_Native.None
                              | p1::[] -> FStar_Pervasives_Native.Some p1
                              | uu____7648 ->
                                  FStar_Errors.raise_error
                                    (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                      "Disjunctive patterns are not supported in abstractions")
                                    p.FStar_Parser_AST.prange
                               in
                            let uu____7655 =
                              match b with
                              | LetBinder uu____7692 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat1, sc_pat_opt) with
                                    | (FStar_Pervasives_Native.None
                                       ,uu____7758) -> sc_pat_opt
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.None ) ->
                                        let uu____7812 =
                                          let uu____7819 =
                                            FStar_Syntax_Syntax.bv_to_name x
                                             in
                                          (uu____7819, p1)  in
                                        FStar_Pervasives_Native.Some
                                          uu____7812
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.Some
                                       (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____7875,uu____7876) ->
                                             let tup2 =
                                               let uu____7878 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____7878
                                                 FStar_Syntax_Syntax.delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____7882 =
                                                 let uu____7889 =
                                                   let uu____7890 =
                                                     let uu____7905 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2)
                                                        in
                                                     let uu____7908 =
                                                       let uu____7917 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc
                                                          in
                                                       let uu____7924 =
                                                         let uu____7933 =
                                                           let uu____7940 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x
                                                              in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____7940
                                                            in
                                                         [uu____7933]  in
                                                       uu____7917 ::
                                                         uu____7924
                                                        in
                                                     (uu____7905, uu____7908)
                                                      in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____7890
                                                    in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____7889
                                                  in
                                               uu____7882
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Parser_AST.range
                                                in
                                             let p2 =
                                               let uu____7975 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p1, false)]))
                                                 uu____7975
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____8018,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____8020,pats)) ->
                                             let tupn =
                                               let uu____8059 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____8059
                                                 FStar_Syntax_Syntax.delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____8069 =
                                                 let uu____8070 =
                                                   let uu____8085 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn)
                                                      in
                                                   let uu____8088 =
                                                     let uu____8097 =
                                                       let uu____8106 =
                                                         let uu____8113 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____8113
                                                          in
                                                       [uu____8106]  in
                                                     FStar_List.append args
                                                       uu____8097
                                                      in
                                                   (uu____8085, uu____8088)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____8070
                                                  in
                                               mk1 uu____8069  in
                                             let p2 =
                                               let uu____8151 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p1, false)])))
                                                 uu____8151
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | uu____8192 ->
                                             failwith "Impossible")
                                     in
                                  ((x, aq), sc_pat_opt1)
                               in
                            (match uu____7655 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest))
                    in
                 aux env [] FStar_Pervasives_Native.None binders2)
        | FStar_Parser_AST.App
            (uu____8273,uu____8274,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____8296 =
                let uu____8297 = unparen e  in uu____8297.FStar_Parser_AST.tm
                 in
              match uu____8296 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____8307 ->
                  let uu____8308 = desugar_term_aq env e  in
                  (match uu____8308 with
                   | (head1,aq) ->
                       let uu____8321 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____8321, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____8328 ->
            let rec aux args aqs e =
              let uu____8387 =
                let uu____8388 = unparen e  in uu____8388.FStar_Parser_AST.tm
                 in
              match uu____8387 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____8408 = desugar_term_aq env t  in
                  (match uu____8408 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____8444 ->
                  let uu____8445 = desugar_term_aq env e  in
                  (match uu____8445 with
                   | (head1,aq) ->
                       let uu____8468 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____8468, (join_aqs (aq :: aqs))))
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
            let uu____8520 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____8520
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
            let uu____8572 = desugar_term_aq env t  in
            (match uu____8572 with
             | (tm,s) ->
                 let uu____8583 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____8583, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____8589 =
              let uu____8602 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____8602 then desugar_typ_aq else desugar_term_aq  in
            uu____8589 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____8657 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____8800  ->
                        match uu____8800 with
                        | (attr_opt,(p,def)) ->
                            let uu____8858 = is_app_pattern p  in
                            if uu____8858
                            then
                              let uu____8889 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____8889, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____8971 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____8971, def1)
                               | uu____9016 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____9054);
                                           FStar_Parser_AST.prange =
                                             uu____9055;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____9103 =
                                            let uu____9124 =
                                              let uu____9129 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____9129  in
                                            (uu____9124, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____9103, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____9220) ->
                                        if top_level
                                        then
                                          let uu____9255 =
                                            let uu____9276 =
                                              let uu____9281 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____9281  in
                                            (uu____9276, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____9255, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____9371 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____9402 =
                FStar_List.fold_left
                  (fun uu____9475  ->
                     fun uu____9476  ->
                       match (uu____9475, uu____9476) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____9584,uu____9585),uu____9586))
                           ->
                           let uu____9703 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____9729 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____9729 with
                                  | (env2,xx) ->
                                      let uu____9748 =
                                        let uu____9751 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____9751 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx), uu____9748))
                             | FStar_Util.Inr l ->
                                 let uu____9759 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (uu____9759, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____9703 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____9402 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____9907 =
                    match uu____9907 with
                    | (attrs_opt,(uu____9943,args,result_t),def) ->
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
                                let uu____10031 = is_comp_type env1 t  in
                                if uu____10031
                                then
                                  ((let uu____10033 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____10043 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____10043))
                                       in
                                    match uu____10033 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____10046 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____10048 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____10048))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____10046
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t)
                                 in
                              let uu____10053 =
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range
                                 in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed (def, t1, tacopt))
                                uu____10053 FStar_Parser_AST.Expr
                           in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____10057 ->
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
                              let uu____10072 =
                                let uu____10073 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____10073
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____10072
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
                  let uu____10148 = desugar_term_aq env' body  in
                  (match uu____10148 with
                   | (body1,aq) ->
                       let uu____10161 =
                         let uu____10164 =
                           let uu____10165 =
                             let uu____10178 =
                               FStar_Syntax_Subst.close rec_bindings1 body1
                                in
                             ((is_rec, lbs1), uu____10178)  in
                           FStar_Syntax_Syntax.Tm_let uu____10165  in
                         FStar_All.pipe_left mk1 uu____10164  in
                       (uu____10161, aq))
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
              let uu____10256 =
                desugar_binding_pat_maybe_top top_level env pat is_mutable
                 in
              match uu____10256 with
              | (env1,binder,pat1) ->
                  let uu____10278 =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let uu____10304 = desugar_term_aq env1 t2  in
                        (match uu____10304 with
                         | (body1,aq) ->
                             let fv =
                               let uu____10318 =
                                 FStar_Syntax_Util.incr_delta_qualifier t12
                                  in
                               FStar_Syntax_Syntax.lid_as_fv l uu____10318
                                 FStar_Pervasives_Native.None
                                in
                             let uu____10319 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t12,
                                            (t12.FStar_Syntax_Syntax.pos))]),
                                      body1))
                                in
                             (uu____10319, aq))
                    | LocalBinder (x,uu____10349) ->
                        let uu____10350 = desugar_term_aq env1 t2  in
                        (match uu____10350 with
                         | (body1,aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | {
                                   FStar_Syntax_Syntax.v =
                                     FStar_Syntax_Syntax.Pat_wild uu____10364;
                                   FStar_Syntax_Syntax.p = uu____10365;_}::[]
                                   -> body1
                               | uu____10366 ->
                                   let uu____10369 =
                                     let uu____10376 =
                                       let uu____10377 =
                                         let uu____10400 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         let uu____10403 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1
                                            in
                                         (uu____10400, uu____10403)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____10377
                                        in
                                     FStar_Syntax_Syntax.mk uu____10376  in
                                   uu____10369 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range
                                in
                             let uu____10443 =
                               let uu____10446 =
                                 let uu____10447 =
                                   let uu____10460 =
                                     let uu____10463 =
                                       let uu____10464 =
                                         FStar_Syntax_Syntax.mk_binder x  in
                                       [uu____10464]  in
                                     FStar_Syntax_Subst.close uu____10463
                                       body2
                                      in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t12,
                                           (t12.FStar_Syntax_Syntax.pos))]),
                                     uu____10460)
                                    in
                                 FStar_Syntax_Syntax.Tm_let uu____10447  in
                               FStar_All.pipe_left mk1 uu____10446  in
                             (uu____10443, aq))
                     in
                  (match uu____10278 with
                   | (tm,aq) ->
                       if is_mutable
                       then
                         let uu____10521 =
                           FStar_All.pipe_left mk1
                             (FStar_Syntax_Syntax.Tm_meta
                                (tm,
                                  (FStar_Syntax_Syntax.Meta_desugared
                                     FStar_Syntax_Syntax.Mutable_alloc)))
                            in
                         (uu____10521, aq)
                       else (tm, aq))
               in
            let uu____10533 = FStar_List.hd lbs  in
            (match uu____10533 with
             | (attrs,(head_pat,defn)) ->
                 let uu____10577 = is_rec || (is_app_pattern head_pat)  in
                 if uu____10577
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____10590 =
                let uu____10591 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____10591  in
              mk1 uu____10590  in
            let uu____10592 = desugar_term_aq env t1  in
            (match uu____10592 with
             | (t1',aq1) ->
                 let uu____10603 = desugar_term_aq env t2  in
                 (match uu____10603 with
                  | (t2',aq2) ->
                      let uu____10614 = desugar_term_aq env t3  in
                      (match uu____10614 with
                       | (t3',aq3) ->
                           let uu____10625 =
                             let uu____10626 =
                               let uu____10627 =
                                 let uu____10650 =
                                   FStar_Syntax_Util.ascribe t1'
                                     ((FStar_Util.Inl t_bool1),
                                       FStar_Pervasives_Native.None)
                                    in
                                 let uu____10671 =
                                   let uu____10688 =
                                     let uu____10703 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t2.FStar_Parser_AST.range
                                        in
                                     (uu____10703,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____10716 =
                                     let uu____10733 =
                                       let uu____10748 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t3.FStar_Parser_AST.range
                                          in
                                       (uu____10748,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____10733]  in
                                   uu____10688 :: uu____10716  in
                                 (uu____10650, uu____10671)  in
                               FStar_Syntax_Syntax.Tm_match uu____10627  in
                             mk1 uu____10626  in
                           (uu____10625, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____10947 =
              match uu____10947 with
              | (pat,wopt,b) ->
                  let uu____10969 = desugar_match_pat env pat  in
                  (match uu____10969 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____11000 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____11000
                          in
                       let uu____11001 = desugar_term_aq env1 b  in
                       (match uu____11001 with
                        | (b1,aq) ->
                            let uu____11014 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____11014, aq)))
               in
            let uu____11019 = desugar_term_aq env e  in
            (match uu____11019 with
             | (e1,aq) ->
                 let uu____11030 =
                   let uu____11053 =
                     let uu____11078 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____11078 FStar_List.unzip  in
                   FStar_All.pipe_right uu____11053
                     (fun uu____11184  ->
                        match uu____11184 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____11030 with
                  | (brs,aqs) ->
                      let uu____11347 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____11347, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____11392 = is_comp_type env t  in
              if uu____11392
              then
                let uu____11401 = desugar_comp t.FStar_Parser_AST.range env t
                   in
                FStar_Util.Inr uu____11401
              else
                (let uu____11409 = desugar_term env t  in
                 FStar_Util.Inl uu____11409)
               in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)  in
            let uu____11419 = desugar_term_aq env e  in
            (match uu____11419 with
             | (e1,aq) ->
                 let uu____11430 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_ascribed
                        (e1, (annot, tac_opt1), FStar_Pervasives_Native.None))
                    in
                 (uu____11430, aq))
        | FStar_Parser_AST.Record (uu____11463,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____11504 = FStar_List.hd fields  in
              match uu____11504 with | (f,uu____11516) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____11562  ->
                        match uu____11562 with
                        | (g,uu____11568) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____11574,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____11588 =
                         let uu____11593 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____11593)
                          in
                       FStar_Errors.raise_error uu____11588
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
                  let uu____11601 =
                    let uu____11612 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____11643  ->
                              match uu____11643 with
                              | (f,uu____11653) ->
                                  let uu____11654 =
                                    let uu____11655 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____11655
                                     in
                                  (uu____11654, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____11612)  in
                  FStar_Parser_AST.Construct uu____11601
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____11673 =
                      let uu____11674 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____11674  in
                    FStar_Parser_AST.mk_term uu____11673
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____11676 =
                      let uu____11689 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____11719  ->
                                match uu____11719 with
                                | (f,uu____11729) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____11689)  in
                    FStar_Parser_AST.Record uu____11676  in
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
            let uu____11789 = desugar_term_aq env recterm1  in
            (match uu____11789 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____11805;
                         FStar_Syntax_Syntax.vars = uu____11806;_},args)
                      ->
                      let uu____11828 =
                        let uu____11829 =
                          let uu____11830 =
                            let uu____11845 =
                              let uu____11848 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____11849 =
                                let uu____11852 =
                                  let uu____11853 =
                                    let uu____11860 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____11860)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____11853
                                   in
                                FStar_Pervasives_Native.Some uu____11852  in
                              FStar_Syntax_Syntax.fvar uu____11848
                                FStar_Syntax_Syntax.delta_constant
                                uu____11849
                               in
                            (uu____11845, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____11830  in
                        FStar_All.pipe_left mk1 uu____11829  in
                      (uu____11828, s)
                  | uu____11887 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____11891 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____11891 with
              | (constrname,is_rec) ->
                  let uu____11906 = desugar_term_aq env e  in
                  (match uu____11906 with
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
                       let uu____11924 =
                         let uu____11925 =
                           let uu____11926 =
                             let uu____11941 =
                               let uu____11944 =
                                 let uu____11945 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____11945
                                  in
                               FStar_Syntax_Syntax.fvar uu____11944
                                 FStar_Syntax_Syntax.delta_equational qual
                                in
                             let uu____11946 =
                               let uu____11955 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____11955]  in
                             (uu____11941, uu____11946)  in
                           FStar_Syntax_Syntax.Tm_app uu____11926  in
                         FStar_All.pipe_left mk1 uu____11925  in
                       (uu____11924, s))))
        | FStar_Parser_AST.NamedTyp (uu____11984,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____11993 =
              let uu____11994 = FStar_Syntax_Subst.compress tm  in
              uu____11994.FStar_Syntax_Syntax.n  in
            (match uu____11993 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____12002 =
                   let uu___155_12003 =
                     let uu____12004 =
                       let uu____12005 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____12005  in
                     FStar_Syntax_Util.exp_string uu____12004  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___155_12003.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___155_12003.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____12002, noaqs)
             | uu____12006 ->
                 let uu____12007 =
                   let uu____12012 =
                     let uu____12013 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.strcat "VQuote, expected an fvar, got: "
                       uu____12013
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____12012)  in
                 FStar_Errors.raise_error uu____12007
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____12019 = desugar_term_aq env e  in
            (match uu____12019 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____12031 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____12031, noaqs))
        | FStar_Parser_AST.Antiquote (b,e) ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____12037 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____12038 =
              let uu____12039 =
                let uu____12048 = desugar_term env e  in (bv, b, uu____12048)
                 in
              [uu____12039]  in
            (uu____12037, uu____12038)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____12079 =
              let uu____12080 =
                let uu____12081 =
                  let uu____12088 = desugar_term env e  in (uu____12088, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____12081  in
              FStar_All.pipe_left mk1 uu____12080  in
            (uu____12079, noaqs)
        | uu____12093 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____12094 = desugar_formula env top  in
            (uu____12094, noaqs)
        | uu____12095 ->
            let uu____12096 =
              let uu____12101 =
                let uu____12102 = FStar_Parser_AST.term_to_string top  in
                Prims.strcat "Unexpected term: " uu____12102  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____12101)  in
            FStar_Errors.raise_error uu____12096 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____12108 -> false
    | uu____12117 -> true

and (is_synth_by_tactic :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (l,r,FStar_Parser_AST.Hash ) ->
          is_synth_by_tactic e l
      | FStar_Parser_AST.Var lid ->
          let uu____12123 =
            FStar_Syntax_DsEnv.resolve_to_fully_qualified_name e lid  in
          (match uu____12123 with
           | FStar_Pervasives_Native.Some lid1 ->
               FStar_Ident.lid_equals lid1 FStar_Parser_Const.synth_lid
           | FStar_Pervasives_Native.None  -> false)
      | uu____12127 -> false

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
           (fun uu____12164  ->
              match uu____12164 with
              | (a,imp) ->
                  let uu____12177 = desugar_term env a  in
                  arg_withimp_e imp uu____12177))

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
        let is_requires uu____12209 =
          match uu____12209 with
          | (t1,uu____12215) ->
              let uu____12216 =
                let uu____12217 = unparen t1  in
                uu____12217.FStar_Parser_AST.tm  in
              (match uu____12216 with
               | FStar_Parser_AST.Requires uu____12218 -> true
               | uu____12225 -> false)
           in
        let is_ensures uu____12235 =
          match uu____12235 with
          | (t1,uu____12241) ->
              let uu____12242 =
                let uu____12243 = unparen t1  in
                uu____12243.FStar_Parser_AST.tm  in
              (match uu____12242 with
               | FStar_Parser_AST.Ensures uu____12244 -> true
               | uu____12251 -> false)
           in
        let is_app head1 uu____12266 =
          match uu____12266 with
          | (t1,uu____12272) ->
              let uu____12273 =
                let uu____12274 = unparen t1  in
                uu____12274.FStar_Parser_AST.tm  in
              (match uu____12273 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____12276;
                      FStar_Parser_AST.level = uu____12277;_},uu____12278,uu____12279)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____12280 -> false)
           in
        let is_smt_pat uu____12290 =
          match uu____12290 with
          | (t1,uu____12296) ->
              let uu____12297 =
                let uu____12298 = unparen t1  in
                uu____12298.FStar_Parser_AST.tm  in
              (match uu____12297 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____12301);
                             FStar_Parser_AST.range = uu____12302;
                             FStar_Parser_AST.level = uu____12303;_},uu____12304)::uu____12305::[])
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
                             FStar_Parser_AST.range = uu____12344;
                             FStar_Parser_AST.level = uu____12345;_},uu____12346)::uu____12347::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
               | uu____12372 -> false)
           in
        let is_decreases = is_app "decreases"  in
        let pre_process_comp_typ t1 =
          let uu____12404 = head_and_args t1  in
          match uu____12404 with
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
                   let thunk_ens uu____12502 =
                     match uu____12502 with
                     | (e,i) ->
                         let uu____12513 = thunk_ens_ e  in (uu____12513, i)
                      in
                   let fail_lemma uu____12525 =
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
                         let uu____12605 =
                           let uu____12612 =
                             let uu____12619 = thunk_ens ens  in
                             [uu____12619; nil_pat]  in
                           req_true :: uu____12612  in
                         unit_tm :: uu____12605
                     | req::ens::[] when
                         (is_requires req) && (is_ensures ens) ->
                         let uu____12666 =
                           let uu____12673 =
                             let uu____12680 = thunk_ens ens  in
                             [uu____12680; nil_pat]  in
                           req :: uu____12673  in
                         unit_tm :: uu____12666
                     | ens::smtpat::[] when
                         (((let uu____12729 = is_requires ens  in
                            Prims.op_Negation uu____12729) &&
                             (let uu____12731 = is_smt_pat ens  in
                              Prims.op_Negation uu____12731))
                            &&
                            (let uu____12733 = is_decreases ens  in
                             Prims.op_Negation uu____12733))
                           && (is_smt_pat smtpat)
                         ->
                         let uu____12734 =
                           let uu____12741 =
                             let uu____12748 = thunk_ens ens  in
                             [uu____12748; smtpat]  in
                           req_true :: uu____12741  in
                         unit_tm :: uu____12734
                     | ens::dec::[] when
                         (is_ensures ens) && (is_decreases dec) ->
                         let uu____12795 =
                           let uu____12802 =
                             let uu____12809 = thunk_ens ens  in
                             [uu____12809; nil_pat; dec]  in
                           req_true :: uu____12802  in
                         unit_tm :: uu____12795
                     | ens::dec::smtpat::[] when
                         ((is_ensures ens) && (is_decreases dec)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____12869 =
                           let uu____12876 =
                             let uu____12883 = thunk_ens ens  in
                             [uu____12883; smtpat; dec]  in
                           req_true :: uu____12876  in
                         unit_tm :: uu____12869
                     | req::ens::dec::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_decreases dec)
                         ->
                         let uu____12943 =
                           let uu____12950 =
                             let uu____12957 = thunk_ens ens  in
                             [uu____12957; nil_pat; dec]  in
                           req :: uu____12950  in
                         unit_tm :: uu____12943
                     | req::ens::smtpat::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____13017 =
                           let uu____13024 =
                             let uu____13031 = thunk_ens ens  in
                             [uu____13031; smtpat]  in
                           req :: uu____13024  in
                         unit_tm :: uu____13017
                     | req::ens::dec::smtpat::[] when
                         (((is_requires req) && (is_ensures ens)) &&
                            (is_smt_pat smtpat))
                           && (is_decreases dec)
                         ->
                         let uu____13096 =
                           let uu____13103 =
                             let uu____13110 = thunk_ens ens  in
                             [uu____13110; dec; smtpat]  in
                           req :: uu____13103  in
                         unit_tm :: uu____13096
                     | _other -> fail_lemma ()  in
                   let head_and_attributes =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) lemma
                      in
                   (head_and_attributes, args1)
               | FStar_Parser_AST.Name l when
                   FStar_Syntax_DsEnv.is_effect_name env l ->
                   let uu____13172 =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) l
                      in
                   (uu____13172, args)
               | FStar_Parser_AST.Name l when
                   (let uu____13200 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____13200
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   let uu____13201 =
                     let uu____13208 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_Tot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____13208, [])  in
                   (uu____13201, args)
               | FStar_Parser_AST.Name l when
                   (let uu____13226 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____13226
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                   ->
                   let uu____13227 =
                     let uu____13234 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_GTot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____13234, [])  in
                   (uu____13227, args)
               | FStar_Parser_AST.Name l when
                   (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                      ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                     || ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                   ->
                   let uu____13250 =
                     let uu____13257 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_Tot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____13257, [])  in
                   (uu____13250, [(t1, FStar_Parser_AST.Nothing)])
               | uu____13280 ->
                   let default_effect =
                     let uu____13282 = FStar_Options.ml_ish ()  in
                     if uu____13282
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____13285 =
                           FStar_Options.warn_default_effects ()  in
                         if uu____13285
                         then
                           FStar_Errors.log_issue
                             head1.FStar_Parser_AST.range
                             (FStar_Errors.Warning_UseDefaultEffect,
                               "Using default effect Tot")
                         else ());
                        FStar_Parser_Const.effect_Tot_lid)
                      in
                   let uu____13287 =
                     let uu____13294 =
                       FStar_Ident.set_lid_range default_effect
                         head1.FStar_Parser_AST.range
                        in
                     (uu____13294, [])  in
                   (uu____13287, [(t1, FStar_Parser_AST.Nothing)]))
           in
        let uu____13317 = pre_process_comp_typ t  in
        match uu____13317 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____13367 =
                  let uu____13372 =
                    let uu____13373 = FStar_Syntax_Print.lid_to_string eff
                       in
                    FStar_Util.format1 "Not enough args to effect %s"
                      uu____13373
                     in
                  (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____13372)  in
                fail1 uu____13367)
             else ();
             (let is_universe uu____13384 =
                match uu____13384 with
                | (uu____13389,imp) -> imp = FStar_Parser_AST.UnivApp  in
              let uu____13391 = FStar_Util.take is_universe args  in
              match uu____13391 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____13450  ->
                         match uu____13450 with
                         | (u,imp) -> desugar_universe u) universes
                     in
                  let uu____13457 =
                    let uu____13472 = FStar_List.hd args1  in
                    let uu____13481 = FStar_List.tl args1  in
                    (uu____13472, uu____13481)  in
                  (match uu____13457 with
                   | (result_arg,rest) ->
                       let result_typ =
                         desugar_typ env
                           (FStar_Pervasives_Native.fst result_arg)
                          in
                       let rest1 = desugar_args env rest  in
                       let uu____13536 =
                         let is_decrease uu____13574 =
                           match uu____13574 with
                           | (t1,uu____13584) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.pos = uu____13594;
                                       FStar_Syntax_Syntax.vars = uu____13595;_},uu____13596::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.decreases_lid
                                | uu____13627 -> false)
                            in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease)
                          in
                       (match uu____13536 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____13743  ->
                                      match uu____13743 with
                                      | (t1,uu____13753) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____13762,(arg,uu____13764)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____13793 -> failwith "impos")))
                               in
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
                                | uu____13810 -> false  in
                              (((is_empty decreases_clause) &&
                                  (is_empty rest2))
                                 && (is_empty cattributes))
                                && (is_empty universes1)
                               in
                            let uu____13821 =
                              no_additional_args &&
                                (FStar_Ident.lid_equals eff
                                   FStar_Parser_Const.effect_Tot_lid)
                               in
                            if uu____13821
                            then FStar_Syntax_Syntax.mk_Total result_typ
                            else
                              (let uu____13825 =
                                 no_additional_args &&
                                   (FStar_Ident.lid_equals eff
                                      FStar_Parser_Const.effect_GTot_lid)
                                  in
                               if uu____13825
                               then FStar_Syntax_Syntax.mk_GTotal result_typ
                               else
                                 (let flags1 =
                                    let uu____13832 =
                                      FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_Lemma_lid
                                       in
                                    if uu____13832
                                    then [FStar_Syntax_Syntax.LEMMA]
                                    else
                                      (let uu____13836 =
                                         FStar_Ident.lid_equals eff
                                           FStar_Parser_Const.effect_Tot_lid
                                          in
                                       if uu____13836
                                       then [FStar_Syntax_Syntax.TOTAL]
                                       else
                                         (let uu____13840 =
                                            FStar_Ident.lid_equals eff
                                              FStar_Parser_Const.effect_ML_lid
                                             in
                                          if uu____13840
                                          then [FStar_Syntax_Syntax.MLEFFECT]
                                          else
                                            (let uu____13844 =
                                               FStar_Ident.lid_equals eff
                                                 FStar_Parser_Const.effect_GTot_lid
                                                in
                                             if uu____13844
                                             then
                                               [FStar_Syntax_Syntax.SOMETRIVIAL]
                                             else [])))
                                     in
                                  let flags2 =
                                    FStar_List.append flags1 cattributes  in
                                  let rest3 =
                                    let uu____13860 =
                                      FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_Lemma_lid
                                       in
                                    if uu____13860
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
                                                  let uu____13945 =
                                                    FStar_Ident.set_lid_range
                                                      FStar_Parser_Const.pattern_lid
                                                      pat.FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_Syntax.fvar
                                                    uu____13945
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
                                            | uu____13960 -> pat  in
                                          let uu____13961 =
                                            let uu____13972 =
                                              let uu____13983 =
                                                let uu____13992 =
                                                  FStar_Syntax_Syntax.mk
                                                    (FStar_Syntax_Syntax.Tm_meta
                                                       (pat1,
                                                         (FStar_Syntax_Syntax.Meta_desugared
                                                            FStar_Syntax_Syntax.Meta_smt_pat)))
                                                    FStar_Pervasives_Native.None
                                                    pat1.FStar_Syntax_Syntax.pos
                                                   in
                                                (uu____13992, aq)  in
                                              [uu____13983]  in
                                            ens :: uu____13972  in
                                          req :: uu____13961
                                      | uu____14033 -> rest2
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
        | uu____14057 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___156_14078 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___156_14078.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___156_14078.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___157_14120 = b  in
             {
               FStar_Parser_AST.b = (uu___157_14120.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___157_14120.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___157_14120.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____14183 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____14183)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____14196 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____14196 with
             | (env1,a1) ->
                 let a2 =
                   let uu___158_14206 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___158_14206.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___158_14206.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____14232 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____14246 =
                     let uu____14249 =
                       let uu____14250 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____14250]  in
                     no_annot_abs uu____14249 body2  in
                   FStar_All.pipe_left setpos uu____14246  in
                 let uu____14265 =
                   let uu____14266 =
                     let uu____14281 =
                       let uu____14284 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____14284
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____14285 =
                       let uu____14294 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____14294]  in
                     (uu____14281, uu____14285)  in
                   FStar_Syntax_Syntax.Tm_app uu____14266  in
                 FStar_All.pipe_left mk1 uu____14265)
        | uu____14325 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____14405 = q (rest, pats, body)  in
              let uu____14412 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____14405 uu____14412
                FStar_Parser_AST.Formula
               in
            let uu____14413 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____14413 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____14422 -> failwith "impossible"  in
      let uu____14425 =
        let uu____14426 = unparen f  in uu____14426.FStar_Parser_AST.tm  in
      match uu____14425 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____14433,uu____14434) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____14445,uu____14446) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____14477 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____14477
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____14513 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____14513
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____14556 -> desugar_term env f

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
      let uu____14561 =
        FStar_List.fold_left
          (fun uu____14597  ->
             fun b  ->
               match uu____14597 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___159_14649 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___159_14649.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___159_14649.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___159_14649.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____14666 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____14666 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___160_14686 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___160_14686.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___160_14686.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____14703 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____14561 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

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
          let uu____14790 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____14790)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____14795 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____14795)
      | FStar_Parser_AST.TVariable x ->
          let uu____14799 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____14799)
      | FStar_Parser_AST.NoName t ->
          let uu____14803 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____14803)
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
               (fun uu___122_14842  ->
                  match uu___122_14842 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____14843 -> false))
           in
        let quals2 q =
          let uu____14856 =
            (let uu____14859 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____14859) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____14856
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____14873 = FStar_Ident.range_of_lid disc_name  in
                let uu____14874 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____14873;
                  FStar_Syntax_Syntax.sigquals = uu____14874;
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
            let uu____14913 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____14947  ->
                        match uu____14947 with
                        | (x,uu____14955) ->
                            let uu____14956 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____14956 with
                             | (field_name,uu____14964) ->
                                 let only_decl =
                                   ((let uu____14968 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____14968)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____14970 =
                                        let uu____14971 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____14971.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____14970)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____14987 =
                                       FStar_List.filter
                                         (fun uu___123_14991  ->
                                            match uu___123_14991 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____14992 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____14987
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___124_15005  ->
                                             match uu___124_15005 with
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____15006 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____15008 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____15008;
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____15013 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____15013
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          FStar_Syntax_Syntax.delta_equational
                                      else
                                        FStar_Syntax_Syntax.delta_equational
                                       in
                                    let lb =
                                      let uu____15018 =
                                        let uu____15023 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____15023  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____15018;
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
                                      let uu____15027 =
                                        let uu____15028 =
                                          let uu____15035 =
                                            let uu____15038 =
                                              let uu____15039 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____15039
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____15038]  in
                                          ((false, [lb]), uu____15035)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____15028
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____15027;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____14913 FStar_List.flatten
  
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
            (lid,uu____15083,t,uu____15085,n1,uu____15087) when
            let uu____15092 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____15092 ->
            let uu____15093 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____15093 with
             | (formals,uu____15109) ->
                 (match formals with
                  | [] -> []
                  | uu____15132 ->
                      let filter_records uu___125_15146 =
                        match uu___125_15146 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____15149,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____15161 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____15163 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____15163 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Syntax_Syntax.Data_ctor
                        | FStar_Pervasives_Native.Some q -> q  in
                      let iquals1 =
                        if
                          FStar_List.contains FStar_Syntax_Syntax.Abstract
                            iquals
                        then FStar_Syntax_Syntax.Private :: iquals
                        else iquals  in
                      let uu____15173 = FStar_Util.first_N n1 formals  in
                      (match uu____15173 with
                       | (uu____15196,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____15222 -> []
  
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
                    let uu____15292 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____15292
                    then
                      let uu____15295 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____15295
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____15298 =
                      let uu____15303 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____15303  in
                    let uu____15304 =
                      let uu____15307 = FStar_Syntax_Syntax.mk_Total k  in
                      FStar_Syntax_Util.arrow typars uu____15307  in
                    let uu____15310 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____15298;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____15304;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____15310;
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
          let tycon_id uu___126_15361 =
            match uu___126_15361 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____15363,uu____15364) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____15374,uu____15375,uu____15376) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____15386,uu____15387,uu____15388) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____15418,uu____15419,uu____15420) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____15464) ->
                let uu____15465 =
                  let uu____15466 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____15466  in
                FStar_Parser_AST.mk_term uu____15465 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____15468 =
                  let uu____15469 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____15469  in
                FStar_Parser_AST.mk_term uu____15468 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____15471) ->
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
              | uu____15502 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____15508 =
                     let uu____15509 =
                       let uu____15516 = binder_to_term b  in
                       (out, uu____15516, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____15509  in
                   FStar_Parser_AST.mk_term uu____15508
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___127_15528 =
            match uu___127_15528 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____15584  ->
                       match uu____15584 with
                       | (x,t,uu____15595) ->
                           let uu____15600 =
                             let uu____15601 =
                               let uu____15606 =
                                 FStar_Syntax_Util.mangle_field_name x  in
                               (uu____15606, t)  in
                             FStar_Parser_AST.Annotated uu____15601  in
                           FStar_Parser_AST.mk_binder uu____15600
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____15608 =
                    let uu____15609 =
                      let uu____15610 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____15610  in
                    FStar_Parser_AST.mk_term uu____15609
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____15608 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let uu____15614 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____15641  ->
                          match uu____15641 with
                          | (x,uu____15651,uu____15652) ->
                              FStar_Syntax_Util.unmangle_field_name x))
                   in
                ((FStar_Parser_AST.TyconVariant
                    (id1, parms, kopt,
                      [(constrName, (FStar_Pervasives_Native.Some constrTyp),
                         FStar_Pervasives_Native.None, false)])),
                  uu____15614)
            | uu____15705 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___128_15744 =
            match uu___128_15744 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____15768 = typars_of_binders _env binders  in
                (match uu____15768 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____15810 =
                         let uu____15811 =
                           let uu____15812 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____15812  in
                         FStar_Parser_AST.mk_term uu____15811
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____15810 binders  in
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
            | uu____15823 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____15871 =
              FStar_List.fold_left
                (fun uu____15911  ->
                   fun uu____15912  ->
                     match (uu____15911, uu____15912) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____16003 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____16003 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____15871 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____16116 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____16116
                | uu____16117 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____16125 = desugar_abstract_tc quals env [] tc  in
              (match uu____16125 with
               | (uu____16138,uu____16139,se,uu____16141) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____16144,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____16161 =
                                 let uu____16162 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____16162  in
                               if uu____16161
                               then
                                 let uu____16163 =
                                   let uu____16168 =
                                     let uu____16169 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____16169
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____16168)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____16163
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
                           | uu____16176 ->
                               let uu____16177 =
                                 let uu____16184 =
                                   let uu____16185 =
                                     let uu____16198 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____16198)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____16185
                                    in
                                 FStar_Syntax_Syntax.mk uu____16184  in
                               uu____16177 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___161_16212 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___161_16212.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___161_16212.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___161_16212.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____16213 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____16216 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____16216
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____16229 = typars_of_binders env binders  in
              (match uu____16229 with
               | (env',typars) ->
                   let k =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____16265 =
                           FStar_Util.for_some
                             (fun uu___129_16267  ->
                                match uu___129_16267 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____16268 -> false) quals
                            in
                         if uu____16265
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Util.ktype
                     | FStar_Pervasives_Native.Some k -> desugar_term env' k
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____16275 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___130_16279  ->
                               match uu___130_16279 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____16280 -> false))
                        in
                     if uu____16275
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____16289 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____16289
                     then
                       let uu____16292 =
                         let uu____16299 =
                           let uu____16300 = unparen t  in
                           uu____16300.FStar_Parser_AST.tm  in
                         match uu____16299 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____16321 =
                               match FStar_List.rev args with
                               | (last_arg,uu____16351)::args_rev ->
                                   let uu____16363 =
                                     let uu____16364 = unparen last_arg  in
                                     uu____16364.FStar_Parser_AST.tm  in
                                   (match uu____16363 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____16392 -> ([], args))
                               | uu____16401 -> ([], args)  in
                             (match uu____16321 with
                              | (cattributes,args1) ->
                                  let uu____16440 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____16440))
                         | uu____16451 -> (t, [])  in
                       match uu____16292 with
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
                                  (fun uu___131_16473  ->
                                     match uu___131_16473 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____16474 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____16481)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____16505 = tycon_record_as_variant trec  in
              (match uu____16505 with
               | (t,fs) ->
                   let uu____16522 =
                     let uu____16525 =
                       let uu____16526 =
                         let uu____16535 =
                           let uu____16538 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____16538  in
                         (uu____16535, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____16526  in
                     uu____16525 :: quals  in
                   desugar_tycon env d uu____16522 [t])
          | uu____16543::uu____16544 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____16711 = et  in
                match uu____16711 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____16936 ->
                         let trec = tc  in
                         let uu____16960 = tycon_record_as_variant trec  in
                         (match uu____16960 with
                          | (t,fs) ->
                              let uu____17019 =
                                let uu____17022 =
                                  let uu____17023 =
                                    let uu____17032 =
                                      let uu____17035 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____17035  in
                                    (uu____17032, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____17023
                                   in
                                uu____17022 :: quals1  in
                              collect_tcs uu____17019 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____17122 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____17122 with
                          | (env2,uu____17182,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____17331 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____17331 with
                          | (env2,uu____17391,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____17516 ->
                         failwith "Unrecognized mutual type definition")
                 in
              let uu____17563 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____17563 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___133_18074  ->
                             match uu___133_18074 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____18141,uu____18142);
                                    FStar_Syntax_Syntax.sigrng = uu____18143;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____18144;
                                    FStar_Syntax_Syntax.sigmeta = uu____18145;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____18146;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____18207 =
                                     typars_of_binders env1 binders  in
                                   match uu____18207 with
                                   | (env2,tpars1) ->
                                       let uu____18238 =
                                         push_tparams env2 tpars1  in
                                       (match uu____18238 with
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
                                 let uu____18271 =
                                   let uu____18292 =
                                     mk_typ_abbrev id1 uvs tpars k t1 
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____18292)
                                    in
                                 [uu____18271]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____18360);
                                    FStar_Syntax_Syntax.sigrng = uu____18361;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____18363;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____18364;_},constrs,tconstr,quals1)
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
                                 let uu____18462 = push_tparams env1 tpars
                                    in
                                 (match uu____18462 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____18539  ->
                                             match uu____18539 with
                                             | (x,uu____18553) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____18561 =
                                        let uu____18590 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____18704  ->
                                                  match uu____18704 with
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
                                                        let uu____18760 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____18760
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
                                                                uu___132_18771
                                                                 ->
                                                                match uu___132_18771
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____18783
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____18791 =
                                                        let uu____18812 =
                                                          let uu____18813 =
                                                            let uu____18814 =
                                                              let uu____18829
                                                                =
                                                                let uu____18830
                                                                  =
                                                                  let uu____18833
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____18833
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____18830
                                                                 in
                                                              (name, univs1,
                                                                uu____18829,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____18814
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____18813;
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
                                                          uu____18812)
                                                         in
                                                      (name, uu____18791)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____18590
                                         in
                                      (match uu____18561 with
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
                             | uu____19070 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____19202  ->
                             match uu____19202 with
                             | (name_doc,uu____19230,uu____19231) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____19311  ->
                             match uu____19311 with
                             | (uu____19332,uu____19333,se) -> se))
                      in
                   let uu____19363 =
                     let uu____19370 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____19370 rng
                      in
                   (match uu____19363 with
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
                               (fun uu____19436  ->
                                  match uu____19436 with
                                  | (uu____19459,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____19510,tps,k,uu____19513,constrs)
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
                                  | uu____19532 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____19549  ->
                                 match uu____19549 with
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
      let uu____19592 =
        FStar_List.fold_left
          (fun uu____19627  ->
             fun b  ->
               match uu____19627 with
               | (env1,binders1) ->
                   let uu____19671 = desugar_binder env1 b  in
                   (match uu____19671 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____19694 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____19694 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____19749 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____19592 with
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
          let uu____19850 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___134_19855  ->
                    match uu___134_19855 with
                    | FStar_Syntax_Syntax.Reflectable uu____19856 -> true
                    | uu____19857 -> false))
             in
          if uu____19850
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____19860 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____19860
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
      let uu____19892 = FStar_Syntax_Util.head_and_args at1  in
      match uu____19892 with
      | (hd1,args) ->
          let uu____19937 =
            let uu____19950 =
              let uu____19951 = FStar_Syntax_Subst.compress hd1  in
              uu____19951.FStar_Syntax_Syntax.n  in
            (uu____19950, args)  in
          (match uu____19937 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(a1,uu____19972)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.fail_errs_attr
               ->
               let uu____19997 =
                 let uu____20002 =
                   FStar_Syntax_Embeddings.e_list
                     FStar_Syntax_Embeddings.e_int
                    in
                 FStar_Syntax_Embeddings.unembed uu____20002 a1  in
               (match uu____19997 with
                | FStar_Pervasives_Native.Some [] ->
                    FStar_Errors.raise_error
                      (FStar_Errors.Error_EmptyFailErrs,
                        "Found ill-applied fail_errs, argument should be a non-empty list of integers")
                      at1.FStar_Syntax_Syntax.pos
                | FStar_Pervasives_Native.Some es ->
                    let uu____20032 =
                      let uu____20039 =
                        FStar_List.map FStar_BigInt.to_int_fs es  in
                      (uu____20039, false)  in
                    FStar_Pervasives_Native.Some uu____20032
                | FStar_Pervasives_Native.None  ->
                    (if warn
                     then
                       FStar_Errors.log_issue at1.FStar_Syntax_Syntax.pos
                         (FStar_Errors.Warning_UnappliedFail,
                           "Found ill-applied fail_errs, argument should be non-empty a list of integers")
                     else ();
                     FStar_Pervasives_Native.None))
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____20061) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.fail_errs_attr
               ->
               (if warn
                then
                  FStar_Errors.log_issue at1.FStar_Syntax_Syntax.pos
                    (FStar_Errors.Warning_UnappliedFail,
                      "Found unapplied fail_errs, did you forget to use parentheses?")
                else ();
                FStar_Pervasives_Native.None)
           | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr
               -> FStar_Pervasives_Native.Some ([], false)
           | (FStar_Syntax_Syntax.Tm_fvar fv,[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.fail_lax_attr
               -> FStar_Pervasives_Native.Some ([], true)
           | uu____20132 -> FStar_Pervasives_Native.None)
  
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
                  let uu____20287 = desugar_binders monad_env eff_binders  in
                  match uu____20287 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let for_free =
                        let uu____20326 =
                          let uu____20328 =
                            let uu____20335 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____20335  in
                          FStar_List.length uu____20328  in
                        uu____20326 = (Prims.parse_int "1")  in
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
                            (uu____20376,(FStar_Parser_AST.TyconAbbrev
                                          (name,uu____20378,uu____20379,uu____20380),uu____20381)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____20414 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____20415 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____20427 = name_of_eff_decl decl  in
                             FStar_List.mem uu____20427 mandatory_members)
                          eff_decls
                         in
                      (match uu____20415 with
                       | (mandatory_members_decls,actions) ->
                           let uu____20444 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____20473  ->
                                     fun decl  ->
                                       match uu____20473 with
                                       | (env2,out) ->
                                           let uu____20493 =
                                             desugar_decl env2 decl  in
                                           (match uu____20493 with
                                            | (env3,ses) ->
                                                let uu____20506 =
                                                  let uu____20509 =
                                                    FStar_List.hd ses  in
                                                  uu____20509 :: out  in
                                                (env3, uu____20506)))
                                  (env1, []))
                              in
                           (match uu____20444 with
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
                                              (uu____20577,(FStar_Parser_AST.TyconAbbrev
                                                            (name,action_params,uu____20580,
                                                             {
                                                               FStar_Parser_AST.tm
                                                                 =
                                                                 FStar_Parser_AST.Construct
                                                                 (uu____20581,
                                                                  (def,uu____20583)::
                                                                  (cps_type,uu____20585)::[]);
                                                               FStar_Parser_AST.range
                                                                 =
                                                                 uu____20586;
                                                               FStar_Parser_AST.level
                                                                 =
                                                                 uu____20587;_}),doc1)::[])
                                              when Prims.op_Negation for_free
                                              ->
                                              let uu____20639 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____20639 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____20677 =
                                                     let uu____20678 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____20679 =
                                                       let uu____20680 =
                                                         desugar_term env3
                                                           def
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____20680
                                                        in
                                                     let uu____20685 =
                                                       let uu____20686 =
                                                         desugar_typ env3
                                                           cps_type
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____20686
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____20678;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____20679;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____20685
                                                     }  in
                                                   (uu____20677, doc1))
                                          | FStar_Parser_AST.Tycon
                                              (uu____20693,(FStar_Parser_AST.TyconAbbrev
                                                            (name,action_params,uu____20696,defn),doc1)::[])
                                              when for_free ->
                                              let uu____20731 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____20731 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____20769 =
                                                     let uu____20770 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____20771 =
                                                       let uu____20772 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____20772
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____20770;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____20771;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____20769, doc1))
                                          | uu____20779 ->
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
                                    let uu____20811 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____20811
                                     in
                                  let uu____20812 =
                                    let uu____20813 =
                                      FStar_Syntax_DsEnv.fail_or env2
                                        (FStar_Syntax_DsEnv.try_lookup_definition
                                           env2) l
                                       in
                                    FStar_All.pipe_left
                                      (FStar_Syntax_Subst.close binders1)
                                      uu____20813
                                     in
                                  ([], uu____20812)  in
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
                                      let uu____20830 =
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      ([], uu____20830)  in
                                    let uu____20837 =
                                      let uu____20838 =
                                        let uu____20839 =
                                          let uu____20840 = lookup1 "repr"
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____20840
                                           in
                                        let uu____20849 = lookup1 "return"
                                           in
                                        let uu____20850 = lookup1 "bind"  in
                                        let uu____20851 =
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
                                            uu____20839;
                                          FStar_Syntax_Syntax.return_repr =
                                            uu____20849;
                                          FStar_Syntax_Syntax.bind_repr =
                                            uu____20850;
                                          FStar_Syntax_Syntax.actions =
                                            actions1;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            uu____20851
                                        }  in
                                      FStar_Syntax_Syntax.Sig_new_effect_for_free
                                        uu____20838
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____20837;
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
                                         (fun uu___135_20857  ->
                                            match uu___135_20857 with
                                            | FStar_Syntax_Syntax.Reifiable 
                                                -> true
                                            | FStar_Syntax_Syntax.Reflectable
                                                uu____20858 -> true
                                            | uu____20859 -> false)
                                         qualifiers
                                        in
                                     let un_ts =
                                       ([], FStar_Syntax_Syntax.tun)  in
                                     let uu____20873 =
                                       let uu____20874 =
                                         let uu____20875 =
                                           lookup1 "return_wp"  in
                                         let uu____20876 = lookup1 "bind_wp"
                                            in
                                         let uu____20877 =
                                           lookup1 "if_then_else"  in
                                         let uu____20878 = lookup1 "ite_wp"
                                            in
                                         let uu____20879 = lookup1 "stronger"
                                            in
                                         let uu____20880 = lookup1 "close_wp"
                                            in
                                         let uu____20881 = lookup1 "assert_p"
                                            in
                                         let uu____20882 = lookup1 "assume_p"
                                            in
                                         let uu____20883 = lookup1 "null_wp"
                                            in
                                         let uu____20884 = lookup1 "trivial"
                                            in
                                         let uu____20885 =
                                           if rr
                                           then
                                             let uu____20886 = lookup1 "repr"
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.snd
                                               uu____20886
                                           else FStar_Syntax_Syntax.tun  in
                                         let uu____20902 =
                                           if rr
                                           then lookup1 "return"
                                           else un_ts  in
                                         let uu____20904 =
                                           if rr
                                           then lookup1 "bind"
                                           else un_ts  in
                                         let uu____20906 =
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
                                             uu____20875;
                                           FStar_Syntax_Syntax.bind_wp =
                                             uu____20876;
                                           FStar_Syntax_Syntax.if_then_else =
                                             uu____20877;
                                           FStar_Syntax_Syntax.ite_wp =
                                             uu____20878;
                                           FStar_Syntax_Syntax.stronger =
                                             uu____20879;
                                           FStar_Syntax_Syntax.close_wp =
                                             uu____20880;
                                           FStar_Syntax_Syntax.assert_p =
                                             uu____20881;
                                           FStar_Syntax_Syntax.assume_p =
                                             uu____20882;
                                           FStar_Syntax_Syntax.null_wp =
                                             uu____20883;
                                           FStar_Syntax_Syntax.trivial =
                                             uu____20884;
                                           FStar_Syntax_Syntax.repr =
                                             uu____20885;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____20902;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____20904;
                                           FStar_Syntax_Syntax.actions =
                                             actions1;
                                           FStar_Syntax_Syntax.eff_attrs =
                                             uu____20906
                                         }  in
                                       FStar_Syntax_Syntax.Sig_new_effect
                                         uu____20874
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         uu____20873;
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
                                          fun uu____20932  ->
                                            match uu____20932 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____20946 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____20946
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
                let uu____20970 = desugar_binders env1 eff_binders  in
                match uu____20970 with
                | (env2,binders) ->
                    let uu____21007 =
                      let uu____21026 = head_and_args defn  in
                      match uu____21026 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____21071 ->
                                let uu____21072 =
                                  let uu____21077 =
                                    let uu____21078 =
                                      let uu____21079 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.strcat uu____21079 " not found"
                                       in
                                    Prims.strcat "Effect " uu____21078  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____21077)
                                   in
                                FStar_Errors.raise_error uu____21072
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____21081 =
                            match FStar_List.rev args with
                            | (last_arg,uu____21111)::args_rev ->
                                let uu____21123 =
                                  let uu____21124 = unparen last_arg  in
                                  uu____21124.FStar_Parser_AST.tm  in
                                (match uu____21123 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____21152 -> ([], args))
                            | uu____21161 -> ([], args)  in
                          (match uu____21081 with
                           | (cattributes,args1) ->
                               let uu____21212 = desugar_args env2 args1  in
                               let uu____21221 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____21212, uu____21221))
                       in
                    (match uu____21007 with
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
                          (let uu____21277 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____21277 with
                           | (ed_binders,uu____21291,ed_binders_opening) ->
                               let sub1 uu____21304 =
                                 match uu____21304 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____21318 =
                                         FStar_Syntax_Subst.shift_subst
                                           (FStar_List.length us)
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____21318 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____21322 =
                                       let uu____21323 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____21323)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____21322
                                  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____21332 =
                                   let uu____21333 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____21333
                                    in
                                 let uu____21348 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____21349 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____21350 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____21351 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____21352 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____21353 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____21354 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____21355 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____21356 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____21357 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____21358 =
                                   let uu____21359 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____21359
                                    in
                                 let uu____21374 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____21375 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____21376 =
                                   FStar_List.map
                                     (fun action  ->
                                        let uu____21384 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____21385 =
                                          let uu____21386 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____21386
                                           in
                                        let uu____21401 =
                                          let uu____21402 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____21402
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____21384;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____21385;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____21401
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
                                     uu____21332;
                                   FStar_Syntax_Syntax.ret_wp = uu____21348;
                                   FStar_Syntax_Syntax.bind_wp = uu____21349;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____21350;
                                   FStar_Syntax_Syntax.ite_wp = uu____21351;
                                   FStar_Syntax_Syntax.stronger = uu____21352;
                                   FStar_Syntax_Syntax.close_wp = uu____21353;
                                   FStar_Syntax_Syntax.assert_p = uu____21354;
                                   FStar_Syntax_Syntax.assume_p = uu____21355;
                                   FStar_Syntax_Syntax.null_wp = uu____21356;
                                   FStar_Syntax_Syntax.trivial = uu____21357;
                                   FStar_Syntax_Syntax.repr = uu____21358;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____21374;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____21375;
                                   FStar_Syntax_Syntax.actions = uu____21376;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____21419 =
                                     let uu____21421 =
                                       let uu____21428 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____21428
                                        in
                                     FStar_List.length uu____21421  in
                                   uu____21419 = (Prims.parse_int "1")  in
                                 let uu____21454 =
                                   let uu____21457 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____21457 quals  in
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
                                   FStar_Syntax_Syntax.sigquals = uu____21454;
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
                                             let uu____21479 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____21479
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____21481 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____21481
                                 then
                                   let reflect_lid =
                                     let uu____21485 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____21485
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
    let uu____21495 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____21495 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.strcat "  " (Prims.strcat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____21546 ->
              let uu____21547 =
                let uu____21548 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____21548
                 in
              Prims.strcat "\n  " uu____21547
          | uu____21549 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____21562  ->
               match uu____21562 with
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
          let uu____21580 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____21580
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____21582 =
          let uu____21591 = FStar_Syntax_Syntax.as_arg arg  in [uu____21591]
           in
        FStar_Syntax_Util.mk_app fv uu____21582

and (desugar_decl :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      let uu____21616 = desugar_decl_noattrs env d  in
      match uu____21616 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____21634 = mk_comment_attr d  in uu____21634 :: attrs1  in
          let uu____21635 =
            FStar_List.mapi
              (fun i  ->
                 fun sigelt  ->
                   if i = (Prims.parse_int "0")
                   then
                     let uu___162_21641 = sigelt  in
                     {
                       FStar_Syntax_Syntax.sigel =
                         (uu___162_21641.FStar_Syntax_Syntax.sigel);
                       FStar_Syntax_Syntax.sigrng =
                         (uu___162_21641.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___162_21641.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___162_21641.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs = attrs2
                     }
                   else
                     (let uu___163_21643 = sigelt  in
                      let uu____21644 =
                        FStar_List.filter
                          (fun at1  ->
                             let uu____21650 = get_fail_attr false at1  in
                             FStar_Option.isNone uu____21650) attrs2
                         in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___163_21643.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___163_21643.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___163_21643.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___163_21643.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs = uu____21644
                      })) sigelts
             in
          (env1, uu____21635)

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
      | FStar_Parser_AST.Fsdoc uu____21690 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____21698 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____21698, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals  in
          let tcs1 =
            FStar_List.map
              (fun uu____21735  ->
                 match uu____21735 with | (x,uu____21743) -> x) tcs
             in
          let uu____21748 =
            FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals
             in
          desugar_tycon env d uu____21748 tcs1
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals  in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____21770;
                    FStar_Parser_AST.prange = uu____21771;_},uu____21772)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____21781;
                    FStar_Parser_AST.prange = uu____21782;_},uu____21783)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____21798;
                         FStar_Parser_AST.prange = uu____21799;_},uu____21800);
                    FStar_Parser_AST.prange = uu____21801;_},uu____21802)::[]
                   -> false
               | (p,uu____21830)::[] ->
                   let uu____21839 = is_app_pattern p  in
                   Prims.op_Negation uu____21839
               | uu____21840 -> false)
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
            let uu____21913 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____21913 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____21925 =
                     let uu____21926 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____21926.FStar_Syntax_Syntax.n  in
                   match uu____21925 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____21936) ->
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
                         | uu____21969::uu____21970 ->
                             FStar_List.map
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____21973 ->
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.collect
                                  (fun uu___136_21988  ->
                                     match uu___136_21988 with
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inl uu____21991;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____21992;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____21993;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____21994;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____21995;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____21996;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____21997;_}
                                         -> []
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____22009;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____22010;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____22011;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____22012;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____22013;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____22014;_}
                                         ->
                                         FStar_Syntax_DsEnv.lookup_letbinding_quals
                                           env
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                          in
                       let quals2 =
                         let uu____22028 =
                           FStar_All.pipe_right lets1
                             (FStar_Util.for_some
                                (fun uu____22059  ->
                                   match uu____22059 with
                                   | (uu____22072,(uu____22073,t)) ->
                                       t.FStar_Parser_AST.level =
                                         FStar_Parser_AST.Formula))
                            in
                         if uu____22028
                         then FStar_Syntax_Syntax.Logic :: quals1
                         else quals1  in
                       let lbs1 =
                         let uu____22091 =
                           FStar_All.pipe_right quals2
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract)
                            in
                         if uu____22091
                         then
                           let uu____22094 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu___164_22108 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___165_22110 = fv  in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___165_22110.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___165_22110.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___164_22108.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___164_22108.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___164_22108.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___164_22108.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___164_22108.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___164_22108.FStar_Syntax_Syntax.lbpos)
                                     }))
                              in
                           ((FStar_Pervasives_Native.fst lbs), uu____22094)
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
                   | uu____22137 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____22143 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____22162 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____22143 with
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
                       let uu___166_22198 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___166_22198.FStar_Parser_AST.prange)
                       }
                   | uu____22205 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___167_22212 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___167_22212.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___167_22212.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___167_22212.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____22248 id1 =
                   match uu____22248 with
                   | (env1,ses) ->
                       let main =
                         let uu____22269 =
                           let uu____22270 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____22270  in
                         FStar_Parser_AST.mk_term uu____22269
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
                       let uu____22320 = desugar_decl env1 id_decl  in
                       (match uu____22320 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____22338 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____22338 FStar_Util.set_elements
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
            let uu____22363 = close_fun env t  in
            desugar_term env uu____22363  in
          let quals1 =
            let uu____22367 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____22367
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let se =
            let uu____22373 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____22373;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in
          let env2 =
            FStar_Syntax_DsEnv.push_doc env1 lid d.FStar_Parser_AST.doc  in
          (env2, [se])
      | FStar_Parser_AST.Exception (id1,FStar_Pervasives_Native.None ) ->
          let uu____22381 =
            FStar_Syntax_DsEnv.fail_or env
              (FStar_Syntax_DsEnv.try_lookup_lid env)
              FStar_Parser_Const.exn_lid
             in
          (match uu____22381 with
           | (t,uu____22395) ->
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
            let uu____22425 =
              let uu____22432 = FStar_Syntax_Syntax.null_binder t  in
              [uu____22432]  in
            let uu____22445 =
              let uu____22448 =
                let uu____22449 =
                  FStar_Syntax_DsEnv.fail_or env
                    (FStar_Syntax_DsEnv.try_lookup_lid env)
                    FStar_Parser_Const.exn_lid
                   in
                FStar_Pervasives_Native.fst uu____22449  in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____22448
               in
            FStar_Syntax_Util.arrow uu____22425 uu____22445  in
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
            let uu____22510 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____22510 with
            | FStar_Pervasives_Native.None  ->
                let uu____22513 =
                  let uu____22518 =
                    let uu____22519 =
                      let uu____22520 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.strcat uu____22520 " not found"  in
                    Prims.strcat "Effect name " uu____22519  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____22518)  in
                FStar_Errors.raise_error uu____22513
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____22524 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____22566 =
                  let uu____22575 =
                    let uu____22582 = desugar_term env t  in
                    ([], uu____22582)  in
                  FStar_Pervasives_Native.Some uu____22575  in
                (uu____22566, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____22615 =
                  let uu____22624 =
                    let uu____22631 = desugar_term env wp  in
                    ([], uu____22631)  in
                  FStar_Pervasives_Native.Some uu____22624  in
                let uu____22640 =
                  let uu____22649 =
                    let uu____22656 = desugar_term env t  in
                    ([], uu____22656)  in
                  FStar_Pervasives_Native.Some uu____22649  in
                (uu____22615, uu____22640)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____22682 =
                  let uu____22691 =
                    let uu____22698 = desugar_term env t  in
                    ([], uu____22698)  in
                  FStar_Pervasives_Native.Some uu____22691  in
                (FStar_Pervasives_Native.None, uu____22682)
             in
          (match uu____22524 with
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
            let uu____22776 =
              let uu____22777 =
                let uu____22784 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____22784, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____22777  in
            {
              FStar_Syntax_Syntax.sigel = uu____22776;
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
      let uu____22810 =
        FStar_List.fold_left
          (fun uu____22830  ->
             fun d  ->
               match uu____22830 with
               | (env1,sigelts) ->
                   let uu____22850 = desugar_decl env1 d  in
                   (match uu____22850 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____22810 with
      | (env1,sigelts) ->
          let rec forward acc uu___138_22895 =
            match uu___138_22895 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____22909,FStar_Syntax_Syntax.Sig_let uu____22910) ->
                     let uu____22923 =
                       let uu____22926 =
                         let uu___168_22927 = se2  in
                         let uu____22928 =
                           let uu____22931 =
                             FStar_List.filter
                               (fun uu___137_22945  ->
                                  match uu___137_22945 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____22949;
                                           FStar_Syntax_Syntax.vars =
                                             uu____22950;_},uu____22951);
                                      FStar_Syntax_Syntax.pos = uu____22952;
                                      FStar_Syntax_Syntax.vars = uu____22953;_}
                                      when
                                      let uu____22976 =
                                        let uu____22977 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____22977
                                         in
                                      uu____22976 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____22978 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____22931
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___168_22927.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___168_22927.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___168_22927.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___168_22927.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____22928
                         }  in
                       uu____22926 :: se1 :: acc  in
                     forward uu____22923 sigelts1
                 | uu____22983 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____22991 = forward [] sigelts  in (env1, uu____22991)
  
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
      let uu____23033 =
        let uu____23046 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____23063  ->
               match uu____23063 with
               | ({ FStar_Syntax_Syntax.ppname = uu____23072;
                    FStar_Syntax_Syntax.index = uu____23073;
                    FStar_Syntax_Syntax.sort = t;_},uu____23075)
                   ->
                   let uu____23078 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____23078) uu____23046
         in
      FStar_All.pipe_right bs uu____23033  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____23092 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____23109 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____23135 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____23156,uu____23157,bs,t,uu____23160,uu____23161)
                            ->
                            let uu____23170 = bs_univnames bs  in
                            let uu____23173 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____23170 uu____23173
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____23176,uu____23177,t,uu____23179,uu____23180,uu____23181)
                            -> FStar_Syntax_Free.univnames t
                        | uu____23186 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____23135 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___169_23194 = s  in
        let uu____23195 =
          let uu____23196 =
            let uu____23205 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____23223,bs,t,lids1,lids2) ->
                          let uu___170_23236 = se  in
                          let uu____23237 =
                            let uu____23238 =
                              let uu____23255 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____23256 =
                                let uu____23257 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____23257 t  in
                              (lid, uvs, uu____23255, uu____23256, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____23238
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____23237;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___170_23236.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___170_23236.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___170_23236.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___170_23236.FStar_Syntax_Syntax.sigattrs)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____23269,t,tlid,n1,lids1) ->
                          let uu___171_23278 = se  in
                          let uu____23279 =
                            let uu____23280 =
                              let uu____23295 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____23295, tlid, n1, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____23280  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____23279;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___171_23278.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___171_23278.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___171_23278.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___171_23278.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____23298 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____23205, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____23196  in
        {
          FStar_Syntax_Syntax.sigel = uu____23195;
          FStar_Syntax_Syntax.sigrng =
            (uu___169_23194.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___169_23194.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___169_23194.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___169_23194.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____23304,t) ->
        let uvs =
          let uu____23307 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____23307 FStar_Util.set_elements  in
        let uu___172_23312 = s  in
        let uu____23313 =
          let uu____23314 =
            let uu____23321 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____23321)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____23314  in
        {
          FStar_Syntax_Syntax.sigel = uu____23313;
          FStar_Syntax_Syntax.sigrng =
            (uu___172_23312.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___172_23312.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___172_23312.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___172_23312.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____23343 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____23346 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____23353) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____23382,(FStar_Util.Inl t,uu____23384),uu____23385)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____23432,(FStar_Util.Inr c,uu____23434),uu____23435)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____23482 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____23483,(FStar_Util.Inl t,uu____23485),uu____23486) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____23533,(FStar_Util.Inr c,uu____23535),uu____23536) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____23583 -> empty_set  in
          FStar_Util.set_union uu____23343 uu____23346  in
        let all_lb_univs =
          let uu____23587 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____23603 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____23603) empty_set)
             in
          FStar_All.pipe_right uu____23587 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___173_23613 = s  in
        let uu____23614 =
          let uu____23615 =
            let uu____23622 =
              let uu____23623 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___174_23635 = lb  in
                        let uu____23636 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____23639 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___174_23635.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____23636;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___174_23635.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____23639;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___174_23635.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___174_23635.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____23623)  in
            (uu____23622, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____23615  in
        {
          FStar_Syntax_Syntax.sigel = uu____23614;
          FStar_Syntax_Syntax.sigrng =
            (uu___173_23613.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___173_23613.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___173_23613.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___173_23613.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____23647,fml) ->
        let uvs =
          let uu____23650 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____23650 FStar_Util.set_elements  in
        let uu___175_23655 = s  in
        let uu____23656 =
          let uu____23657 =
            let uu____23664 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____23664)  in
          FStar_Syntax_Syntax.Sig_assume uu____23657  in
        {
          FStar_Syntax_Syntax.sigel = uu____23656;
          FStar_Syntax_Syntax.sigrng =
            (uu___175_23655.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___175_23655.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___175_23655.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___175_23655.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____23666,bs,c,flags1) ->
        let uvs =
          let uu____23675 =
            let uu____23678 = bs_univnames bs  in
            let uu____23681 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____23678 uu____23681  in
          FStar_All.pipe_right uu____23675 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___176_23689 = s  in
        let uu____23690 =
          let uu____23691 =
            let uu____23704 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____23705 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____23704, uu____23705, flags1)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____23691  in
        {
          FStar_Syntax_Syntax.sigel = uu____23690;
          FStar_Syntax_Syntax.sigrng =
            (uu___176_23689.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___176_23689.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___176_23689.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___176_23689.FStar_Syntax_Syntax.sigattrs)
        }
    | uu____23708 -> s
  
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
          | (FStar_Pervasives_Native.None ,uu____23743) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____23747;
               FStar_Syntax_Syntax.exports = uu____23748;
               FStar_Syntax_Syntax.is_interface = uu____23749;_},FStar_Parser_AST.Module
             (current_lid,uu____23751)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____23759) ->
              let uu____23762 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____23762
           in
        let uu____23767 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____23803 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____23803, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____23820 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____23820, mname, decls, false)
           in
        match uu____23767 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____23850 = desugar_decls env2 decls  in
            (match uu____23850 with
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
          let uu____23915 =
            (FStar_Options.interactive ()) &&
              (let uu____23917 =
                 let uu____23918 =
                   let uu____23919 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____23919  in
                 FStar_Util.get_file_extension uu____23918  in
               FStar_List.mem uu____23917 ["fsti"; "fsi"])
             in
          if uu____23915 then as_interface m else m  in
        let uu____23923 = desugar_modul_common curmod env m1  in
        match uu____23923 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____23941 = FStar_Syntax_DsEnv.pop ()  in
              (uu____23941, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul ->
      (env_t,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun m  ->
      let uu____23961 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____23961 with
      | (env1,modul,pop_when_done) ->
          let uu____23975 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____23975 with
           | (env2,modul1) ->
               ((let uu____23987 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____23987
                 then
                   let uu____23988 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____23988
                 else ());
                (let uu____23990 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____23990, modul1))))
  
let (ast_modul_to_modul :
  FStar_Parser_AST.modul ->
    FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun env  ->
      let uu____24008 = desugar_modul env modul  in
      match uu____24008 with | (env1,modul1) -> (modul1, env1)
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      let uu____24039 = desugar_decls env decls  in
      match uu____24039 with | (env1,sigelts) -> (sigelts, env1)
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        let uu____24081 = desugar_partial_modul modul env a_modul  in
        match uu____24081 with | (env1,modul1) -> (modul1, env1)
  
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
              | uu____24167 ->
                  let t =
                    let uu____24175 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____24175  in
                  let uu____24186 =
                    let uu____24187 = FStar_Syntax_Subst.compress t  in
                    uu____24187.FStar_Syntax_Syntax.n  in
                  (match uu____24186 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____24197,uu____24198)
                       -> bs1
                   | uu____24219 -> failwith "Impossible")
               in
            let uu____24226 =
              let uu____24233 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____24233
                FStar_Syntax_Syntax.t_unit
               in
            match uu____24226 with
            | (binders,uu____24235,binders_opening) ->
                let erase_term t =
                  let uu____24243 =
                    let uu____24244 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____24244  in
                  FStar_Syntax_Subst.close binders uu____24243  in
                let erase_tscheme uu____24262 =
                  match uu____24262 with
                  | (us,t) ->
                      let t1 =
                        let uu____24282 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____24282 t  in
                      let uu____24285 =
                        let uu____24286 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____24286  in
                      ([], uu____24285)
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
                    | uu____24305 ->
                        let bs =
                          let uu____24313 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____24313  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____24345 =
                          let uu____24346 =
                            let uu____24349 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____24349  in
                          uu____24346.FStar_Syntax_Syntax.n  in
                        (match uu____24345 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____24351,uu____24352) -> bs1
                         | uu____24373 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____24380 =
                      let uu____24381 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____24381  in
                    FStar_Syntax_Subst.close binders uu____24380  in
                  let uu___177_24382 = action  in
                  let uu____24383 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____24384 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___177_24382.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___177_24382.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____24383;
                    FStar_Syntax_Syntax.action_typ = uu____24384
                  }  in
                let uu___178_24385 = ed  in
                let uu____24386 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____24387 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____24388 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____24389 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____24390 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____24391 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____24392 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____24393 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____24394 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____24395 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____24396 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____24397 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____24398 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____24399 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____24400 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____24401 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___178_24385.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___178_24385.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____24386;
                  FStar_Syntax_Syntax.signature = uu____24387;
                  FStar_Syntax_Syntax.ret_wp = uu____24388;
                  FStar_Syntax_Syntax.bind_wp = uu____24389;
                  FStar_Syntax_Syntax.if_then_else = uu____24390;
                  FStar_Syntax_Syntax.ite_wp = uu____24391;
                  FStar_Syntax_Syntax.stronger = uu____24392;
                  FStar_Syntax_Syntax.close_wp = uu____24393;
                  FStar_Syntax_Syntax.assert_p = uu____24394;
                  FStar_Syntax_Syntax.assume_p = uu____24395;
                  FStar_Syntax_Syntax.null_wp = uu____24396;
                  FStar_Syntax_Syntax.trivial = uu____24397;
                  FStar_Syntax_Syntax.repr = uu____24398;
                  FStar_Syntax_Syntax.return_repr = uu____24399;
                  FStar_Syntax_Syntax.bind_repr = uu____24400;
                  FStar_Syntax_Syntax.actions = uu____24401;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___178_24385.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___179_24417 = se  in
                  let uu____24418 =
                    let uu____24419 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____24419  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____24418;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___179_24417.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___179_24417.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___179_24417.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___179_24417.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___180_24423 = se  in
                  let uu____24424 =
                    let uu____24425 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____24425
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____24424;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___180_24423.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___180_24423.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___180_24423.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___180_24423.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____24427 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____24428 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____24428 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____24440 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____24440
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____24442 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____24442)
  