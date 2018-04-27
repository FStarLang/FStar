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
                let uu____346 = FStar_Options.ml_ish ()  in
                if uu____346
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
  fun uu___88_1710  ->
    match uu___88_1710 with
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
      fun uu___89_1756  ->
        match uu___89_1756 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____1784 = FStar_Syntax_Syntax.null_binder k  in
            (uu____1784, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____1793 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____1793 with
             | (env1,a1) ->
                 (((let uu___113_1819 = a1  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___113_1819.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___113_1819.FStar_Syntax_Syntax.index);
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
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
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
              FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
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
                  FStar_Syntax_Syntax.Delta_constant
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
  fun uu___90_2175  ->
    match uu___90_2175 with
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
                  (fun uu___91_2388  ->
                     match uu___91_2388 with
                     | FStar_Util.Inr uu____2393 -> true
                     | uu____2394 -> false) univargs
              then
                let uu____2399 =
                  let uu____2400 =
                    FStar_List.map
                      (fun uu___92_2409  ->
                         match uu___92_2409 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____2400  in
                FStar_Util.Inr uu____2399
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___93_2426  ->
                        match uu___93_2426 with
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
                           let uu___114_3385 = p4  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var
                                  (let uu___115_3390 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___115_3390.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___115_3390.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }));
                             FStar_Syntax_Syntax.p =
                               (uu___114_3385.FStar_Syntax_Syntax.p)
                           }
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let uu___116_3392 = p4  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild
                                  (let uu___117_3397 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___117_3397.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___117_3397.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }));
                             FStar_Syntax_Syntax.p =
                               (uu___116_3392.FStar_Syntax_Syntax.p)
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
                                  ((let uu___118_3454 = x  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___118_3454.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___118_3454.FStar_Syntax_Syntax.index);
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
                                FStar_Syntax_Syntax.Delta_constant
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
                                     FStar_Syntax_Syntax.Delta_constant
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
                                let uu___119_4555 = fv  in
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
                                    (uu___119_4555.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___119_4555.FStar_Syntax_Syntax.fv_delta);
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
                           let uu___120_5192 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___120_5192.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___120_5192.FStar_Syntax_Syntax.vars)
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
          let uu___121_5563 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___121_5563.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___121_5563.FStar_Syntax_Syntax.vars)
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
                        let uu____5769 = desugar_typ_aq env t  in
                        match uu____5769 with
                        | (t',aq) ->
                            let uu____5780 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____5780, aq)))
                 in
              FStar_All.pipe_right uu____5708 FStar_List.unzip  in
            (match uu____5683 with
             | (targs,aqs) ->
                 let uu____5889 =
                   let uu____5894 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____5894
                    in
                 (match uu____5889 with
                  | (tup,uu____5910) ->
                      let uu____5911 =
                        mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                      (uu____5911, (join_aqs aqs))))
        | FStar_Parser_AST.Tvar a ->
            let uu____5923 =
              let uu____5924 =
                let uu____5927 =
                  FStar_Syntax_DsEnv.fail_or2
                    (FStar_Syntax_DsEnv.try_lookup_id env) a
                   in
                FStar_Pervasives_Native.fst uu____5927  in
              FStar_All.pipe_left setpos uu____5924  in
            (uu____5923, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____5939 =
              let uu____5944 =
                let uu____5945 =
                  let uu____5946 = FStar_Ident.text_of_id u  in
                  Prims.strcat uu____5946 " in non-universe context"  in
                Prims.strcat "Unexpected universe variable " uu____5945  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____5944)  in
            FStar_Errors.raise_error uu____5939 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____5957 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____5957 with
             | FStar_Pervasives_Native.None  ->
                 let uu____5964 =
                   let uu____5969 =
                     let uu____5970 = FStar_Ident.text_of_id s  in
                     Prims.strcat "Unexpected or unbound operator: "
                       uu____5970
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____5969)
                    in
                 FStar_Errors.raise_error uu____5964
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let uu____5980 =
                     let uu____6005 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____6067 = desugar_term_aq env t  in
                               match uu____6067 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____6005 FStar_List.unzip  in
                   (match uu____5980 with
                    | (args1,aqs) ->
                        let uu____6200 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____6200, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____6214)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____6229 =
              let uu___122_6230 = top  in
              let uu____6231 =
                let uu____6232 =
                  let uu____6239 =
                    let uu___123_6240 = top  in
                    let uu____6241 =
                      let uu____6242 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____6242  in
                    {
                      FStar_Parser_AST.tm = uu____6241;
                      FStar_Parser_AST.range =
                        (uu___123_6240.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___123_6240.FStar_Parser_AST.level)
                    }  in
                  (uu____6239, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____6232  in
              {
                FStar_Parser_AST.tm = uu____6231;
                FStar_Parser_AST.range =
                  (uu___122_6230.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___122_6230.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____6229
        | FStar_Parser_AST.Construct (n1,(a,uu____6245)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____6261 =
                let uu___124_6262 = top  in
                let uu____6263 =
                  let uu____6264 =
                    let uu____6271 =
                      let uu___125_6272 = top  in
                      let uu____6273 =
                        let uu____6274 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____6274  in
                      {
                        FStar_Parser_AST.tm = uu____6273;
                        FStar_Parser_AST.range =
                          (uu___125_6272.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___125_6272.FStar_Parser_AST.level)
                      }  in
                    (uu____6271, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____6264  in
                {
                  FStar_Parser_AST.tm = uu____6263;
                  FStar_Parser_AST.range =
                    (uu___124_6262.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___124_6262.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____6261))
        | FStar_Parser_AST.Construct (n1,(a,uu____6277)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____6292 =
              let uu___126_6293 = top  in
              let uu____6294 =
                let uu____6295 =
                  let uu____6302 =
                    let uu___127_6303 = top  in
                    let uu____6304 =
                      let uu____6305 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____6305  in
                    {
                      FStar_Parser_AST.tm = uu____6304;
                      FStar_Parser_AST.range =
                        (uu___127_6303.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___127_6303.FStar_Parser_AST.level)
                    }  in
                  (uu____6302, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____6295  in
              {
                FStar_Parser_AST.tm = uu____6294;
                FStar_Parser_AST.range =
                  (uu___126_6293.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___126_6293.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____6292
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____6306; FStar_Ident.ident = uu____6307;
              FStar_Ident.nsstr = uu____6308; FStar_Ident.str = "Type0";_}
            ->
            let uu____6311 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____6311, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____6312; FStar_Ident.ident = uu____6313;
              FStar_Ident.nsstr = uu____6314; FStar_Ident.str = "Type";_}
            ->
            let uu____6317 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____6317, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____6318; FStar_Ident.ident = uu____6319;
               FStar_Ident.nsstr = uu____6320; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____6338 =
              let uu____6339 =
                let uu____6340 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____6340  in
              mk1 uu____6339  in
            (uu____6338, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____6341; FStar_Ident.ident = uu____6342;
              FStar_Ident.nsstr = uu____6343; FStar_Ident.str = "Effect";_}
            ->
            let uu____6346 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____6346, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____6347; FStar_Ident.ident = uu____6348;
              FStar_Ident.nsstr = uu____6349; FStar_Ident.str = "True";_}
            ->
            let uu____6352 =
              let uu____6353 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____6353
                FStar_Syntax_Syntax.Delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____6352, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____6354; FStar_Ident.ident = uu____6355;
              FStar_Ident.nsstr = uu____6356; FStar_Ident.str = "False";_}
            ->
            let uu____6359 =
              let uu____6360 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____6360
                FStar_Syntax_Syntax.Delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____6359, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____6363;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____6365 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____6365 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____6374 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_defined_at_level
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None
                     in
                  (uu____6374, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____6375 =
                    let uu____6376 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____6376 txt
                     in
                  failwith uu____6375))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____6383 = desugar_name mk1 setpos env true l  in
              (uu____6383, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____6386 = desugar_name mk1 setpos env true l  in
              (uu____6386, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____6397 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____6397 with
                | FStar_Pervasives_Native.Some uu____6406 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____6411 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____6411 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____6425 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____6442 =
                    let uu____6443 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____6443  in
                  (uu____6442, noaqs)
              | uu____6444 ->
                  let uu____6451 =
                    let uu____6456 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____6456)  in
                  FStar_Errors.raise_error uu____6451
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____6463 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____6463 with
              | FStar_Pervasives_Native.None  ->
                  let uu____6470 =
                    let uu____6475 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____6475)
                     in
                  FStar_Errors.raise_error uu____6470
                    top.FStar_Parser_AST.range
              | uu____6480 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____6484 = desugar_name mk1 setpos env true lid'  in
                  (uu____6484, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____6500 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____6500 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____6519 ->
                       let uu____6526 =
                         FStar_Util.take
                           (fun uu____6550  ->
                              match uu____6550 with
                              | (uu____6555,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____6526 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____6600 =
                              let uu____6625 =
                                FStar_List.map
                                  (fun uu____6668  ->
                                     match uu____6668 with
                                     | (t,imp) ->
                                         let uu____6685 =
                                           desugar_term_aq env t  in
                                         (match uu____6685 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____6625
                                FStar_List.unzip
                               in
                            (match uu____6600 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____6826 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____6826, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____6842 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____6842 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.strcat "Constructor "
                             (Prims.strcat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____6849 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.strcat "Effect "
                             (Prims.strcat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____6860 =
              FStar_List.fold_left
                (fun uu____6901  ->
                   fun b  ->
                     match uu____6901 with
                     | (env1,tparams,typs) ->
                         let uu____6950 = desugar_binder env1 b  in
                         (match uu____6950 with
                          | (xopt,t1) ->
                              let uu____6977 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____6986 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____6986)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____6977 with
                               | (env2,x) ->
                                   let uu____7004 =
                                     let uu____7007 =
                                       let uu____7010 =
                                         let uu____7011 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____7011
                                          in
                                       [uu____7010]  in
                                     FStar_List.append typs uu____7007  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___128_7035 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___128_7035.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___128_7035.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____7004)))) (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      FStar_Pervasives_Native.None])
               in
            (match uu____6860 with
             | (env1,uu____7059,targs) ->
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
                 let rec aux env1 bs1 uu___94_7154 =
                   match uu___94_7154 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1  in
                       let uu____7170 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____7170
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____7192 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____7192 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____7225 = aux env [] bs  in (uu____7225, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____7234 = desugar_binder env b  in
            (match uu____7234 with
             | (FStar_Pervasives_Native.None ,uu____7245) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____7259 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____7259 with
                  | ((x,uu____7275),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____7288 =
                        let uu____7289 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____7289  in
                      (uu____7288, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern)
               in
            let uu____7307 =
              FStar_List.fold_left
                (fun uu____7327  ->
                   fun pat  ->
                     match uu____7327 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed
                              (uu____7353,(t,FStar_Pervasives_Native.None ))
                              ->
                              let uu____7363 =
                                let uu____7366 = free_type_vars env1 t  in
                                FStar_List.append uu____7366 ftvs  in
                              (env1, uu____7363)
                          | FStar_Parser_AST.PatAscribed
                              (uu____7371,(t,FStar_Pervasives_Native.Some
                                           tac))
                              ->
                              let uu____7382 =
                                let uu____7385 = free_type_vars env1 t  in
                                let uu____7388 =
                                  let uu____7391 = free_type_vars env1 tac
                                     in
                                  FStar_List.append uu____7391 ftvs  in
                                FStar_List.append uu____7385 uu____7388  in
                              (env1, uu____7382)
                          | uu____7396 -> (env1, ftvs))) (env, []) binders1
               in
            (match uu____7307 with
             | (uu____7405,ftv) ->
                 let ftv1 = sort_ftv ftv  in
                 let binders2 =
                   let uu____7417 =
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
                   FStar_List.append uu____7417 binders1  in
                 let rec aux env1 bs sc_pat_opt uu___95_7472 =
                   match uu___95_7472 with
                   | [] ->
                       let uu____7497 = desugar_term_aq env1 body  in
                       (match uu____7497 with
                        | (body1,aq) ->
                            let body2 =
                              match sc_pat_opt with
                              | FStar_Pervasives_Native.Some (sc,pat) ->
                                  let body2 =
                                    let uu____7534 =
                                      let uu____7535 =
                                        FStar_Syntax_Syntax.pat_bvs pat  in
                                      FStar_All.pipe_right uu____7535
                                        (FStar_List.map
                                           FStar_Syntax_Syntax.mk_binder)
                                       in
                                    FStar_Syntax_Subst.close uu____7534 body1
                                     in
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_match
                                       (sc,
                                         [(pat, FStar_Pervasives_Native.None,
                                            body2)]))
                                    FStar_Pervasives_Native.None
                                    body2.FStar_Syntax_Syntax.pos
                              | FStar_Pervasives_Native.None  -> body1  in
                            let uu____7604 =
                              let uu____7607 =
                                no_annot_abs (FStar_List.rev bs) body2  in
                              setpos uu____7607  in
                            (uu____7604, aq))
                   | p::rest ->
                       let uu____7620 = desugar_binding_pat env1 p  in
                       (match uu____7620 with
                        | (env2,b,pat) ->
                            let pat1 =
                              match pat with
                              | [] -> FStar_Pervasives_Native.None
                              | p1::[] -> FStar_Pervasives_Native.Some p1
                              | uu____7654 ->
                                  FStar_Errors.raise_error
                                    (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                      "Disjunctive patterns are not supported in abstractions")
                                    p.FStar_Parser_AST.prange
                               in
                            let uu____7661 =
                              match b with
                              | LetBinder uu____7698 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat1, sc_pat_opt) with
                                    | (FStar_Pervasives_Native.None
                                       ,uu____7764) -> sc_pat_opt
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.None ) ->
                                        let uu____7818 =
                                          let uu____7825 =
                                            FStar_Syntax_Syntax.bv_to_name x
                                             in
                                          (uu____7825, p1)  in
                                        FStar_Pervasives_Native.Some
                                          uu____7818
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.Some
                                       (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____7881,uu____7882) ->
                                             let tup2 =
                                               let uu____7884 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____7884
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____7888 =
                                                 let uu____7895 =
                                                   let uu____7896 =
                                                     let uu____7911 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2)
                                                        in
                                                     let uu____7914 =
                                                       let uu____7923 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc
                                                          in
                                                       let uu____7930 =
                                                         let uu____7939 =
                                                           let uu____7946 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x
                                                              in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____7946
                                                            in
                                                         [uu____7939]  in
                                                       uu____7923 ::
                                                         uu____7930
                                                        in
                                                     (uu____7911, uu____7914)
                                                      in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____7896
                                                    in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____7895
                                                  in
                                               uu____7888
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Parser_AST.range
                                                in
                                             let p2 =
                                               let uu____7987 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p1, false)]))
                                                 uu____7987
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____8030,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____8032,pats)) ->
                                             let tupn =
                                               let uu____8071 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____8071
                                                 FStar_Syntax_Syntax.Delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____8081 =
                                                 let uu____8082 =
                                                   let uu____8097 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn)
                                                      in
                                                   let uu____8100 =
                                                     let uu____8109 =
                                                       let uu____8118 =
                                                         let uu____8125 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____8125
                                                          in
                                                       [uu____8118]  in
                                                     FStar_List.append args
                                                       uu____8109
                                                      in
                                                   (uu____8097, uu____8100)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____8082
                                                  in
                                               mk1 uu____8081  in
                                             let p2 =
                                               let uu____8163 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p1, false)])))
                                                 uu____8163
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | uu____8204 ->
                                             failwith "Impossible")
                                     in
                                  ((x, aq), sc_pat_opt1)
                               in
                            (match uu____7661 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest))
                    in
                 aux env [] FStar_Pervasives_Native.None binders2)
        | FStar_Parser_AST.App
            (uu____8285,uu____8286,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____8308 =
                let uu____8309 = unparen e  in uu____8309.FStar_Parser_AST.tm
                 in
              match uu____8308 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____8319 ->
                  let uu____8320 = desugar_term_aq env e  in
                  (match uu____8320 with
                   | (head1,aq) ->
                       let uu____8333 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____8333, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____8340 ->
            let rec aux args aqs e =
              let uu____8419 =
                let uu____8420 = unparen e  in uu____8420.FStar_Parser_AST.tm
                 in
              match uu____8419 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____8440 = desugar_term_aq env t  in
                  (match uu____8440 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____8476 ->
                  let uu____8477 = desugar_term_aq env e  in
                  (match uu____8477 with
                   | (head1,aq) ->
                       let uu____8500 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____8500, (join_aqs (aq :: aqs))))
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
            let uu____8562 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____8562
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
            let uu____8614 = desugar_term_aq env t  in
            (match uu____8614 with
             | (tm,s) ->
                 let uu____8625 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____8625, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____8631 =
              let uu____8644 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____8644 then desugar_typ_aq else desugar_term_aq  in
            uu____8631 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____8699 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____8842  ->
                        match uu____8842 with
                        | (attr_opt,(p,def)) ->
                            let uu____8900 = is_app_pattern p  in
                            if uu____8900
                            then
                              let uu____8931 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____8931, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____9013 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____9013, def1)
                               | uu____9058 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____9096);
                                           FStar_Parser_AST.prange =
                                             uu____9097;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____9145 =
                                            let uu____9166 =
                                              let uu____9171 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____9171  in
                                            (uu____9166, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____9145, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____9262) ->
                                        if top_level
                                        then
                                          let uu____9297 =
                                            let uu____9318 =
                                              let uu____9323 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____9323  in
                                            (uu____9318, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____9297, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____9413 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____9444 =
                FStar_List.fold_left
                  (fun uu____9517  ->
                     fun uu____9518  ->
                       match (uu____9517, uu____9518) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____9626,uu____9627),uu____9628))
                           ->
                           let uu____9745 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____9771 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____9771 with
                                  | (env2,xx) ->
                                      let uu____9790 =
                                        let uu____9793 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____9793 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx), uu____9790))
                             | FStar_Util.Inr l ->
                                 let uu____9801 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.Delta_equational
                                    in
                                 (uu____9801, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____9745 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____9444 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____9949 =
                    match uu____9949 with
                    | (attrs_opt,(uu____9985,args,result_t),def) ->
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
                                let uu____10073 = is_comp_type env1 t  in
                                if uu____10073
                                then
                                  ((let uu____10075 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____10085 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____10085))
                                       in
                                    match uu____10075 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____10088 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____10090 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____10090))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____10088
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t)
                                 in
                              let uu____10095 =
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range
                                 in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed (def, t1, tacopt))
                                uu____10095 FStar_Parser_AST.Expr
                           in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____10099 ->
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
                              let uu____10114 =
                                let uu____10115 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____10115
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____10114
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
                  let uu____10190 = desugar_term_aq env' body  in
                  (match uu____10190 with
                   | (body1,aq) ->
                       let uu____10203 =
                         let uu____10206 =
                           let uu____10207 =
                             let uu____10220 =
                               FStar_Syntax_Subst.close rec_bindings1 body1
                                in
                             ((is_rec, lbs1), uu____10220)  in
                           FStar_Syntax_Syntax.Tm_let uu____10207  in
                         FStar_All.pipe_left mk1 uu____10206  in
                       (uu____10203, aq))
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
              let uu____10298 =
                desugar_binding_pat_maybe_top top_level env pat is_mutable
                 in
              match uu____10298 with
              | (env1,binder,pat1) ->
                  let uu____10320 =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let uu____10346 = desugar_term_aq env1 t2  in
                        (match uu____10346 with
                         | (body1,aq) ->
                             let fv =
                               let uu____10360 =
                                 FStar_Syntax_Util.incr_delta_qualifier t12
                                  in
                               FStar_Syntax_Syntax.lid_as_fv l uu____10360
                                 FStar_Pervasives_Native.None
                                in
                             let uu____10361 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t12,
                                            (t12.FStar_Syntax_Syntax.pos))]),
                                      body1))
                                in
                             (uu____10361, aq))
                    | LocalBinder (x,uu____10391) ->
                        let uu____10392 = desugar_term_aq env1 t2  in
                        (match uu____10392 with
                         | (body1,aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | {
                                   FStar_Syntax_Syntax.v =
                                     FStar_Syntax_Syntax.Pat_wild uu____10406;
                                   FStar_Syntax_Syntax.p = uu____10407;_}::[]
                                   -> body1
                               | uu____10408 ->
                                   let uu____10411 =
                                     let uu____10418 =
                                       let uu____10419 =
                                         let uu____10442 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         let uu____10445 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1
                                            in
                                         (uu____10442, uu____10445)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____10419
                                        in
                                     FStar_Syntax_Syntax.mk uu____10418  in
                                   uu____10411 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range
                                in
                             let uu____10485 =
                               let uu____10488 =
                                 let uu____10489 =
                                   let uu____10502 =
                                     let uu____10505 =
                                       let uu____10506 =
                                         FStar_Syntax_Syntax.mk_binder x  in
                                       [uu____10506]  in
                                     FStar_Syntax_Subst.close uu____10505
                                       body2
                                      in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t12,
                                           (t12.FStar_Syntax_Syntax.pos))]),
                                     uu____10502)
                                    in
                                 FStar_Syntax_Syntax.Tm_let uu____10489  in
                               FStar_All.pipe_left mk1 uu____10488  in
                             (uu____10485, aq))
                     in
                  (match uu____10320 with
                   | (tm,aq) ->
                       if is_mutable
                       then
                         let uu____10563 =
                           FStar_All.pipe_left mk1
                             (FStar_Syntax_Syntax.Tm_meta
                                (tm,
                                  (FStar_Syntax_Syntax.Meta_desugared
                                     FStar_Syntax_Syntax.Mutable_alloc)))
                            in
                         (uu____10563, aq)
                       else (tm, aq))
               in
            let uu____10575 = FStar_List.hd lbs  in
            (match uu____10575 with
             | (attrs,(head_pat,defn)) ->
                 let uu____10619 = is_rec || (is_app_pattern head_pat)  in
                 if uu____10619
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____10632 =
                let uu____10633 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.Delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____10633  in
              mk1 uu____10632  in
            let uu____10634 = desugar_term_aq env t1  in
            (match uu____10634 with
             | (t1',aq1) ->
                 let uu____10645 = desugar_term_aq env t2  in
                 (match uu____10645 with
                  | (t2',aq2) ->
                      let uu____10656 = desugar_term_aq env t3  in
                      (match uu____10656 with
                       | (t3',aq3) ->
                           let uu____10667 =
                             let uu____10668 =
                               let uu____10669 =
                                 let uu____10692 =
                                   FStar_Syntax_Util.ascribe t1'
                                     ((FStar_Util.Inl t_bool1),
                                       FStar_Pervasives_Native.None)
                                    in
                                 let uu____10713 =
                                   let uu____10730 =
                                     let uu____10745 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t2.FStar_Parser_AST.range
                                        in
                                     (uu____10745,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____10758 =
                                     let uu____10775 =
                                       let uu____10790 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t3.FStar_Parser_AST.range
                                          in
                                       (uu____10790,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____10775]  in
                                   uu____10730 :: uu____10758  in
                                 (uu____10692, uu____10713)  in
                               FStar_Syntax_Syntax.Tm_match uu____10669  in
                             mk1 uu____10668  in
                           (uu____10667, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____10989 =
              match uu____10989 with
              | (pat,wopt,b) ->
                  let uu____11011 = desugar_match_pat env pat  in
                  (match uu____11011 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____11042 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____11042
                          in
                       let uu____11043 = desugar_term_aq env1 b  in
                       (match uu____11043 with
                        | (b1,aq) ->
                            let uu____11056 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____11056, aq)))
               in
            let uu____11061 = desugar_term_aq env e  in
            (match uu____11061 with
             | (e1,aq) ->
                 let uu____11072 =
                   let uu____11105 =
                     let uu____11140 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____11140 FStar_List.unzip  in
                   FStar_All.pipe_right uu____11105
                     (fun uu____11276  ->
                        match uu____11276 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____11072 with
                  | (brs,aqs) ->
                      let uu____11509 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____11509, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____11554 = is_comp_type env t  in
              if uu____11554
              then
                let uu____11563 = desugar_comp t.FStar_Parser_AST.range env t
                   in
                FStar_Util.Inr uu____11563
              else
                (let uu____11571 = desugar_term env t  in
                 FStar_Util.Inl uu____11571)
               in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)  in
            let uu____11581 = desugar_term_aq env e  in
            (match uu____11581 with
             | (e1,aq) ->
                 let uu____11592 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_ascribed
                        (e1, (annot, tac_opt1), FStar_Pervasives_Native.None))
                    in
                 (uu____11592, aq))
        | FStar_Parser_AST.Record (uu____11625,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____11666 = FStar_List.hd fields  in
              match uu____11666 with | (f,uu____11678) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____11724  ->
                        match uu____11724 with
                        | (g,uu____11730) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____11736,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____11750 =
                         let uu____11755 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____11755)
                          in
                       FStar_Errors.raise_error uu____11750
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
                  let uu____11763 =
                    let uu____11774 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____11805  ->
                              match uu____11805 with
                              | (f,uu____11815) ->
                                  let uu____11816 =
                                    let uu____11817 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____11817
                                     in
                                  (uu____11816, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____11774)  in
                  FStar_Parser_AST.Construct uu____11763
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____11835 =
                      let uu____11836 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____11836  in
                    FStar_Parser_AST.mk_term uu____11835
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____11838 =
                      let uu____11851 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____11881  ->
                                match uu____11881 with
                                | (f,uu____11891) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____11851)  in
                    FStar_Parser_AST.Record uu____11838  in
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
            let uu____11951 = desugar_term_aq env recterm1  in
            (match uu____11951 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____11967;
                         FStar_Syntax_Syntax.vars = uu____11968;_},args)
                      ->
                      let uu____11990 =
                        let uu____11991 =
                          let uu____11992 =
                            let uu____12007 =
                              let uu____12010 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____12011 =
                                let uu____12014 =
                                  let uu____12015 =
                                    let uu____12022 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____12022)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____12015
                                   in
                                FStar_Pervasives_Native.Some uu____12014  in
                              FStar_Syntax_Syntax.fvar uu____12010
                                FStar_Syntax_Syntax.Delta_constant
                                uu____12011
                               in
                            (uu____12007, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____11992  in
                        FStar_All.pipe_left mk1 uu____11991  in
                      (uu____11990, s)
                  | uu____12049 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____12053 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____12053 with
              | (constrname,is_rec) ->
                  let uu____12068 = desugar_term_aq env e  in
                  (match uu____12068 with
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
                       let uu____12086 =
                         let uu____12087 =
                           let uu____12088 =
                             let uu____12103 =
                               let uu____12106 =
                                 let uu____12107 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____12107
                                  in
                               FStar_Syntax_Syntax.fvar uu____12106
                                 FStar_Syntax_Syntax.Delta_equational qual
                                in
                             let uu____12108 =
                               let uu____12117 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____12117]  in
                             (uu____12103, uu____12108)  in
                           FStar_Syntax_Syntax.Tm_app uu____12088  in
                         FStar_All.pipe_left mk1 uu____12087  in
                       (uu____12086, s))))
        | FStar_Parser_AST.NamedTyp (uu____12146,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____12155 =
              let uu____12156 = FStar_Syntax_Subst.compress tm  in
              uu____12156.FStar_Syntax_Syntax.n  in
            (match uu____12155 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____12164 =
                   let uu___129_12165 =
                     let uu____12166 =
                       let uu____12167 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____12167  in
                     FStar_Syntax_Util.exp_string uu____12166  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___129_12165.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___129_12165.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____12164, noaqs)
             | uu____12168 ->
                 let uu____12169 =
                   let uu____12174 =
                     let uu____12175 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.strcat "VQuote, expected an fvar, got: "
                       uu____12175
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____12174)  in
                 FStar_Errors.raise_error uu____12169
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____12181 = desugar_term_aq env e  in
            (match uu____12181 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____12193 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____12193, noaqs))
        | FStar_Parser_AST.Antiquote (b,e) ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____12199 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____12200 =
              let uu____12201 =
                let uu____12210 = desugar_term env e  in (bv, b, uu____12210)
                 in
              [uu____12201]  in
            (uu____12199, uu____12200)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____12241 =
              let uu____12242 =
                let uu____12243 =
                  let uu____12250 = desugar_term env e  in (uu____12250, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____12243  in
              FStar_All.pipe_left mk1 uu____12242  in
            (uu____12241, noaqs)
        | uu____12255 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____12256 = desugar_formula env top  in
            (uu____12256, noaqs)
        | uu____12257 ->
            let uu____12258 =
              let uu____12263 =
                let uu____12264 = FStar_Parser_AST.term_to_string top  in
                Prims.strcat "Unexpected term: " uu____12264  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____12263)  in
            FStar_Errors.raise_error uu____12258 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____12270 -> false
    | uu____12279 -> true

and (is_synth_by_tactic :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (l,r,FStar_Parser_AST.Hash ) ->
          is_synth_by_tactic e l
      | FStar_Parser_AST.Var lid ->
          let uu____12285 =
            FStar_Syntax_DsEnv.resolve_to_fully_qualified_name e lid  in
          (match uu____12285 with
           | FStar_Pervasives_Native.Some lid1 ->
               FStar_Ident.lid_equals lid1 FStar_Parser_Const.synth_lid
           | FStar_Pervasives_Native.None  -> false)
      | uu____12289 -> false

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
           (fun uu____12326  ->
              match uu____12326 with
              | (a,imp) ->
                  let uu____12339 = desugar_term env a  in
                  arg_withimp_e imp uu____12339))

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
        let is_requires uu____12371 =
          match uu____12371 with
          | (t1,uu____12377) ->
              let uu____12378 =
                let uu____12379 = unparen t1  in
                uu____12379.FStar_Parser_AST.tm  in
              (match uu____12378 with
               | FStar_Parser_AST.Requires uu____12380 -> true
               | uu____12387 -> false)
           in
        let is_ensures uu____12397 =
          match uu____12397 with
          | (t1,uu____12403) ->
              let uu____12404 =
                let uu____12405 = unparen t1  in
                uu____12405.FStar_Parser_AST.tm  in
              (match uu____12404 with
               | FStar_Parser_AST.Ensures uu____12406 -> true
               | uu____12413 -> false)
           in
        let is_app head1 uu____12428 =
          match uu____12428 with
          | (t1,uu____12434) ->
              let uu____12435 =
                let uu____12436 = unparen t1  in
                uu____12436.FStar_Parser_AST.tm  in
              (match uu____12435 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____12438;
                      FStar_Parser_AST.level = uu____12439;_},uu____12440,uu____12441)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____12442 -> false)
           in
        let is_smt_pat uu____12452 =
          match uu____12452 with
          | (t1,uu____12458) ->
              let uu____12459 =
                let uu____12460 = unparen t1  in
                uu____12460.FStar_Parser_AST.tm  in
              (match uu____12459 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____12463);
                             FStar_Parser_AST.range = uu____12464;
                             FStar_Parser_AST.level = uu____12465;_},uu____12466)::uu____12467::[])
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
                             FStar_Parser_AST.range = uu____12506;
                             FStar_Parser_AST.level = uu____12507;_},uu____12508)::uu____12509::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
               | uu____12534 -> false)
           in
        let is_decreases = is_app "decreases"  in
        let pre_process_comp_typ t1 =
          let uu____12566 = head_and_args t1  in
          match uu____12566 with
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
                   let thunk_ens uu____12664 =
                     match uu____12664 with
                     | (e,i) ->
                         let uu____12675 = thunk_ens_ e  in (uu____12675, i)
                      in
                   let fail_lemma uu____12687 =
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
                         let uu____12767 =
                           let uu____12774 =
                             let uu____12781 = thunk_ens ens  in
                             [uu____12781; nil_pat]  in
                           req_true :: uu____12774  in
                         unit_tm :: uu____12767
                     | req::ens::[] when
                         (is_requires req) && (is_ensures ens) ->
                         let uu____12828 =
                           let uu____12835 =
                             let uu____12842 = thunk_ens ens  in
                             [uu____12842; nil_pat]  in
                           req :: uu____12835  in
                         unit_tm :: uu____12828
                     | ens::smtpat::[] when
                         (((let uu____12891 = is_requires ens  in
                            Prims.op_Negation uu____12891) &&
                             (let uu____12893 = is_smt_pat ens  in
                              Prims.op_Negation uu____12893))
                            &&
                            (let uu____12895 = is_decreases ens  in
                             Prims.op_Negation uu____12895))
                           && (is_smt_pat smtpat)
                         ->
                         let uu____12896 =
                           let uu____12903 =
                             let uu____12910 = thunk_ens ens  in
                             [uu____12910; smtpat]  in
                           req_true :: uu____12903  in
                         unit_tm :: uu____12896
                     | ens::dec::[] when
                         (is_ensures ens) && (is_decreases dec) ->
                         let uu____12957 =
                           let uu____12964 =
                             let uu____12971 = thunk_ens ens  in
                             [uu____12971; nil_pat; dec]  in
                           req_true :: uu____12964  in
                         unit_tm :: uu____12957
                     | ens::dec::smtpat::[] when
                         ((is_ensures ens) && (is_decreases dec)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____13031 =
                           let uu____13038 =
                             let uu____13045 = thunk_ens ens  in
                             [uu____13045; smtpat; dec]  in
                           req_true :: uu____13038  in
                         unit_tm :: uu____13031
                     | req::ens::dec::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_decreases dec)
                         ->
                         let uu____13105 =
                           let uu____13112 =
                             let uu____13119 = thunk_ens ens  in
                             [uu____13119; nil_pat; dec]  in
                           req :: uu____13112  in
                         unit_tm :: uu____13105
                     | req::ens::smtpat::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____13179 =
                           let uu____13186 =
                             let uu____13193 = thunk_ens ens  in
                             [uu____13193; smtpat]  in
                           req :: uu____13186  in
                         unit_tm :: uu____13179
                     | req::ens::dec::smtpat::[] when
                         (((is_requires req) && (is_ensures ens)) &&
                            (is_smt_pat smtpat))
                           && (is_decreases dec)
                         ->
                         let uu____13258 =
                           let uu____13265 =
                             let uu____13272 = thunk_ens ens  in
                             [uu____13272; dec; smtpat]  in
                           req :: uu____13265  in
                         unit_tm :: uu____13258
                     | _other -> fail_lemma ()  in
                   let head_and_attributes =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) lemma
                      in
                   (head_and_attributes, args1)
               | FStar_Parser_AST.Name l when
                   FStar_Syntax_DsEnv.is_effect_name env l ->
                   let uu____13334 =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) l
                      in
                   (uu____13334, args)
               | FStar_Parser_AST.Name l when
                   (let uu____13362 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____13362
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   let uu____13363 =
                     let uu____13370 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_Tot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____13370, [])  in
                   (uu____13363, args)
               | FStar_Parser_AST.Name l when
                   (let uu____13388 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____13388
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                   ->
                   let uu____13389 =
                     let uu____13396 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_GTot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____13396, [])  in
                   (uu____13389, args)
               | FStar_Parser_AST.Name l when
                   (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                      ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                     || ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                   ->
                   let uu____13412 =
                     let uu____13419 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_Tot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____13419, [])  in
                   (uu____13412, [(t1, FStar_Parser_AST.Nothing)])
               | uu____13442 ->
                   let default_effect =
                     let uu____13444 = FStar_Options.ml_ish ()  in
                     if uu____13444
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____13447 =
                           FStar_Options.warn_default_effects ()  in
                         if uu____13447
                         then
                           FStar_Errors.log_issue
                             head1.FStar_Parser_AST.range
                             (FStar_Errors.Warning_UseDefaultEffect,
                               "Using default effect Tot")
                         else ());
                        FStar_Parser_Const.effect_Tot_lid)
                      in
                   let uu____13449 =
                     let uu____13456 =
                       FStar_Ident.set_lid_range default_effect
                         head1.FStar_Parser_AST.range
                        in
                     (uu____13456, [])  in
                   (uu____13449, [(t1, FStar_Parser_AST.Nothing)]))
           in
        let uu____13479 = pre_process_comp_typ t  in
        match uu____13479 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____13529 =
                  let uu____13534 =
                    let uu____13535 = FStar_Syntax_Print.lid_to_string eff
                       in
                    FStar_Util.format1 "Not enough args to effect %s"
                      uu____13535
                     in
                  (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____13534)  in
                fail1 uu____13529)
             else ();
             (let is_universe uu____13546 =
                match uu____13546 with
                | (uu____13551,imp) -> imp = FStar_Parser_AST.UnivApp  in
              let uu____13553 = FStar_Util.take is_universe args  in
              match uu____13553 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____13612  ->
                         match uu____13612 with
                         | (u,imp) -> desugar_universe u) universes
                     in
                  let uu____13619 =
                    let uu____13634 = FStar_List.hd args1  in
                    let uu____13643 = FStar_List.tl args1  in
                    (uu____13634, uu____13643)  in
                  (match uu____13619 with
                   | (result_arg,rest) ->
                       let result_typ =
                         desugar_typ env
                           (FStar_Pervasives_Native.fst result_arg)
                          in
                       let rest1 = desugar_args env rest  in
                       let uu____13698 =
                         let is_decrease uu____13736 =
                           match uu____13736 with
                           | (t1,uu____13746) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.pos = uu____13756;
                                       FStar_Syntax_Syntax.vars = uu____13757;_},uu____13758::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.decreases_lid
                                | uu____13789 -> false)
                            in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease)
                          in
                       (match uu____13698 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____13905  ->
                                      match uu____13905 with
                                      | (t1,uu____13915) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____13924,(arg,uu____13926)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____13955 -> failwith "impos")))
                               in
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
                                | uu____13972 -> false  in
                              (((is_empty decreases_clause) &&
                                  (is_empty rest2))
                                 && (is_empty cattributes))
                                && (is_empty universes1)
                               in
                            let uu____13983 =
                              no_additional_args &&
                                (FStar_Ident.lid_equals eff
                                   FStar_Parser_Const.effect_Tot_lid)
                               in
                            if uu____13983
                            then FStar_Syntax_Syntax.mk_Total result_typ
                            else
                              (let uu____13987 =
                                 no_additional_args &&
                                   (FStar_Ident.lid_equals eff
                                      FStar_Parser_Const.effect_GTot_lid)
                                  in
                               if uu____13987
                               then FStar_Syntax_Syntax.mk_GTotal result_typ
                               else
                                 (let flags1 =
                                    let uu____13994 =
                                      FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_Lemma_lid
                                       in
                                    if uu____13994
                                    then [FStar_Syntax_Syntax.LEMMA]
                                    else
                                      (let uu____13998 =
                                         FStar_Ident.lid_equals eff
                                           FStar_Parser_Const.effect_Tot_lid
                                          in
                                       if uu____13998
                                       then [FStar_Syntax_Syntax.TOTAL]
                                       else
                                         (let uu____14002 =
                                            FStar_Ident.lid_equals eff
                                              FStar_Parser_Const.effect_ML_lid
                                             in
                                          if uu____14002
                                          then [FStar_Syntax_Syntax.MLEFFECT]
                                          else
                                            (let uu____14006 =
                                               FStar_Ident.lid_equals eff
                                                 FStar_Parser_Const.effect_GTot_lid
                                                in
                                             if uu____14006
                                             then
                                               [FStar_Syntax_Syntax.SOMETRIVIAL]
                                             else [])))
                                     in
                                  let flags2 =
                                    FStar_List.append flags1 cattributes  in
                                  let rest3 =
                                    let uu____14022 =
                                      FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_Lemma_lid
                                       in
                                    if uu____14022
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
                                                  let uu____14107 =
                                                    FStar_Ident.set_lid_range
                                                      FStar_Parser_Const.pattern_lid
                                                      pat.FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_Syntax.fvar
                                                    uu____14107
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
                                            | uu____14122 -> pat  in
                                          let uu____14123 =
                                            let uu____14134 =
                                              let uu____14145 =
                                                let uu____14154 =
                                                  FStar_Syntax_Syntax.mk
                                                    (FStar_Syntax_Syntax.Tm_meta
                                                       (pat1,
                                                         (FStar_Syntax_Syntax.Meta_desugared
                                                            FStar_Syntax_Syntax.Meta_smt_pat)))
                                                    FStar_Pervasives_Native.None
                                                    pat1.FStar_Syntax_Syntax.pos
                                                   in
                                                (uu____14154, aq)  in
                                              [uu____14145]  in
                                            ens :: uu____14134  in
                                          req :: uu____14123
                                      | uu____14195 -> rest2
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
        | uu____14219 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___130_14240 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___130_14240.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___130_14240.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___131_14282 = b  in
             {
               FStar_Parser_AST.b = (uu___131_14282.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___131_14282.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___131_14282.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____14345 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____14345)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____14358 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____14358 with
             | (env1,a1) ->
                 let a2 =
                   let uu___132_14368 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___132_14368.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___132_14368.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____14394 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____14408 =
                     let uu____14411 =
                       let uu____14412 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____14412]  in
                     no_annot_abs uu____14411 body2  in
                   FStar_All.pipe_left setpos uu____14408  in
                 let uu____14427 =
                   let uu____14428 =
                     let uu____14443 =
                       let uu____14446 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____14446
                         (FStar_Syntax_Syntax.Delta_defined_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____14447 =
                       let uu____14456 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____14456]  in
                     (uu____14443, uu____14447)  in
                   FStar_Syntax_Syntax.Tm_app uu____14428  in
                 FStar_All.pipe_left mk1 uu____14427)
        | uu____14487 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____14567 = q (rest, pats, body)  in
              let uu____14574 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____14567 uu____14574
                FStar_Parser_AST.Formula
               in
            let uu____14575 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____14575 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____14584 -> failwith "impossible"  in
      let uu____14587 =
        let uu____14588 = unparen f  in uu____14588.FStar_Parser_AST.tm  in
      match uu____14587 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____14595,uu____14596) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____14607,uu____14608) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____14639 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____14639
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____14675 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____14675
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____14718 -> desugar_term env f

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
      let uu____14723 =
        FStar_List.fold_left
          (fun uu____14759  ->
             fun b  ->
               match uu____14759 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___133_14811 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___133_14811.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___133_14811.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___133_14811.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____14828 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____14828 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___134_14848 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___134_14848.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___134_14848.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____14865 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____14723 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

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
          let uu____14952 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____14952)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____14957 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____14957)
      | FStar_Parser_AST.TVariable x ->
          let uu____14961 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____14961)
      | FStar_Parser_AST.NoName t ->
          let uu____14965 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____14965)
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
               (fun uu___96_15004  ->
                  match uu___96_15004 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____15005 -> false))
           in
        let quals2 q =
          let uu____15018 =
            (let uu____15021 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____15021) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____15018
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____15035 = FStar_Ident.range_of_lid disc_name  in
                let uu____15036 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____15035;
                  FStar_Syntax_Syntax.sigquals = uu____15036;
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
            let uu____15075 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____15109  ->
                        match uu____15109 with
                        | (x,uu____15117) ->
                            let uu____15118 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____15118 with
                             | (field_name,uu____15126) ->
                                 let only_decl =
                                   ((let uu____15130 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____15130)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____15132 =
                                        let uu____15133 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____15133.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____15132)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____15149 =
                                       FStar_List.filter
                                         (fun uu___97_15153  ->
                                            match uu___97_15153 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____15154 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____15149
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___98_15167  ->
                                             match uu___98_15167 with
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____15168 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____15170 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____15170;
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____15175 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____15175
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          FStar_Syntax_Syntax.Delta_equational
                                      else
                                        FStar_Syntax_Syntax.Delta_equational
                                       in
                                    let lb =
                                      let uu____15180 =
                                        let uu____15185 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____15185  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____15180;
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
                                      let uu____15189 =
                                        let uu____15190 =
                                          let uu____15197 =
                                            let uu____15200 =
                                              let uu____15201 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____15201
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____15200]  in
                                          ((false, [lb]), uu____15197)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____15190
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____15189;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____15075 FStar_List.flatten
  
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
            (lid,uu____15245,t,uu____15247,n1,uu____15249) when
            let uu____15254 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____15254 ->
            let uu____15255 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____15255 with
             | (formals,uu____15271) ->
                 (match formals with
                  | [] -> []
                  | uu____15294 ->
                      let filter_records uu___99_15308 =
                        match uu___99_15308 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____15311,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____15323 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____15325 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____15325 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Syntax_Syntax.Data_ctor
                        | FStar_Pervasives_Native.Some q -> q  in
                      let iquals1 =
                        if
                          FStar_List.contains FStar_Syntax_Syntax.Abstract
                            iquals
                        then FStar_Syntax_Syntax.Private :: iquals
                        else iquals  in
                      let uu____15335 = FStar_Util.first_N n1 formals  in
                      (match uu____15335 with
                       | (uu____15358,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____15384 -> []
  
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
                    let uu____15454 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____15454
                    then
                      let uu____15457 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____15457
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____15460 =
                      let uu____15465 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____15465  in
                    let uu____15466 =
                      let uu____15469 = FStar_Syntax_Syntax.mk_Total k  in
                      FStar_Syntax_Util.arrow typars uu____15469  in
                    let uu____15472 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____15460;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____15466;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____15472;
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
          let tycon_id uu___100_15523 =
            match uu___100_15523 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____15525,uu____15526) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____15536,uu____15537,uu____15538) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____15548,uu____15549,uu____15550) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____15580,uu____15581,uu____15582) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____15626) ->
                let uu____15627 =
                  let uu____15628 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____15628  in
                FStar_Parser_AST.mk_term uu____15627 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____15630 =
                  let uu____15631 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____15631  in
                FStar_Parser_AST.mk_term uu____15630 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____15633) ->
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
              | uu____15664 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____15670 =
                     let uu____15671 =
                       let uu____15678 = binder_to_term b  in
                       (out, uu____15678, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____15671  in
                   FStar_Parser_AST.mk_term uu____15670
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___101_15690 =
            match uu___101_15690 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____15746  ->
                       match uu____15746 with
                       | (x,t,uu____15757) ->
                           let uu____15762 =
                             let uu____15763 =
                               let uu____15768 =
                                 FStar_Syntax_Util.mangle_field_name x  in
                               (uu____15768, t)  in
                             FStar_Parser_AST.Annotated uu____15763  in
                           FStar_Parser_AST.mk_binder uu____15762
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____15770 =
                    let uu____15771 =
                      let uu____15772 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____15772  in
                    FStar_Parser_AST.mk_term uu____15771
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____15770 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let uu____15776 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____15803  ->
                          match uu____15803 with
                          | (x,uu____15813,uu____15814) ->
                              FStar_Syntax_Util.unmangle_field_name x))
                   in
                ((FStar_Parser_AST.TyconVariant
                    (id1, parms, kopt,
                      [(constrName, (FStar_Pervasives_Native.Some constrTyp),
                         FStar_Pervasives_Native.None, false)])),
                  uu____15776)
            | uu____15867 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___102_15906 =
            match uu___102_15906 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____15930 = typars_of_binders _env binders  in
                (match uu____15930 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____15972 =
                         let uu____15973 =
                           let uu____15974 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____15974  in
                         FStar_Parser_AST.mk_term uu____15973
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____15972 binders  in
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
            | uu____15985 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____16033 =
              FStar_List.fold_left
                (fun uu____16073  ->
                   fun uu____16074  ->
                     match (uu____16073, uu____16074) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____16165 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____16165 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____16033 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____16278 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____16278
                | uu____16279 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____16287 = desugar_abstract_tc quals env [] tc  in
              (match uu____16287 with
               | (uu____16300,uu____16301,se,uu____16303) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____16306,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____16323 =
                                 let uu____16324 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____16324  in
                               if uu____16323
                               then
                                 let uu____16325 =
                                   let uu____16330 =
                                     let uu____16331 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____16331
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____16330)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____16325
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
                           | uu____16338 ->
                               let uu____16339 =
                                 let uu____16346 =
                                   let uu____16347 =
                                     let uu____16360 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____16360)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____16347
                                    in
                                 FStar_Syntax_Syntax.mk uu____16346  in
                               uu____16339 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___135_16374 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___135_16374.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___135_16374.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___135_16374.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____16375 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____16378 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____16378
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____16391 = typars_of_binders env binders  in
              (match uu____16391 with
               | (env',typars) ->
                   let k =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____16427 =
                           FStar_Util.for_some
                             (fun uu___103_16429  ->
                                match uu___103_16429 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____16430 -> false) quals
                            in
                         if uu____16427
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Util.ktype
                     | FStar_Pervasives_Native.Some k -> desugar_term env' k
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____16437 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___104_16441  ->
                               match uu___104_16441 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____16442 -> false))
                        in
                     if uu____16437
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____16451 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____16451
                     then
                       let uu____16454 =
                         let uu____16461 =
                           let uu____16462 = unparen t  in
                           uu____16462.FStar_Parser_AST.tm  in
                         match uu____16461 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____16483 =
                               match FStar_List.rev args with
                               | (last_arg,uu____16513)::args_rev ->
                                   let uu____16525 =
                                     let uu____16526 = unparen last_arg  in
                                     uu____16526.FStar_Parser_AST.tm  in
                                   (match uu____16525 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____16554 -> ([], args))
                               | uu____16563 -> ([], args)  in
                             (match uu____16483 with
                              | (cattributes,args1) ->
                                  let uu____16602 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____16602))
                         | uu____16613 -> (t, [])  in
                       match uu____16454 with
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
                                  (fun uu___105_16635  ->
                                     match uu___105_16635 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____16636 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____16643)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____16667 = tycon_record_as_variant trec  in
              (match uu____16667 with
               | (t,fs) ->
                   let uu____16684 =
                     let uu____16687 =
                       let uu____16688 =
                         let uu____16697 =
                           let uu____16700 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____16700  in
                         (uu____16697, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____16688  in
                     uu____16687 :: quals  in
                   desugar_tycon env d uu____16684 [t])
          | uu____16705::uu____16706 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____16873 = et  in
                match uu____16873 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____17098 ->
                         let trec = tc  in
                         let uu____17122 = tycon_record_as_variant trec  in
                         (match uu____17122 with
                          | (t,fs) ->
                              let uu____17181 =
                                let uu____17184 =
                                  let uu____17185 =
                                    let uu____17194 =
                                      let uu____17197 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____17197  in
                                    (uu____17194, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____17185
                                   in
                                uu____17184 :: quals1  in
                              collect_tcs uu____17181 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____17284 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____17284 with
                          | (env2,uu____17344,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____17493 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____17493 with
                          | (env2,uu____17553,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____17678 ->
                         failwith "Unrecognized mutual type definition")
                 in
              let uu____17725 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____17725 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___107_18236  ->
                             match uu___107_18236 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____18303,uu____18304);
                                    FStar_Syntax_Syntax.sigrng = uu____18305;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____18306;
                                    FStar_Syntax_Syntax.sigmeta = uu____18307;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____18308;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____18369 =
                                     typars_of_binders env1 binders  in
                                   match uu____18369 with
                                   | (env2,tpars1) ->
                                       let uu____18400 =
                                         push_tparams env2 tpars1  in
                                       (match uu____18400 with
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
                                 let uu____18433 =
                                   let uu____18454 =
                                     mk_typ_abbrev id1 uvs tpars k t1 
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____18454)
                                    in
                                 [uu____18433]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____18522);
                                    FStar_Syntax_Syntax.sigrng = uu____18523;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____18525;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____18526;_},constrs,tconstr,quals1)
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
                                 let uu____18624 = push_tparams env1 tpars
                                    in
                                 (match uu____18624 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____18701  ->
                                             match uu____18701 with
                                             | (x,uu____18715) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____18723 =
                                        let uu____18752 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____18866  ->
                                                  match uu____18866 with
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
                                                        let uu____18922 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____18922
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
                                                                uu___106_18933
                                                                 ->
                                                                match uu___106_18933
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____18945
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____18953 =
                                                        let uu____18974 =
                                                          let uu____18975 =
                                                            let uu____18976 =
                                                              let uu____18991
                                                                =
                                                                let uu____18992
                                                                  =
                                                                  let uu____18995
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____18995
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____18992
                                                                 in
                                                              (name, univs1,
                                                                uu____18991,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____18976
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____18975;
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
                                                          uu____18974)
                                                         in
                                                      (name, uu____18953)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____18752
                                         in
                                      (match uu____18723 with
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
                             | uu____19232 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____19364  ->
                             match uu____19364 with
                             | (name_doc,uu____19392,uu____19393) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____19473  ->
                             match uu____19473 with
                             | (uu____19494,uu____19495,se) -> se))
                      in
                   let uu____19525 =
                     let uu____19532 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____19532 rng
                      in
                   (match uu____19525 with
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
                               (fun uu____19598  ->
                                  match uu____19598 with
                                  | (uu____19621,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____19672,tps,k,uu____19675,constrs)
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
                                  | uu____19694 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____19711  ->
                                 match uu____19711 with
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
      let uu____19754 =
        FStar_List.fold_left
          (fun uu____19789  ->
             fun b  ->
               match uu____19789 with
               | (env1,binders1) ->
                   let uu____19833 = desugar_binder env1 b  in
                   (match uu____19833 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____19856 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____19856 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____19911 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____19754 with
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
          let uu____20012 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___108_20017  ->
                    match uu___108_20017 with
                    | FStar_Syntax_Syntax.Reflectable uu____20018 -> true
                    | uu____20019 -> false))
             in
          if uu____20012
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____20022 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____20022
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
                  let uu____20164 = desugar_binders monad_env eff_binders  in
                  match uu____20164 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let for_free =
                        let uu____20203 =
                          let uu____20205 =
                            let uu____20212 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____20212  in
                          FStar_List.length uu____20205  in
                        uu____20203 = (Prims.parse_int "1")  in
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
                            (uu____20253,(FStar_Parser_AST.TyconAbbrev
                                          (name,uu____20255,uu____20256,uu____20257),uu____20258)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____20291 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____20292 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____20304 = name_of_eff_decl decl  in
                             FStar_List.mem uu____20304 mandatory_members)
                          eff_decls
                         in
                      (match uu____20292 with
                       | (mandatory_members_decls,actions) ->
                           let uu____20321 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____20350  ->
                                     fun decl  ->
                                       match uu____20350 with
                                       | (env2,out) ->
                                           let uu____20370 =
                                             desugar_decl env2 decl  in
                                           (match uu____20370 with
                                            | (env3,ses) ->
                                                let uu____20383 =
                                                  let uu____20386 =
                                                    FStar_List.hd ses  in
                                                  uu____20386 :: out  in
                                                (env3, uu____20383)))
                                  (env1, []))
                              in
                           (match uu____20321 with
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
                                              (uu____20454,(FStar_Parser_AST.TyconAbbrev
                                                            (name,action_params,uu____20457,
                                                             {
                                                               FStar_Parser_AST.tm
                                                                 =
                                                                 FStar_Parser_AST.Construct
                                                                 (uu____20458,
                                                                  (def,uu____20460)::
                                                                  (cps_type,uu____20462)::[]);
                                                               FStar_Parser_AST.range
                                                                 =
                                                                 uu____20463;
                                                               FStar_Parser_AST.level
                                                                 =
                                                                 uu____20464;_}),doc1)::[])
                                              when Prims.op_Negation for_free
                                              ->
                                              let uu____20516 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____20516 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____20554 =
                                                     let uu____20555 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____20556 =
                                                       let uu____20557 =
                                                         desugar_term env3
                                                           def
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____20557
                                                        in
                                                     let uu____20562 =
                                                       let uu____20563 =
                                                         desugar_typ env3
                                                           cps_type
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____20563
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____20555;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____20556;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____20562
                                                     }  in
                                                   (uu____20554, doc1))
                                          | FStar_Parser_AST.Tycon
                                              (uu____20570,(FStar_Parser_AST.TyconAbbrev
                                                            (name,action_params,uu____20573,defn),doc1)::[])
                                              when for_free ->
                                              let uu____20608 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____20608 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____20646 =
                                                     let uu____20647 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____20648 =
                                                       let uu____20649 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____20649
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____20647;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____20648;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____20646, doc1))
                                          | uu____20656 ->
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
                                    let uu____20688 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____20688
                                     in
                                  let uu____20689 =
                                    let uu____20690 =
                                      FStar_Syntax_DsEnv.fail_or env2
                                        (FStar_Syntax_DsEnv.try_lookup_definition
                                           env2) l
                                       in
                                    FStar_All.pipe_left
                                      (FStar_Syntax_Subst.close binders1)
                                      uu____20690
                                     in
                                  ([], uu____20689)  in
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
                                      let uu____20707 =
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      ([], uu____20707)  in
                                    let uu____20714 =
                                      let uu____20715 =
                                        let uu____20716 =
                                          let uu____20717 = lookup1 "repr"
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____20717
                                           in
                                        let uu____20726 = lookup1 "return"
                                           in
                                        let uu____20727 = lookup1 "bind"  in
                                        let uu____20728 =
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
                                            uu____20716;
                                          FStar_Syntax_Syntax.return_repr =
                                            uu____20726;
                                          FStar_Syntax_Syntax.bind_repr =
                                            uu____20727;
                                          FStar_Syntax_Syntax.actions =
                                            actions1;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            uu____20728
                                        }  in
                                      FStar_Syntax_Syntax.Sig_new_effect_for_free
                                        uu____20715
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____20714;
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
                                         (fun uu___109_20734  ->
                                            match uu___109_20734 with
                                            | FStar_Syntax_Syntax.Reifiable 
                                                -> true
                                            | FStar_Syntax_Syntax.Reflectable
                                                uu____20735 -> true
                                            | uu____20736 -> false)
                                         qualifiers
                                        in
                                     let un_ts =
                                       ([], FStar_Syntax_Syntax.tun)  in
                                     let uu____20750 =
                                       let uu____20751 =
                                         let uu____20752 =
                                           lookup1 "return_wp"  in
                                         let uu____20753 = lookup1 "bind_wp"
                                            in
                                         let uu____20754 =
                                           lookup1 "if_then_else"  in
                                         let uu____20755 = lookup1 "ite_wp"
                                            in
                                         let uu____20756 = lookup1 "stronger"
                                            in
                                         let uu____20757 = lookup1 "close_wp"
                                            in
                                         let uu____20758 = lookup1 "assert_p"
                                            in
                                         let uu____20759 = lookup1 "assume_p"
                                            in
                                         let uu____20760 = lookup1 "null_wp"
                                            in
                                         let uu____20761 = lookup1 "trivial"
                                            in
                                         let uu____20762 =
                                           if rr
                                           then
                                             let uu____20763 = lookup1 "repr"
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.snd
                                               uu____20763
                                           else FStar_Syntax_Syntax.tun  in
                                         let uu____20779 =
                                           if rr
                                           then lookup1 "return"
                                           else un_ts  in
                                         let uu____20781 =
                                           if rr
                                           then lookup1 "bind"
                                           else un_ts  in
                                         let uu____20783 =
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
                                             uu____20752;
                                           FStar_Syntax_Syntax.bind_wp =
                                             uu____20753;
                                           FStar_Syntax_Syntax.if_then_else =
                                             uu____20754;
                                           FStar_Syntax_Syntax.ite_wp =
                                             uu____20755;
                                           FStar_Syntax_Syntax.stronger =
                                             uu____20756;
                                           FStar_Syntax_Syntax.close_wp =
                                             uu____20757;
                                           FStar_Syntax_Syntax.assert_p =
                                             uu____20758;
                                           FStar_Syntax_Syntax.assume_p =
                                             uu____20759;
                                           FStar_Syntax_Syntax.null_wp =
                                             uu____20760;
                                           FStar_Syntax_Syntax.trivial =
                                             uu____20761;
                                           FStar_Syntax_Syntax.repr =
                                             uu____20762;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____20779;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____20781;
                                           FStar_Syntax_Syntax.actions =
                                             actions1;
                                           FStar_Syntax_Syntax.eff_attrs =
                                             uu____20783
                                         }  in
                                       FStar_Syntax_Syntax.Sig_new_effect
                                         uu____20751
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         uu____20750;
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
                                          fun uu____20809  ->
                                            match uu____20809 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____20823 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____20823
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
                let uu____20847 = desugar_binders env1 eff_binders  in
                match uu____20847 with
                | (env2,binders) ->
                    let uu____20884 =
                      let uu____20903 = head_and_args defn  in
                      match uu____20903 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____20948 ->
                                let uu____20949 =
                                  let uu____20954 =
                                    let uu____20955 =
                                      let uu____20956 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.strcat uu____20956 " not found"
                                       in
                                    Prims.strcat "Effect " uu____20955  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____20954)
                                   in
                                FStar_Errors.raise_error uu____20949
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____20958 =
                            match FStar_List.rev args with
                            | (last_arg,uu____20988)::args_rev ->
                                let uu____21000 =
                                  let uu____21001 = unparen last_arg  in
                                  uu____21001.FStar_Parser_AST.tm  in
                                (match uu____21000 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____21029 -> ([], args))
                            | uu____21038 -> ([], args)  in
                          (match uu____20958 with
                           | (cattributes,args1) ->
                               let uu____21089 = desugar_args env2 args1  in
                               let uu____21098 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____21089, uu____21098))
                       in
                    (match uu____20884 with
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
                          (let uu____21154 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____21154 with
                           | (ed_binders,uu____21168,ed_binders_opening) ->
                               let sub1 uu____21181 =
                                 match uu____21181 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____21195 =
                                         FStar_Syntax_Subst.shift_subst
                                           (FStar_List.length us)
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____21195 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____21199 =
                                       let uu____21200 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____21200)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____21199
                                  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____21209 =
                                   let uu____21210 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____21210
                                    in
                                 let uu____21225 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____21226 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____21227 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____21228 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____21229 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____21230 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____21231 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____21232 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____21233 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____21234 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____21235 =
                                   let uu____21236 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____21236
                                    in
                                 let uu____21251 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____21252 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____21253 =
                                   FStar_List.map
                                     (fun action  ->
                                        let uu____21261 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____21262 =
                                          let uu____21263 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____21263
                                           in
                                        let uu____21278 =
                                          let uu____21279 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____21279
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____21261;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____21262;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____21278
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
                                     uu____21209;
                                   FStar_Syntax_Syntax.ret_wp = uu____21225;
                                   FStar_Syntax_Syntax.bind_wp = uu____21226;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____21227;
                                   FStar_Syntax_Syntax.ite_wp = uu____21228;
                                   FStar_Syntax_Syntax.stronger = uu____21229;
                                   FStar_Syntax_Syntax.close_wp = uu____21230;
                                   FStar_Syntax_Syntax.assert_p = uu____21231;
                                   FStar_Syntax_Syntax.assume_p = uu____21232;
                                   FStar_Syntax_Syntax.null_wp = uu____21233;
                                   FStar_Syntax_Syntax.trivial = uu____21234;
                                   FStar_Syntax_Syntax.repr = uu____21235;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____21251;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____21252;
                                   FStar_Syntax_Syntax.actions = uu____21253;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____21296 =
                                     let uu____21298 =
                                       let uu____21305 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____21305
                                        in
                                     FStar_List.length uu____21298  in
                                   uu____21296 = (Prims.parse_int "1")  in
                                 let uu____21331 =
                                   let uu____21334 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____21334 quals  in
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
                                   FStar_Syntax_Syntax.sigquals = uu____21331;
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
                                             let uu____21356 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____21356
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____21358 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____21358
                                 then
                                   let reflect_lid =
                                     let uu____21362 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____21362
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
    let uu____21372 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____21372 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.strcat "  " (Prims.strcat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____21423 ->
              let uu____21424 =
                let uu____21425 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____21425
                 in
              Prims.strcat "\n  " uu____21424
          | uu____21426 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____21439  ->
               match uu____21439 with
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
          let uu____21457 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____21457
            FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____21459 =
          let uu____21468 = FStar_Syntax_Syntax.as_arg arg  in [uu____21468]
           in
        FStar_Syntax_Util.mk_app fv uu____21459

and (desugar_decl :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      let uu____21493 = desugar_decl_noattrs env d  in
      match uu____21493 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____21511 = mk_comment_attr d  in uu____21511 :: attrs1  in
          let uu____21512 =
            FStar_List.map
              (fun sigelt  ->
                 let uu___136_21516 = sigelt  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___136_21516.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___136_21516.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___136_21516.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___136_21516.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs = attrs2
                 }) sigelts
             in
          (env1, uu____21512)

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
      | FStar_Parser_AST.Fsdoc uu____21542 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____21550 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____21550, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals  in
          let tcs1 =
            FStar_List.map
              (fun uu____21587  ->
                 match uu____21587 with | (x,uu____21595) -> x) tcs
             in
          let uu____21600 =
            FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals
             in
          desugar_tycon env d uu____21600 tcs1
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals  in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____21622;
                    FStar_Parser_AST.prange = uu____21623;_},uu____21624)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____21633;
                    FStar_Parser_AST.prange = uu____21634;_},uu____21635)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____21650;
                         FStar_Parser_AST.prange = uu____21651;_},uu____21652);
                    FStar_Parser_AST.prange = uu____21653;_},uu____21654)::[]
                   -> false
               | (p,uu____21682)::[] ->
                   let uu____21691 = is_app_pattern p  in
                   Prims.op_Negation uu____21691
               | uu____21692 -> false)
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
            let uu____21765 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____21765 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____21777 =
                     let uu____21778 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____21778.FStar_Syntax_Syntax.n  in
                   match uu____21777 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____21788) ->
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
                         | uu____21821::uu____21822 ->
                             FStar_List.map
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____21825 ->
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.collect
                                  (fun uu___110_21840  ->
                                     match uu___110_21840 with
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inl uu____21843;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____21844;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____21845;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____21846;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____21847;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____21848;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____21849;_}
                                         -> []
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____21861;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____21862;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____21863;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____21864;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____21865;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____21866;_}
                                         ->
                                         FStar_Syntax_DsEnv.lookup_letbinding_quals
                                           env
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                          in
                       let quals2 =
                         let uu____21880 =
                           FStar_All.pipe_right lets1
                             (FStar_Util.for_some
                                (fun uu____21911  ->
                                   match uu____21911 with
                                   | (uu____21924,(uu____21925,t)) ->
                                       t.FStar_Parser_AST.level =
                                         FStar_Parser_AST.Formula))
                            in
                         if uu____21880
                         then FStar_Syntax_Syntax.Logic :: quals1
                         else quals1  in
                       let lbs1 =
                         let uu____21943 =
                           FStar_All.pipe_right quals2
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract)
                            in
                         if uu____21943
                         then
                           let uu____21946 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu___137_21960 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___138_21962 = fv  in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___138_21962.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___138_21962.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___137_21960.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___137_21960.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___137_21960.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___137_21960.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___137_21960.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___137_21960.FStar_Syntax_Syntax.lbpos)
                                     }))
                              in
                           ((FStar_Pervasives_Native.fst lbs), uu____21946)
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
                   | uu____21989 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____21995 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____22014 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____21995 with
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
                       let uu___139_22050 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___139_22050.FStar_Parser_AST.prange)
                       }
                   | uu____22057 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___140_22064 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___140_22064.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___140_22064.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___140_22064.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____22100 id1 =
                   match uu____22100 with
                   | (env1,ses) ->
                       let main =
                         let uu____22121 =
                           let uu____22122 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____22122  in
                         FStar_Parser_AST.mk_term uu____22121
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
                       let uu____22172 = desugar_decl env1 id_decl  in
                       (match uu____22172 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____22190 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____22190 FStar_Util.set_elements
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
            let uu____22213 = close_fun env t  in
            desugar_term env uu____22213  in
          let quals1 =
            let uu____22217 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____22217
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let se =
            let uu____22223 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____22223;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in
          let env2 =
            FStar_Syntax_DsEnv.push_doc env1 lid d.FStar_Parser_AST.doc  in
          (env2, [se])
      | FStar_Parser_AST.Exception (id1,FStar_Pervasives_Native.None ) ->
          let uu____22231 =
            FStar_Syntax_DsEnv.fail_or env
              (FStar_Syntax_DsEnv.try_lookup_lid env)
              FStar_Parser_Const.exn_lid
             in
          (match uu____22231 with
           | (t,uu____22245) ->
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
            let uu____22275 =
              let uu____22282 = FStar_Syntax_Syntax.null_binder t  in
              [uu____22282]  in
            let uu____22295 =
              let uu____22298 =
                let uu____22299 =
                  FStar_Syntax_DsEnv.fail_or env
                    (FStar_Syntax_DsEnv.try_lookup_lid env)
                    FStar_Parser_Const.exn_lid
                   in
                FStar_Pervasives_Native.fst uu____22299  in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____22298
               in
            FStar_Syntax_Util.arrow uu____22275 uu____22295  in
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
            let uu____22360 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____22360 with
            | FStar_Pervasives_Native.None  ->
                let uu____22363 =
                  let uu____22368 =
                    let uu____22369 =
                      let uu____22370 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.strcat uu____22370 " not found"  in
                    Prims.strcat "Effect name " uu____22369  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____22368)  in
                FStar_Errors.raise_error uu____22363
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____22374 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____22416 =
                  let uu____22425 =
                    let uu____22432 = desugar_term env t  in
                    ([], uu____22432)  in
                  FStar_Pervasives_Native.Some uu____22425  in
                (uu____22416, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____22465 =
                  let uu____22474 =
                    let uu____22481 = desugar_term env wp  in
                    ([], uu____22481)  in
                  FStar_Pervasives_Native.Some uu____22474  in
                let uu____22490 =
                  let uu____22499 =
                    let uu____22506 = desugar_term env t  in
                    ([], uu____22506)  in
                  FStar_Pervasives_Native.Some uu____22499  in
                (uu____22465, uu____22490)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____22532 =
                  let uu____22541 =
                    let uu____22548 = desugar_term env t  in
                    ([], uu____22548)  in
                  FStar_Pervasives_Native.Some uu____22541  in
                (FStar_Pervasives_Native.None, uu____22532)
             in
          (match uu____22374 with
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
            let uu____22626 =
              let uu____22627 =
                let uu____22634 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____22634, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____22627  in
            {
              FStar_Syntax_Syntax.sigel = uu____22626;
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
      let uu____22660 =
        FStar_List.fold_left
          (fun uu____22680  ->
             fun d  ->
               match uu____22680 with
               | (env1,sigelts) ->
                   let uu____22700 = desugar_decl env1 d  in
                   (match uu____22700 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____22660 with
      | (env1,sigelts) ->
          let rec forward acc uu___112_22745 =
            match uu___112_22745 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____22759,FStar_Syntax_Syntax.Sig_let uu____22760) ->
                     let uu____22773 =
                       let uu____22776 =
                         let uu___141_22777 = se2  in
                         let uu____22778 =
                           let uu____22781 =
                             FStar_List.filter
                               (fun uu___111_22795  ->
                                  match uu___111_22795 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____22799;
                                           FStar_Syntax_Syntax.vars =
                                             uu____22800;_},uu____22801);
                                      FStar_Syntax_Syntax.pos = uu____22802;
                                      FStar_Syntax_Syntax.vars = uu____22803;_}
                                      when
                                      let uu____22826 =
                                        let uu____22827 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____22827
                                         in
                                      uu____22826 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____22828 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____22781
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___141_22777.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___141_22777.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___141_22777.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___141_22777.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____22778
                         }  in
                       uu____22776 :: se1 :: acc  in
                     forward uu____22773 sigelts1
                 | uu____22833 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____22841 = forward [] sigelts  in (env1, uu____22841)
  
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
      let uu____22883 =
        let uu____22896 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____22913  ->
               match uu____22913 with
               | ({ FStar_Syntax_Syntax.ppname = uu____22922;
                    FStar_Syntax_Syntax.index = uu____22923;
                    FStar_Syntax_Syntax.sort = t;_},uu____22925)
                   ->
                   let uu____22928 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____22928) uu____22896
         in
      FStar_All.pipe_right bs uu____22883  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____22942 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____22959 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____22985 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____23006,uu____23007,bs,t,uu____23010,uu____23011)
                            ->
                            let uu____23020 = bs_univnames bs  in
                            let uu____23023 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____23020 uu____23023
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____23026,uu____23027,t,uu____23029,uu____23030,uu____23031)
                            -> FStar_Syntax_Free.univnames t
                        | uu____23036 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____22985 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___142_23044 = s  in
        let uu____23045 =
          let uu____23046 =
            let uu____23055 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____23073,bs,t,lids1,lids2) ->
                          let uu___143_23086 = se  in
                          let uu____23087 =
                            let uu____23088 =
                              let uu____23105 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____23106 =
                                let uu____23107 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____23107 t  in
                              (lid, uvs, uu____23105, uu____23106, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____23088
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____23087;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___143_23086.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___143_23086.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___143_23086.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___143_23086.FStar_Syntax_Syntax.sigattrs)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____23119,t,tlid,n1,lids1) ->
                          let uu___144_23128 = se  in
                          let uu____23129 =
                            let uu____23130 =
                              let uu____23145 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____23145, tlid, n1, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____23130  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____23129;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___144_23128.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___144_23128.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___144_23128.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___144_23128.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____23148 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____23055, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____23046  in
        {
          FStar_Syntax_Syntax.sigel = uu____23045;
          FStar_Syntax_Syntax.sigrng =
            (uu___142_23044.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___142_23044.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___142_23044.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___142_23044.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____23154,t) ->
        let uvs =
          let uu____23157 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____23157 FStar_Util.set_elements  in
        let uu___145_23162 = s  in
        let uu____23163 =
          let uu____23164 =
            let uu____23171 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____23171)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____23164  in
        {
          FStar_Syntax_Syntax.sigel = uu____23163;
          FStar_Syntax_Syntax.sigrng =
            (uu___145_23162.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___145_23162.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___145_23162.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___145_23162.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____23193 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____23196 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____23203) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____23232,(FStar_Util.Inl t,uu____23234),uu____23235)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____23282,(FStar_Util.Inr c,uu____23284),uu____23285)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____23332 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____23333,(FStar_Util.Inl t,uu____23335),uu____23336) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____23383,(FStar_Util.Inr c,uu____23385),uu____23386) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____23433 -> empty_set  in
          FStar_Util.set_union uu____23193 uu____23196  in
        let all_lb_univs =
          let uu____23437 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____23453 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____23453) empty_set)
             in
          FStar_All.pipe_right uu____23437 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___146_23463 = s  in
        let uu____23464 =
          let uu____23465 =
            let uu____23472 =
              let uu____23473 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___147_23485 = lb  in
                        let uu____23486 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____23489 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___147_23485.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____23486;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___147_23485.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____23489;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___147_23485.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___147_23485.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____23473)  in
            (uu____23472, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____23465  in
        {
          FStar_Syntax_Syntax.sigel = uu____23464;
          FStar_Syntax_Syntax.sigrng =
            (uu___146_23463.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___146_23463.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___146_23463.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___146_23463.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____23497,fml) ->
        let uvs =
          let uu____23500 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____23500 FStar_Util.set_elements  in
        let uu___148_23505 = s  in
        let uu____23506 =
          let uu____23507 =
            let uu____23514 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____23514)  in
          FStar_Syntax_Syntax.Sig_assume uu____23507  in
        {
          FStar_Syntax_Syntax.sigel = uu____23506;
          FStar_Syntax_Syntax.sigrng =
            (uu___148_23505.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___148_23505.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___148_23505.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___148_23505.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____23516,bs,c,flags1) ->
        let uvs =
          let uu____23525 =
            let uu____23528 = bs_univnames bs  in
            let uu____23531 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____23528 uu____23531  in
          FStar_All.pipe_right uu____23525 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___149_23539 = s  in
        let uu____23540 =
          let uu____23541 =
            let uu____23554 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____23555 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____23554, uu____23555, flags1)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____23541  in
        {
          FStar_Syntax_Syntax.sigel = uu____23540;
          FStar_Syntax_Syntax.sigrng =
            (uu___149_23539.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___149_23539.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___149_23539.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___149_23539.FStar_Syntax_Syntax.sigattrs)
        }
    | uu____23558 -> s
  
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
          | (FStar_Pervasives_Native.None ,uu____23593) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____23597;
               FStar_Syntax_Syntax.exports = uu____23598;
               FStar_Syntax_Syntax.is_interface = uu____23599;_},FStar_Parser_AST.Module
             (current_lid,uu____23601)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____23609) ->
              let uu____23612 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____23612
           in
        let uu____23617 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____23653 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____23653, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____23670 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____23670, mname, decls, false)
           in
        match uu____23617 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____23700 = desugar_decls env2 decls  in
            (match uu____23700 with
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
          let uu____23765 =
            (FStar_Options.interactive ()) &&
              (let uu____23767 =
                 let uu____23768 =
                   let uu____23769 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____23769  in
                 FStar_Util.get_file_extension uu____23768  in
               FStar_List.mem uu____23767 ["fsti"; "fsi"])
             in
          if uu____23765 then as_interface m else m  in
        let uu____23773 = desugar_modul_common curmod env m1  in
        match uu____23773 with
        | (x,y,pop_when_done) ->
            (if pop_when_done
             then (let uu____23788 = FStar_Syntax_DsEnv.pop ()  in ())
             else ();
             (x, y))
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul ->
      (env_t,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun m  ->
      let uu____23808 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____23808 with
      | (env1,modul,pop_when_done) ->
          let uu____23822 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____23822 with
           | (env2,modul1) ->
               ((let uu____23834 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____23834
                 then
                   let uu____23835 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____23835
                 else ());
                (let uu____23837 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____23837, modul1))))
  
let (ast_modul_to_modul :
  FStar_Parser_AST.modul ->
    FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun env  ->
      let uu____23855 = desugar_modul env modul  in
      match uu____23855 with | (env1,modul1) -> (modul1, env1)
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      let uu____23886 = desugar_decls env decls  in
      match uu____23886 with | (env1,sigelts) -> (sigelts, env1)
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        let uu____23928 = desugar_partial_modul modul env a_modul  in
        match uu____23928 with | (env1,modul1) -> (modul1, env1)
  
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
              | uu____24014 ->
                  let t =
                    let uu____24022 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____24022  in
                  let uu____24033 =
                    let uu____24034 = FStar_Syntax_Subst.compress t  in
                    uu____24034.FStar_Syntax_Syntax.n  in
                  (match uu____24033 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____24044,uu____24045)
                       -> bs1
                   | uu____24066 -> failwith "Impossible")
               in
            let uu____24073 =
              let uu____24080 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____24080
                FStar_Syntax_Syntax.t_unit
               in
            match uu____24073 with
            | (binders,uu____24082,binders_opening) ->
                let erase_term t =
                  let uu____24090 =
                    let uu____24091 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____24091  in
                  FStar_Syntax_Subst.close binders uu____24090  in
                let erase_tscheme uu____24109 =
                  match uu____24109 with
                  | (us,t) ->
                      let t1 =
                        let uu____24129 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____24129 t  in
                      let uu____24132 =
                        let uu____24133 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____24133  in
                      ([], uu____24132)
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
                    | uu____24152 ->
                        let bs =
                          let uu____24160 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____24160  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____24192 =
                          let uu____24193 =
                            let uu____24196 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____24196  in
                          uu____24193.FStar_Syntax_Syntax.n  in
                        (match uu____24192 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____24198,uu____24199) -> bs1
                         | uu____24220 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____24227 =
                      let uu____24228 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____24228  in
                    FStar_Syntax_Subst.close binders uu____24227  in
                  let uu___150_24229 = action  in
                  let uu____24230 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____24231 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___150_24229.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___150_24229.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____24230;
                    FStar_Syntax_Syntax.action_typ = uu____24231
                  }  in
                let uu___151_24232 = ed  in
                let uu____24233 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____24234 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____24235 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____24236 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____24237 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____24238 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____24239 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____24240 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____24241 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____24242 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____24243 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____24244 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____24245 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____24246 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____24247 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____24248 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___151_24232.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___151_24232.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____24233;
                  FStar_Syntax_Syntax.signature = uu____24234;
                  FStar_Syntax_Syntax.ret_wp = uu____24235;
                  FStar_Syntax_Syntax.bind_wp = uu____24236;
                  FStar_Syntax_Syntax.if_then_else = uu____24237;
                  FStar_Syntax_Syntax.ite_wp = uu____24238;
                  FStar_Syntax_Syntax.stronger = uu____24239;
                  FStar_Syntax_Syntax.close_wp = uu____24240;
                  FStar_Syntax_Syntax.assert_p = uu____24241;
                  FStar_Syntax_Syntax.assume_p = uu____24242;
                  FStar_Syntax_Syntax.null_wp = uu____24243;
                  FStar_Syntax_Syntax.trivial = uu____24244;
                  FStar_Syntax_Syntax.repr = uu____24245;
                  FStar_Syntax_Syntax.return_repr = uu____24246;
                  FStar_Syntax_Syntax.bind_repr = uu____24247;
                  FStar_Syntax_Syntax.actions = uu____24248;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___151_24232.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___152_24264 = se  in
                  let uu____24265 =
                    let uu____24266 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____24266  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____24265;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___152_24264.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___152_24264.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___152_24264.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___152_24264.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___153_24270 = se  in
                  let uu____24271 =
                    let uu____24272 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____24272
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____24271;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___153_24270.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___153_24270.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___153_24270.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___153_24270.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____24274 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____24275 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____24275 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____24287 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____24287
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____24289 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____24289)
  