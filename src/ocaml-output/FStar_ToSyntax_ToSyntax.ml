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
  fun uu___201_66  ->
    match uu___201_66 with
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
      fun uu___202_90  ->
        match uu___202_90 with
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
  fun uu___203_99  ->
    match uu___203_99 with
    | FStar_Parser_AST.SetOptions s -> FStar_Syntax_Syntax.SetOptions s
    | FStar_Parser_AST.ResetOptions sopt ->
        FStar_Syntax_Syntax.ResetOptions sopt
    | FStar_Parser_AST.LightOff  -> FStar_Syntax_Syntax.LightOff
  
let (as_imp :
  FStar_Parser_AST.imp ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
  =
  fun uu___204_110  ->
    match uu___204_110 with
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
  fun uu___205_1710  ->
    match uu___205_1710 with
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
      fun uu___206_1756  ->
        match uu___206_1756 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____1784 = FStar_Syntax_Syntax.null_binder k  in
            (uu____1784, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____1793 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____1793 with
             | (env1,a1) ->
                 (((let uu___230_1819 = a1  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___230_1819.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___230_1819.FStar_Syntax_Syntax.index);
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
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___207_2175  ->
    match uu___207_2175 with
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
                  (fun uu___208_2388  ->
                     match uu___208_2388 with
                     | FStar_Util.Inr uu____2393 -> true
                     | uu____2394 -> false) univargs
              then
                let uu____2399 =
                  let uu____2400 =
                    FStar_List.map
                      (fun uu___209_2409  ->
                         match uu___209_2409 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____2400  in
                FStar_Util.Inr uu____2399
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___210_2426  ->
                        match uu___210_2426 with
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
            | FStar_Syntax_Syntax.Pat_dot_term uu____2949 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_wild uu____2956 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_constant uu____2957 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_var x ->
                FStar_Util.set_add x FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_cons (uu____2959,pats1) ->
                let aux out uu____2997 =
                  match uu____2997 with
                  | (p2,uu____3009) ->
                      let intersection =
                        let uu____3017 = pat_vars p2  in
                        FStar_Util.set_intersect uu____3017 out  in
                      let uu____3020 = FStar_Util.set_is_empty intersection
                         in
                      if uu____3020
                      then
                        let uu____3023 = pat_vars p2  in
                        FStar_Util.set_union out uu____3023
                      else
                        (let duplicate_bv =
                           let uu____3028 =
                             FStar_Util.set_elements intersection  in
                           FStar_List.hd uu____3028  in
                         let uu____3031 =
                           let uu____3036 =
                             FStar_Util.format1
                               "Non-linear patterns are not permitted. %s appears more than once in this pattern."
                               (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                              in
                           (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                             uu____3036)
                            in
                         FStar_Errors.raise_error uu____3031 r)
                   in
                FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
             in
          match pats with
          | [] -> ()
          | p1::[] ->
              let uu____3056 = pat_vars p1  in
              FStar_All.pipe_right uu____3056 (fun a237  -> ())
          | p1::ps ->
              let pvars = pat_vars p1  in
              let aux p2 =
                let uu____3084 =
                  let uu____3085 = pat_vars p2  in
                  FStar_Util.set_eq pvars uu____3085  in
                if uu____3084
                then ()
                else
                  (let nonlinear_vars =
                     let uu____3092 = pat_vars p2  in
                     FStar_Util.set_symmetric_difference pvars uu____3092  in
                   let first_nonlinear_var =
                     let uu____3096 = FStar_Util.set_elements nonlinear_vars
                        in
                     FStar_List.hd uu____3096  in
                   let uu____3099 =
                     let uu____3104 =
                       FStar_Util.format1
                         "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                         (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                        in
                     (FStar_Errors.Fatal_IncoherentPatterns, uu____3104)  in
                   FStar_Errors.raise_error uu____3099 r)
                 in
              FStar_List.iter aux ps
           in
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false ,uu____3108) -> ()
         | (true ,FStar_Parser_AST.PatVar uu____3109) -> ()
         | (true ,uu____3116) ->
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_LetMutableForVariablesOnly,
                 "let-mutable is for variables only")
               p.FStar_Parser_AST.prange);
        (let resolvex l e x =
           let uu____3139 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText))
              in
           match uu____3139 with
           | FStar_Pervasives_Native.Some y -> (l, e, y)
           | uu____3155 ->
               let uu____3158 =
                 if is_mut
                 then FStar_Syntax_DsEnv.push_bv_mutable e x
                 else FStar_Syntax_DsEnv.push_bv e x  in
               (match uu____3158 with | (e1,x1) -> ((x1 :: l), e1, x1))
            in
         let rec aux' top loc env1 p1 =
           let pos q =
             FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange  in
           let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
           let orig = p1  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr uu____3270 -> failwith "impossible"
           | FStar_Parser_AST.PatOp op ->
               let uu____3286 =
                 let uu____3287 =
                   let uu____3288 =
                     let uu____3295 =
                       let uu____3296 =
                         let uu____3301 =
                           FStar_Parser_AST.compile_op (Prims.parse_int "0")
                             op.FStar_Ident.idText op.FStar_Ident.idRange
                            in
                         (uu____3301, (op.FStar_Ident.idRange))  in
                       FStar_Ident.mk_ident uu____3296  in
                     (uu____3295, FStar_Pervasives_Native.None)  in
                   FStar_Parser_AST.PatVar uu____3288  in
                 {
                   FStar_Parser_AST.pat = uu____3287;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 }  in
               aux loc env1 uu____3286
           | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
               ((match tacopt with
                 | FStar_Pervasives_Native.None  -> ()
                 | FStar_Pervasives_Native.Some uu____3318 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                         "Type ascriptions within patterns are cannot be associated with a tactic")
                       orig.FStar_Parser_AST.prange);
                (let uu____3319 = aux loc env1 p2  in
                 match uu____3319 with
                 | (loc1,env',binder,p3,imp) ->
                     let annot_pat_var p4 t1 =
                       match p4.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let uu___231_3377 = p4  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var
                                  (let uu___232_3382 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___232_3382.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___232_3382.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }));
                             FStar_Syntax_Syntax.p =
                               (uu___231_3377.FStar_Syntax_Syntax.p)
                           }
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let uu___233_3384 = p4  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild
                                  (let uu___234_3389 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___234_3389.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___234_3389.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }));
                             FStar_Syntax_Syntax.p =
                               (uu___233_3384.FStar_Syntax_Syntax.p)
                           }
                       | uu____3390 when top -> p4
                       | uu____3391 ->
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                               "Type ascriptions within patterns are only allowed on variables")
                             orig.FStar_Parser_AST.prange
                        in
                     let uu____3394 =
                       match binder with
                       | LetBinder uu____3407 -> failwith "impossible"
                       | LocalBinder (x,aq) ->
                           let t1 =
                             let uu____3427 = close_fun env1 t  in
                             desugar_term env1 uu____3427  in
                           (if
                              (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                               with
                               | FStar_Syntax_Syntax.Tm_unknown  -> false
                               | uu____3429 -> true)
                            then
                              (let uu____3430 =
                                 let uu____3435 =
                                   let uu____3436 =
                                     FStar_Syntax_Print.bv_to_string x  in
                                   let uu____3437 =
                                     FStar_Syntax_Print.term_to_string
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____3438 =
                                     FStar_Syntax_Print.term_to_string t1  in
                                   FStar_Util.format3
                                     "Multiple ascriptions for %s in pattern, type %s was shadowed by %s\n"
                                     uu____3436 uu____3437 uu____3438
                                    in
                                 (FStar_Errors.Warning_MultipleAscriptions,
                                   uu____3435)
                                  in
                               FStar_Errors.log_issue
                                 orig.FStar_Parser_AST.prange uu____3430)
                            else ();
                            (let uu____3440 = annot_pat_var p3 t1  in
                             (uu____3440,
                               (LocalBinder
                                  ((let uu___235_3446 = x  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___235_3446.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___235_3446.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    }), aq)))))
                        in
                     (match uu____3394 with
                      | (p4,binder1) -> (loc1, env', binder1, p4, imp))))
           | FStar_Parser_AST.PatWild  ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____3468 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____3468, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____3477 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____3477, false)
           | FStar_Parser_AST.PatTvar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual aq  in
               let uu____3496 = resolvex loc env1 x  in
               (match uu____3496 with
                | (loc1,env2,xbv) ->
                    let uu____3518 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____3518, imp))
           | FStar_Parser_AST.PatVar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual aq  in
               let uu____3537 = resolvex loc env1 x  in
               (match uu____3537 with
                | (loc1,env2,xbv) ->
                    let uu____3559 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____3559, imp))
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
               let uu____3569 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, []))
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____3569, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____3591;_},args)
               ->
               let uu____3597 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____3638  ->
                        match uu____3638 with
                        | (loc1,env2,args1) ->
                            let uu____3686 = aux loc1 env2 arg  in
                            (match uu____3686 with
                             | (loc2,env3,uu____3715,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, [])
                  in
               (match uu____3597 with
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
                    let uu____3785 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                       in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)),
                      uu____3785, false))
           | FStar_Parser_AST.PatApp uu____3800 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                 p1.FStar_Parser_AST.prange
           | FStar_Parser_AST.PatList pats ->
               let uu____3822 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____3855  ->
                        match uu____3855 with
                        | (loc1,env2,pats1) ->
                            let uu____3887 = aux loc1 env2 pat  in
                            (match uu____3887 with
                             | (loc2,env3,uu____3912,pat1,uu____3914) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, [])
                  in
               (match uu____3822 with
                | (loc1,env2,pats1) ->
                    let pat =
                      let uu____3957 =
                        let uu____3960 =
                          let uu____3967 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange
                             in
                          pos_r uu____3967  in
                        let uu____3968 =
                          let uu____3969 =
                            let uu____3982 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Parser_Const.nil_lid
                                FStar_Syntax_Syntax.delta_constant
                                (FStar_Pervasives_Native.Some
                                   FStar_Syntax_Syntax.Data_ctor)
                               in
                            (uu____3982, [])  in
                          FStar_Syntax_Syntax.Pat_cons uu____3969  in
                        FStar_All.pipe_left uu____3960 uu____3968  in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p
                                in
                             let uu____4014 =
                               let uu____4015 =
                                 let uu____4028 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.cons_lid
                                     FStar_Syntax_Syntax.delta_constant
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Data_ctor)
                                    in
                                 (uu____4028, [(hd1, false); (tl1, false)])
                                  in
                               FStar_Syntax_Syntax.Pat_cons uu____4015  in
                             FStar_All.pipe_left (pos_r r) uu____4014) pats1
                        uu____3957
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
               let uu____4070 =
                 FStar_List.fold_left
                   (fun uu____4110  ->
                      fun p2  ->
                        match uu____4110 with
                        | (loc1,env2,pats) ->
                            let uu____4159 = aux loc1 env2 p2  in
                            (match uu____4159 with
                             | (loc2,env3,uu____4188,pat,uu____4190) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args
                  in
               (match uu____4070 with
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
                    let uu____4285 =
                      FStar_Syntax_DsEnv.fail_or env2
                        (FStar_Syntax_DsEnv.try_lookup_lid env2) l
                       in
                    (match uu____4285 with
                     | (constr,uu____4307) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____4310 -> failwith "impossible"  in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (FStar_Pervasives_Native.Some
                                (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun
                            in
                         let uu____4312 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                            in
                         (loc1, env2,
                           (LocalBinder (x, FStar_Pervasives_Native.None)),
                           uu____4312, false)))
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
                      (fun uu____4381  ->
                         match uu____4381 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2)))
                  in
               let args =
                 FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                   (FStar_List.map
                      (fun uu____4411  ->
                         match uu____4411 with
                         | (f,uu____4417) ->
                             let uu____4418 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____4444  ->
                                       match uu____4444 with
                                       | (g,uu____4450) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText))
                                in
                             (match uu____4418 with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
                              | FStar_Pervasives_Native.Some (uu____4455,p2)
                                  -> p2)))
                  in
               let app =
                 let uu____4462 =
                   let uu____4463 =
                     let uu____4470 =
                       let uu____4471 =
                         let uu____4472 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                                [record.FStar_Syntax_DsEnv.constrname])
                            in
                         FStar_Parser_AST.PatName uu____4472  in
                       FStar_Parser_AST.mk_pattern uu____4471
                         p1.FStar_Parser_AST.prange
                        in
                     (uu____4470, args)  in
                   FStar_Parser_AST.PatApp uu____4463  in
                 FStar_Parser_AST.mk_pattern uu____4462
                   p1.FStar_Parser_AST.prange
                  in
               let uu____4475 = aux loc env1 app  in
               (match uu____4475 with
                | (env2,e,b,p2,uu____4504) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____4532 =
                            let uu____4533 =
                              let uu____4546 =
                                let uu___236_4547 = fv  in
                                let uu____4548 =
                                  let uu____4551 =
                                    let uu____4552 =
                                      let uu____4559 =
                                        FStar_All.pipe_right
                                          record.FStar_Syntax_DsEnv.fields
                                          (FStar_List.map
                                             FStar_Pervasives_Native.fst)
                                         in
                                      ((record.FStar_Syntax_DsEnv.typename),
                                        uu____4559)
                                       in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____4552
                                     in
                                  FStar_Pervasives_Native.Some uu____4551  in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___236_4547.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___236_4547.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____4548
                                }  in
                              (uu____4546, args1)  in
                            FStar_Syntax_Syntax.Pat_cons uu____4533  in
                          FStar_All.pipe_left pos uu____4532
                      | uu____4586 -> p2  in
                    (env2, e, b, p3, false))
         
         and aux loc env1 p1 = aux' false loc env1 p1
          in
         let aux_maybe_or env1 p1 =
           let loc = []  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____4640 = aux' true loc env1 p2  in
               (match uu____4640 with
                | (loc1,env2,var,p3,uu____4667) ->
                    let uu____4672 =
                      FStar_List.fold_left
                        (fun uu____4704  ->
                           fun p4  ->
                             match uu____4704 with
                             | (loc2,env3,ps1) ->
                                 let uu____4737 = aux' true loc2 env3 p4  in
                                 (match uu____4737 with
                                  | (loc3,env4,uu____4762,p5,uu____4764) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps
                       in
                    (match uu____4672 with
                     | (loc2,env3,ps1) ->
                         let pats = p3 :: (FStar_List.rev ps1)  in
                         (env3, var, pats)))
           | uu____4815 ->
               let uu____4816 = aux' true loc env1 p1  in
               (match uu____4816 with
                | (loc1,env2,vars,pat,b) -> (env2, vars, [pat]))
            in
         let uu____4856 = aux_maybe_or env p  in
         match uu____4856 with
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
            let uu____4915 =
              let uu____4916 =
                let uu____4927 = FStar_Syntax_DsEnv.qualify env x  in
                (uu____4927,
                  (FStar_Syntax_Syntax.tun, FStar_Pervasives_Native.None))
                 in
              LetBinder uu____4916  in
            (env, uu____4915, [])  in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____4955 =
                  let uu____4956 =
                    let uu____4961 =
                      FStar_Parser_AST.compile_op (Prims.parse_int "0")
                        x.FStar_Ident.idText x.FStar_Ident.idRange
                       in
                    (uu____4961, (x.FStar_Ident.idRange))  in
                  FStar_Ident.mk_ident uu____4956  in
                mklet uu____4955
            | FStar_Parser_AST.PatVar (x,uu____4963) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____4969);
                   FStar_Parser_AST.prange = uu____4970;_},(t,tacopt))
                ->
                let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)
                   in
                let uu____4990 =
                  let uu____4991 =
                    let uu____5002 = FStar_Syntax_DsEnv.qualify env x  in
                    let uu____5003 =
                      let uu____5010 = desugar_term env t  in
                      (uu____5010, tacopt1)  in
                    (uu____5002, uu____5003)  in
                  LetBinder uu____4991  in
                (env, uu____4990, [])
            | uu____5021 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_UnexpectedPattern,
                    "Unexpected pattern at the top-level")
                  p.FStar_Parser_AST.prange
          else
            (let uu____5031 = desugar_data_pat env p is_mut  in
             match uu____5031 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1 with
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                         uu____5060;
                       FStar_Syntax_Syntax.p = uu____5061;_}::[] -> []
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                         uu____5062;
                       FStar_Syntax_Syntax.p = uu____5063;_}::[] -> []
                   | uu____5064 -> p1  in
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
  fun uu____5071  ->
    fun env  ->
      fun pat  ->
        let uu____5074 = desugar_data_pat env pat false  in
        match uu____5074 with | (env1,uu____5090,pat1) -> (env1, pat1)

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
      let uu____5109 = desugar_term_aq env e  in
      match uu____5109 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____5126 = desugar_typ_aq env e  in
      match uu____5126 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness,FStar_Const.width)
        FStar_Pervasives_Native.tuple2 ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____5136  ->
        fun range  ->
          match uu____5136 with
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
              ((let uu____5146 =
                  let uu____5147 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____5147  in
                if uu____5146
                then
                  let uu____5148 =
                    let uu____5153 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____5153)  in
                  FStar_Errors.log_issue range uu____5148
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
                  let uu____5158 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____5158 range  in
                let lid1 =
                  let uu____5162 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____5162 with
                  | FStar_Pervasives_Native.Some (intro_term,uu____5172) ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____5181 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____5181 range  in
                           let private_fv =
                             let uu____5183 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____5183 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___237_5184 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___237_5184.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___237_5184.FStar_Syntax_Syntax.vars)
                           }
                       | uu____5185 ->
                           failwith
                             (Prims.strcat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____5192 =
                        let uu____5197 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____5197)
                         in
                      FStar_Errors.raise_error uu____5192 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____5213 =
                  let uu____5220 =
                    let uu____5221 =
                      let uu____5236 =
                        let uu____5245 =
                          let uu____5252 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____5252)  in
                        [uu____5245]  in
                      (lid1, uu____5236)  in
                    FStar_Syntax_Syntax.Tm_app uu____5221  in
                  FStar_Syntax_Syntax.mk uu____5220  in
                uu____5213 FStar_Pervasives_Native.None range))

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
            let uu____5291 =
              let uu____5300 =
                (if resolve
                 then FStar_Syntax_DsEnv.try_lookup_lid_with_attributes
                 else
                   FStar_Syntax_DsEnv.try_lookup_lid_with_attributes_no_resolve)
                  env
                 in
              FStar_Syntax_DsEnv.fail_or env uu____5300 l  in
            match uu____5291 with
            | (tm,mut,attrs) ->
                let warn_if_deprecated attrs1 =
                  FStar_List.iter
                    (fun a  ->
                       match a.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_app
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____5355;
                              FStar_Syntax_Syntax.vars = uu____5356;_},args)
                           when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____5379 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____5379 " is deprecated"  in
                           let msg1 =
                             if
                               (FStar_List.length args) >
                                 (Prims.parse_int "0")
                             then
                               let uu____5387 =
                                 let uu____5388 =
                                   let uu____5391 = FStar_List.hd args  in
                                   FStar_Pervasives_Native.fst uu____5391  in
                                 uu____5388.FStar_Syntax_Syntax.n  in
                               match uu____5387 with
                               | FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_string (s,uu____5407))
                                   when
                                   Prims.op_Negation
                                     ((FStar_Util.trim_string s) = "")
                                   ->
                                   Prims.strcat msg
                                     (Prims.strcat ", use "
                                        (Prims.strcat s " instead"))
                               | uu____5408 -> msg
                             else msg  in
                           let uu____5410 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____5410
                             (FStar_Errors.Warning_DeprecatedDefinition,
                               msg1)
                       | FStar_Syntax_Syntax.Tm_fvar fv when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____5413 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____5413 " is deprecated"  in
                           let uu____5414 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____5414
                             (FStar_Errors.Warning_DeprecatedDefinition, msg)
                       | uu____5415 -> ()) attrs1
                   in
                (warn_if_deprecated attrs;
                 (let tm1 = setpos tm  in
                  if mut
                  then
                    let uu____5420 =
                      let uu____5421 =
                        let uu____5428 = mk_ref_read tm1  in
                        (uu____5428,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Mutable_rval))
                         in
                      FStar_Syntax_Syntax.Tm_meta uu____5421  in
                    FStar_All.pipe_left mk1 uu____5420
                  else tm1))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____5446 =
          let uu____5447 = unparen t  in uu____5447.FStar_Parser_AST.tm  in
        match uu____5446 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____5448; FStar_Ident.ident = uu____5449;
              FStar_Ident.nsstr = uu____5450; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____5453 ->
            let uu____5454 =
              let uu____5459 =
                let uu____5460 = FStar_Parser_AST.term_to_string t  in
                Prims.strcat "Unknown attribute " uu____5460  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____5459)  in
            FStar_Errors.raise_error uu____5454 t.FStar_Parser_AST.range
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
          let uu___238_5555 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___238_5555.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___238_5555.FStar_Syntax_Syntax.vars)
          }  in
        let uu____5558 =
          let uu____5559 = unparen top  in uu____5559.FStar_Parser_AST.tm  in
        match uu____5558 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____5564 ->
            let uu____5571 = desugar_formula env top  in (uu____5571, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____5578 = desugar_formula env t  in (uu____5578, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____5585 = desugar_formula env t  in (uu____5585, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____5609 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____5609, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____5611 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____5611, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____5619 =
                let uu____5620 =
                  let uu____5627 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____5627, args)  in
                FStar_Parser_AST.Op uu____5620  in
              FStar_Parser_AST.mk_term uu____5619 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____5630 =
              let uu____5631 =
                let uu____5632 =
                  let uu____5639 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____5639, [e])  in
                FStar_Parser_AST.Op uu____5632  in
              FStar_Parser_AST.mk_term uu____5631 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____5630
        | FStar_Parser_AST.Op (op_star,uu____5643::uu____5644::[]) when
            (let uu____5649 = FStar_Ident.text_of_id op_star  in
             uu____5649 = "*") &&
              (let uu____5651 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____5651 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____5666;_},t1::t2::[])
                  ->
                  let uu____5671 = flatten1 t1  in
                  FStar_List.append uu____5671 [t2]
              | uu____5674 -> [t]  in
            let uu____5675 =
              let uu____5700 =
                let uu____5723 =
                  let uu____5726 = unparen top  in flatten1 uu____5726  in
                FStar_All.pipe_right uu____5723
                  (FStar_List.map
                     (fun t  ->
                        let uu____5745 = desugar_typ_aq env t  in
                        match uu____5745 with
                        | (t',aq) ->
                            let uu____5756 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____5756, aq)))
                 in
              FStar_All.pipe_right uu____5700 FStar_List.unzip  in
            (match uu____5675 with
             | (targs,aqs) ->
                 let uu____5865 =
                   let uu____5870 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____5870
                    in
                 (match uu____5865 with
                  | (tup,uu____5886) ->
                      let uu____5887 =
                        mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                      (uu____5887, (join_aqs aqs))))
        | FStar_Parser_AST.Tvar a ->
            let uu____5899 =
              let uu____5900 =
                let uu____5903 =
                  FStar_Syntax_DsEnv.fail_or2
                    (FStar_Syntax_DsEnv.try_lookup_id env) a
                   in
                FStar_Pervasives_Native.fst uu____5903  in
              FStar_All.pipe_left setpos uu____5900  in
            (uu____5899, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____5915 =
              let uu____5920 =
                let uu____5921 =
                  let uu____5922 = FStar_Ident.text_of_id u  in
                  Prims.strcat uu____5922 " in non-universe context"  in
                Prims.strcat "Unexpected universe variable " uu____5921  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____5920)  in
            FStar_Errors.raise_error uu____5915 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____5933 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____5933 with
             | FStar_Pervasives_Native.None  ->
                 let uu____5940 =
                   let uu____5945 =
                     let uu____5946 = FStar_Ident.text_of_id s  in
                     Prims.strcat "Unexpected or unbound operator: "
                       uu____5946
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____5945)
                    in
                 FStar_Errors.raise_error uu____5940
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let uu____5956 =
                     let uu____5981 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____6033 = desugar_term_aq env t  in
                               match uu____6033 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____5981 FStar_List.unzip  in
                   (match uu____5956 with
                    | (args1,aqs) ->
                        let uu____6166 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____6166, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____6180)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____6195 =
              let uu___239_6196 = top  in
              let uu____6197 =
                let uu____6198 =
                  let uu____6205 =
                    let uu___240_6206 = top  in
                    let uu____6207 =
                      let uu____6208 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____6208  in
                    {
                      FStar_Parser_AST.tm = uu____6207;
                      FStar_Parser_AST.range =
                        (uu___240_6206.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___240_6206.FStar_Parser_AST.level)
                    }  in
                  (uu____6205, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____6198  in
              {
                FStar_Parser_AST.tm = uu____6197;
                FStar_Parser_AST.range =
                  (uu___239_6196.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___239_6196.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____6195
        | FStar_Parser_AST.Construct (n1,(a,uu____6211)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____6227 =
                let uu___241_6228 = top  in
                let uu____6229 =
                  let uu____6230 =
                    let uu____6237 =
                      let uu___242_6238 = top  in
                      let uu____6239 =
                        let uu____6240 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____6240  in
                      {
                        FStar_Parser_AST.tm = uu____6239;
                        FStar_Parser_AST.range =
                          (uu___242_6238.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___242_6238.FStar_Parser_AST.level)
                      }  in
                    (uu____6237, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____6230  in
                {
                  FStar_Parser_AST.tm = uu____6229;
                  FStar_Parser_AST.range =
                    (uu___241_6228.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___241_6228.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____6227))
        | FStar_Parser_AST.Construct (n1,(a,uu____6243)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____6258 =
              let uu___243_6259 = top  in
              let uu____6260 =
                let uu____6261 =
                  let uu____6268 =
                    let uu___244_6269 = top  in
                    let uu____6270 =
                      let uu____6271 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____6271  in
                    {
                      FStar_Parser_AST.tm = uu____6270;
                      FStar_Parser_AST.range =
                        (uu___244_6269.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___244_6269.FStar_Parser_AST.level)
                    }  in
                  (uu____6268, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____6261  in
              {
                FStar_Parser_AST.tm = uu____6260;
                FStar_Parser_AST.range =
                  (uu___243_6259.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___243_6259.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____6258
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____6272; FStar_Ident.ident = uu____6273;
              FStar_Ident.nsstr = uu____6274; FStar_Ident.str = "Type0";_}
            ->
            let uu____6277 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____6277, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____6278; FStar_Ident.ident = uu____6279;
              FStar_Ident.nsstr = uu____6280; FStar_Ident.str = "Type";_}
            ->
            let uu____6283 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____6283, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____6284; FStar_Ident.ident = uu____6285;
               FStar_Ident.nsstr = uu____6286; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____6304 =
              let uu____6305 =
                let uu____6306 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____6306  in
              mk1 uu____6305  in
            (uu____6304, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____6307; FStar_Ident.ident = uu____6308;
              FStar_Ident.nsstr = uu____6309; FStar_Ident.str = "Effect";_}
            ->
            let uu____6312 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____6312, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____6313; FStar_Ident.ident = uu____6314;
              FStar_Ident.nsstr = uu____6315; FStar_Ident.str = "True";_}
            ->
            let uu____6318 =
              let uu____6319 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____6319
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____6318, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____6320; FStar_Ident.ident = uu____6321;
              FStar_Ident.nsstr = uu____6322; FStar_Ident.str = "False";_}
            ->
            let uu____6325 =
              let uu____6326 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____6326
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____6325, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____6329;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____6331 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____6331 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____6340 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_constant_at_level
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None
                     in
                  (uu____6340, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____6341 =
                    let uu____6342 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____6342 txt
                     in
                  failwith uu____6341))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____6349 = desugar_name mk1 setpos env true l  in
              (uu____6349, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____6352 = desugar_name mk1 setpos env true l  in
              (uu____6352, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____6363 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____6363 with
                | FStar_Pervasives_Native.Some uu____6372 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____6377 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____6377 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____6391 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____6408 =
                    let uu____6409 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____6409  in
                  (uu____6408, noaqs)
              | uu____6410 ->
                  let uu____6417 =
                    let uu____6422 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____6422)  in
                  FStar_Errors.raise_error uu____6417
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____6429 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____6429 with
              | FStar_Pervasives_Native.None  ->
                  let uu____6436 =
                    let uu____6441 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____6441)
                     in
                  FStar_Errors.raise_error uu____6436
                    top.FStar_Parser_AST.range
              | uu____6446 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____6450 = desugar_name mk1 setpos env true lid'  in
                  (uu____6450, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____6466 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____6466 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____6485 ->
                       let uu____6492 =
                         FStar_Util.take
                           (fun uu____6516  ->
                              match uu____6516 with
                              | (uu____6521,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____6492 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____6566 =
                              let uu____6591 =
                                FStar_List.map
                                  (fun uu____6634  ->
                                     match uu____6634 with
                                     | (t,imp) ->
                                         let uu____6651 =
                                           desugar_term_aq env t  in
                                         (match uu____6651 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____6591
                                FStar_List.unzip
                               in
                            (match uu____6566 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____6792 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____6792, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____6808 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____6808 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.strcat "Constructor "
                             (Prims.strcat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____6815 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.strcat "Effect "
                             (Prims.strcat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____6826 =
              FStar_List.fold_left
                (fun uu____6871  ->
                   fun b  ->
                     match uu____6871 with
                     | (env1,tparams,typs) ->
                         let uu____6928 = desugar_binder env1 b  in
                         (match uu____6928 with
                          | (xopt,t1) ->
                              let uu____6957 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____6966 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____6966)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____6957 with
                               | (env2,x) ->
                                   let uu____6986 =
                                     let uu____6989 =
                                       let uu____6992 =
                                         let uu____6993 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____6993
                                          in
                                       [uu____6992]  in
                                     FStar_List.append typs uu____6989  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___245_7019 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___245_7019.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___245_7019.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____6986)))) (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      FStar_Pervasives_Native.None])
               in
            (match uu____6826 with
             | (env1,uu____7047,targs) ->
                 let uu____7069 =
                   let uu____7074 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____7074
                    in
                 (match uu____7069 with
                  | (tup,uu____7084) ->
                      let uu____7085 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_app (tup, targs))
                         in
                      (uu____7085, noaqs)))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____7102 = uncurry binders t  in
            (match uu____7102 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___211_7144 =
                   match uu___211_7144 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1  in
                       let uu____7158 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____7158
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____7180 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____7180 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____7213 = aux env [] bs  in (uu____7213, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____7220 = desugar_binder env b  in
            (match uu____7220 with
             | (FStar_Pervasives_Native.None ,uu____7231) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____7245 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____7245 with
                  | ((x,uu____7261),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____7274 =
                        let uu____7275 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____7275  in
                      (uu____7274, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern)
               in
            let uu____7293 =
              FStar_List.fold_left
                (fun uu____7313  ->
                   fun pat  ->
                     match uu____7313 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed
                              (uu____7339,(t,FStar_Pervasives_Native.None ))
                              ->
                              let uu____7349 =
                                let uu____7352 = free_type_vars env1 t  in
                                FStar_List.append uu____7352 ftvs  in
                              (env1, uu____7349)
                          | FStar_Parser_AST.PatAscribed
                              (uu____7357,(t,FStar_Pervasives_Native.Some
                                           tac))
                              ->
                              let uu____7368 =
                                let uu____7371 = free_type_vars env1 t  in
                                let uu____7374 =
                                  let uu____7377 = free_type_vars env1 tac
                                     in
                                  FStar_List.append uu____7377 ftvs  in
                                FStar_List.append uu____7371 uu____7374  in
                              (env1, uu____7368)
                          | uu____7382 -> (env1, ftvs))) (env, []) binders1
               in
            (match uu____7293 with
             | (uu____7391,ftv) ->
                 let ftv1 = sort_ftv ftv  in
                 let binders2 =
                   let uu____7403 =
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
                   FStar_List.append uu____7403 binders1  in
                 let rec aux env1 bs sc_pat_opt uu___212_7458 =
                   match uu___212_7458 with
                   | [] ->
                       let uu____7483 = desugar_term_aq env1 body  in
                       (match uu____7483 with
                        | (body1,aq) ->
                            let body2 =
                              match sc_pat_opt with
                              | FStar_Pervasives_Native.Some (sc,pat) ->
                                  let body2 =
                                    let uu____7520 =
                                      let uu____7521 =
                                        FStar_Syntax_Syntax.pat_bvs pat  in
                                      FStar_All.pipe_right uu____7521
                                        (FStar_List.map
                                           FStar_Syntax_Syntax.mk_binder)
                                       in
                                    FStar_Syntax_Subst.close uu____7520 body1
                                     in
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_match
                                       (sc,
                                         [(pat, FStar_Pervasives_Native.None,
                                            body2)]))
                                    FStar_Pervasives_Native.None
                                    body2.FStar_Syntax_Syntax.pos
                              | FStar_Pervasives_Native.None  -> body1  in
                            let uu____7590 =
                              let uu____7593 =
                                no_annot_abs (FStar_List.rev bs) body2  in
                              setpos uu____7593  in
                            (uu____7590, aq))
                   | p::rest ->
                       let uu____7606 = desugar_binding_pat env1 p  in
                       (match uu____7606 with
                        | (env2,b,pat) ->
                            let pat1 =
                              match pat with
                              | [] -> FStar_Pervasives_Native.None
                              | p1::[] -> FStar_Pervasives_Native.Some p1
                              | uu____7640 ->
                                  FStar_Errors.raise_error
                                    (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                      "Disjunctive patterns are not supported in abstractions")
                                    p.FStar_Parser_AST.prange
                               in
                            let uu____7647 =
                              match b with
                              | LetBinder uu____7684 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat1, sc_pat_opt) with
                                    | (FStar_Pervasives_Native.None
                                       ,uu____7750) -> sc_pat_opt
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.None ) ->
                                        let uu____7804 =
                                          let uu____7811 =
                                            FStar_Syntax_Syntax.bv_to_name x
                                             in
                                          (uu____7811, p1)  in
                                        FStar_Pervasives_Native.Some
                                          uu____7804
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.Some
                                       (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____7867,uu____7868) ->
                                             let tup2 =
                                               let uu____7870 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____7870
                                                 FStar_Syntax_Syntax.delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____7874 =
                                                 let uu____7881 =
                                                   let uu____7882 =
                                                     let uu____7897 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2)
                                                        in
                                                     let uu____7900 =
                                                       let uu____7909 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc
                                                          in
                                                       let uu____7916 =
                                                         let uu____7925 =
                                                           let uu____7932 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x
                                                              in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____7932
                                                            in
                                                         [uu____7925]  in
                                                       uu____7909 ::
                                                         uu____7916
                                                        in
                                                     (uu____7897, uu____7900)
                                                      in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____7882
                                                    in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____7881
                                                  in
                                               uu____7874
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Parser_AST.range
                                                in
                                             let p2 =
                                               let uu____7967 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p1, false)]))
                                                 uu____7967
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____8010,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____8012,pats)) ->
                                             let tupn =
                                               let uu____8051 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____8051
                                                 FStar_Syntax_Syntax.delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____8061 =
                                                 let uu____8062 =
                                                   let uu____8077 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn)
                                                      in
                                                   let uu____8080 =
                                                     let uu____8089 =
                                                       let uu____8098 =
                                                         let uu____8105 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____8105
                                                          in
                                                       [uu____8098]  in
                                                     FStar_List.append args
                                                       uu____8089
                                                      in
                                                   (uu____8077, uu____8080)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____8062
                                                  in
                                               mk1 uu____8061  in
                                             let p2 =
                                               let uu____8143 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p1, false)])))
                                                 uu____8143
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | uu____8184 ->
                                             failwith "Impossible")
                                     in
                                  ((x, aq), sc_pat_opt1)
                               in
                            (match uu____7647 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest))
                    in
                 aux env [] FStar_Pervasives_Native.None binders2)
        | FStar_Parser_AST.App
            (uu____8265,uu____8266,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____8288 =
                let uu____8289 = unparen e  in uu____8289.FStar_Parser_AST.tm
                 in
              match uu____8288 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____8299 ->
                  let uu____8300 = desugar_term_aq env e  in
                  (match uu____8300 with
                   | (head1,aq) ->
                       let uu____8313 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____8313, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____8320 ->
            let rec aux args aqs e =
              let uu____8379 =
                let uu____8380 = unparen e  in uu____8380.FStar_Parser_AST.tm
                 in
              match uu____8379 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____8400 = desugar_term_aq env t  in
                  (match uu____8400 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____8436 ->
                  let uu____8437 = desugar_term_aq env e  in
                  (match uu____8437 with
                   | (head1,aq) ->
                       let uu____8460 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____8460, (join_aqs (aq :: aqs))))
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
            let uu____8512 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____8512
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
            let uu____8564 = desugar_term_aq env t  in
            (match uu____8564 with
             | (tm,s) ->
                 let uu____8575 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____8575, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____8581 =
              let uu____8594 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____8594 then desugar_typ_aq else desugar_term_aq  in
            uu____8581 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____8649 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____8792  ->
                        match uu____8792 with
                        | (attr_opt,(p,def)) ->
                            let uu____8850 = is_app_pattern p  in
                            if uu____8850
                            then
                              let uu____8881 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____8881, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____8963 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____8963, def1)
                               | uu____9008 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____9046);
                                           FStar_Parser_AST.prange =
                                             uu____9047;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____9095 =
                                            let uu____9116 =
                                              let uu____9121 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____9121  in
                                            (uu____9116, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____9095, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____9212) ->
                                        if top_level
                                        then
                                          let uu____9247 =
                                            let uu____9268 =
                                              let uu____9273 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____9273  in
                                            (uu____9268, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____9247, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____9363 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____9394 =
                FStar_List.fold_left
                  (fun uu____9467  ->
                     fun uu____9468  ->
                       match (uu____9467, uu____9468) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____9576,uu____9577),uu____9578))
                           ->
                           let uu____9695 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____9721 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____9721 with
                                  | (env2,xx) ->
                                      let uu____9740 =
                                        let uu____9743 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____9743 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx), uu____9740))
                             | FStar_Util.Inr l ->
                                 let uu____9751 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (uu____9751, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____9695 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____9394 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____9899 =
                    match uu____9899 with
                    | (attrs_opt,(uu____9935,args,result_t),def) ->
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
                                let uu____10023 = is_comp_type env1 t  in
                                if uu____10023
                                then
                                  ((let uu____10025 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____10035 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____10035))
                                       in
                                    match uu____10025 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____10038 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____10040 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____10040))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____10038
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t)
                                 in
                              let uu____10045 =
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range
                                 in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed (def, t1, tacopt))
                                uu____10045 FStar_Parser_AST.Expr
                           in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____10049 ->
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
                              let uu____10064 =
                                let uu____10065 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____10065
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____10064
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
                  let uu____10140 = desugar_term_aq env' body  in
                  (match uu____10140 with
                   | (body1,aq) ->
                       let uu____10153 =
                         let uu____10156 =
                           let uu____10157 =
                             let uu____10170 =
                               FStar_Syntax_Subst.close rec_bindings1 body1
                                in
                             ((is_rec, lbs1), uu____10170)  in
                           FStar_Syntax_Syntax.Tm_let uu____10157  in
                         FStar_All.pipe_left mk1 uu____10156  in
                       (uu____10153, aq))
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
              let uu____10248 =
                desugar_binding_pat_maybe_top top_level env pat is_mutable
                 in
              match uu____10248 with
              | (env1,binder,pat1) ->
                  let uu____10270 =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let uu____10296 = desugar_term_aq env1 t2  in
                        (match uu____10296 with
                         | (body1,aq) ->
                             let fv =
                               let uu____10310 =
                                 FStar_Syntax_Util.incr_delta_qualifier t12
                                  in
                               FStar_Syntax_Syntax.lid_as_fv l uu____10310
                                 FStar_Pervasives_Native.None
                                in
                             let uu____10311 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t12,
                                            (t12.FStar_Syntax_Syntax.pos))]),
                                      body1))
                                in
                             (uu____10311, aq))
                    | LocalBinder (x,uu____10341) ->
                        let uu____10342 = desugar_term_aq env1 t2  in
                        (match uu____10342 with
                         | (body1,aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | {
                                   FStar_Syntax_Syntax.v =
                                     FStar_Syntax_Syntax.Pat_wild uu____10356;
                                   FStar_Syntax_Syntax.p = uu____10357;_}::[]
                                   -> body1
                               | uu____10358 ->
                                   let uu____10361 =
                                     let uu____10368 =
                                       let uu____10369 =
                                         let uu____10392 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         let uu____10395 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1
                                            in
                                         (uu____10392, uu____10395)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____10369
                                        in
                                     FStar_Syntax_Syntax.mk uu____10368  in
                                   uu____10361 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range
                                in
                             let uu____10435 =
                               let uu____10438 =
                                 let uu____10439 =
                                   let uu____10452 =
                                     let uu____10455 =
                                       let uu____10456 =
                                         FStar_Syntax_Syntax.mk_binder x  in
                                       [uu____10456]  in
                                     FStar_Syntax_Subst.close uu____10455
                                       body2
                                      in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t12,
                                           (t12.FStar_Syntax_Syntax.pos))]),
                                     uu____10452)
                                    in
                                 FStar_Syntax_Syntax.Tm_let uu____10439  in
                               FStar_All.pipe_left mk1 uu____10438  in
                             (uu____10435, aq))
                     in
                  (match uu____10270 with
                   | (tm,aq) ->
                       if is_mutable
                       then
                         let uu____10513 =
                           FStar_All.pipe_left mk1
                             (FStar_Syntax_Syntax.Tm_meta
                                (tm,
                                  (FStar_Syntax_Syntax.Meta_desugared
                                     FStar_Syntax_Syntax.Mutable_alloc)))
                            in
                         (uu____10513, aq)
                       else (tm, aq))
               in
            let uu____10525 = FStar_List.hd lbs  in
            (match uu____10525 with
             | (attrs,(head_pat,defn)) ->
                 let uu____10569 = is_rec || (is_app_pattern head_pat)  in
                 if uu____10569
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____10582 =
                let uu____10583 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____10583  in
              mk1 uu____10582  in
            let uu____10584 = desugar_term_aq env t1  in
            (match uu____10584 with
             | (t1',aq1) ->
                 let uu____10595 = desugar_term_aq env t2  in
                 (match uu____10595 with
                  | (t2',aq2) ->
                      let uu____10606 = desugar_term_aq env t3  in
                      (match uu____10606 with
                       | (t3',aq3) ->
                           let uu____10617 =
                             let uu____10618 =
                               let uu____10619 =
                                 let uu____10642 =
                                   let uu____10659 =
                                     let uu____10674 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t2.FStar_Parser_AST.range
                                        in
                                     (uu____10674,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____10687 =
                                     let uu____10704 =
                                       let uu____10719 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t3.FStar_Parser_AST.range
                                          in
                                       (uu____10719,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____10704]  in
                                   uu____10659 :: uu____10687  in
                                 (t1', uu____10642)  in
                               FStar_Syntax_Syntax.Tm_match uu____10619  in
                             mk1 uu____10618  in
                           (uu____10617, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____10918 =
              match uu____10918 with
              | (pat,wopt,b) ->
                  let uu____10940 = desugar_match_pat env pat  in
                  (match uu____10940 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____10971 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____10971
                          in
                       let uu____10972 = desugar_term_aq env1 b  in
                       (match uu____10972 with
                        | (b1,aq) ->
                            let uu____10985 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____10985, aq)))
               in
            let uu____10990 = desugar_term_aq env e  in
            (match uu____10990 with
             | (e1,aq) ->
                 let uu____11001 =
                   let uu____11024 =
                     let uu____11049 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____11049 FStar_List.unzip  in
                   FStar_All.pipe_right uu____11024
                     (fun uu____11155  ->
                        match uu____11155 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____11001 with
                  | (brs,aqs) ->
                      let uu____11318 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____11318, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____11363 = is_comp_type env t  in
              if uu____11363
              then
                let uu____11372 = desugar_comp t.FStar_Parser_AST.range env t
                   in
                FStar_Util.Inr uu____11372
              else
                (let uu____11380 = desugar_term env t  in
                 FStar_Util.Inl uu____11380)
               in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)  in
            let uu____11390 = desugar_term_aq env e  in
            (match uu____11390 with
             | (e1,aq) ->
                 let uu____11401 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_ascribed
                        (e1, (annot, tac_opt1), FStar_Pervasives_Native.None))
                    in
                 (uu____11401, aq))
        | FStar_Parser_AST.Record (uu____11434,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____11475 = FStar_List.hd fields  in
              match uu____11475 with | (f,uu____11487) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____11533  ->
                        match uu____11533 with
                        | (g,uu____11539) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____11545,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____11559 =
                         let uu____11564 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____11564)
                          in
                       FStar_Errors.raise_error uu____11559
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
                  let uu____11572 =
                    let uu____11583 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____11614  ->
                              match uu____11614 with
                              | (f,uu____11624) ->
                                  let uu____11625 =
                                    let uu____11626 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____11626
                                     in
                                  (uu____11625, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____11583)  in
                  FStar_Parser_AST.Construct uu____11572
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____11644 =
                      let uu____11645 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____11645  in
                    FStar_Parser_AST.mk_term uu____11644
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____11647 =
                      let uu____11660 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____11690  ->
                                match uu____11690 with
                                | (f,uu____11700) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____11660)  in
                    FStar_Parser_AST.Record uu____11647  in
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
            let uu____11760 = desugar_term_aq env recterm1  in
            (match uu____11760 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____11776;
                         FStar_Syntax_Syntax.vars = uu____11777;_},args)
                      ->
                      let uu____11799 =
                        let uu____11800 =
                          let uu____11801 =
                            let uu____11816 =
                              let uu____11819 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____11820 =
                                let uu____11823 =
                                  let uu____11824 =
                                    let uu____11831 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____11831)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____11824
                                   in
                                FStar_Pervasives_Native.Some uu____11823  in
                              FStar_Syntax_Syntax.fvar uu____11819
                                FStar_Syntax_Syntax.delta_constant
                                uu____11820
                               in
                            (uu____11816, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____11801  in
                        FStar_All.pipe_left mk1 uu____11800  in
                      (uu____11799, s)
                  | uu____11858 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____11862 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____11862 with
              | (constrname,is_rec) ->
                  let uu____11877 = desugar_term_aq env e  in
                  (match uu____11877 with
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
                       let uu____11895 =
                         let uu____11896 =
                           let uu____11897 =
                             let uu____11912 =
                               let uu____11915 =
                                 let uu____11916 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____11916
                                  in
                               FStar_Syntax_Syntax.fvar uu____11915
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1")) qual
                                in
                             let uu____11917 =
                               let uu____11926 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____11926]  in
                             (uu____11912, uu____11917)  in
                           FStar_Syntax_Syntax.Tm_app uu____11897  in
                         FStar_All.pipe_left mk1 uu____11896  in
                       (uu____11895, s))))
        | FStar_Parser_AST.NamedTyp (uu____11955,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____11964 =
              let uu____11965 = FStar_Syntax_Subst.compress tm  in
              uu____11965.FStar_Syntax_Syntax.n  in
            (match uu____11964 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____11973 =
                   let uu___246_11974 =
                     let uu____11975 =
                       let uu____11976 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____11976  in
                     FStar_Syntax_Util.exp_string uu____11975  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___246_11974.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___246_11974.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____11973, noaqs)
             | uu____11977 ->
                 let uu____11978 =
                   let uu____11983 =
                     let uu____11984 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.strcat "VQuote, expected an fvar, got: "
                       uu____11984
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____11983)  in
                 FStar_Errors.raise_error uu____11978
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____11990 = desugar_term_aq env e  in
            (match uu____11990 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____12002 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____12002, noaqs))
        | FStar_Parser_AST.Antiquote (b,e) ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____12008 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____12009 =
              let uu____12010 =
                let uu____12019 = desugar_term env e  in (bv, b, uu____12019)
                 in
              [uu____12010]  in
            (uu____12008, uu____12009)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____12050 =
              let uu____12051 =
                let uu____12052 =
                  let uu____12059 = desugar_term env e  in (uu____12059, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____12052  in
              FStar_All.pipe_left mk1 uu____12051  in
            (uu____12050, noaqs)
        | uu____12064 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____12065 = desugar_formula env top  in
            (uu____12065, noaqs)
        | uu____12066 ->
            let uu____12067 =
              let uu____12072 =
                let uu____12073 = FStar_Parser_AST.term_to_string top  in
                Prims.strcat "Unexpected term: " uu____12073  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____12072)  in
            FStar_Errors.raise_error uu____12067 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____12079 -> false
    | uu____12088 -> true

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
           (fun uu____12125  ->
              match uu____12125 with
              | (a,imp) ->
                  let uu____12138 = desugar_term env a  in
                  arg_withimp_e imp uu____12138))

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
        let is_requires uu____12170 =
          match uu____12170 with
          | (t1,uu____12176) ->
              let uu____12177 =
                let uu____12178 = unparen t1  in
                uu____12178.FStar_Parser_AST.tm  in
              (match uu____12177 with
               | FStar_Parser_AST.Requires uu____12179 -> true
               | uu____12186 -> false)
           in
        let is_ensures uu____12196 =
          match uu____12196 with
          | (t1,uu____12202) ->
              let uu____12203 =
                let uu____12204 = unparen t1  in
                uu____12204.FStar_Parser_AST.tm  in
              (match uu____12203 with
               | FStar_Parser_AST.Ensures uu____12205 -> true
               | uu____12212 -> false)
           in
        let is_app head1 uu____12227 =
          match uu____12227 with
          | (t1,uu____12233) ->
              let uu____12234 =
                let uu____12235 = unparen t1  in
                uu____12235.FStar_Parser_AST.tm  in
              (match uu____12234 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____12237;
                      FStar_Parser_AST.level = uu____12238;_},uu____12239,uu____12240)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____12241 -> false)
           in
        let is_smt_pat uu____12251 =
          match uu____12251 with
          | (t1,uu____12257) ->
              let uu____12258 =
                let uu____12259 = unparen t1  in
                uu____12259.FStar_Parser_AST.tm  in
              (match uu____12258 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____12262);
                             FStar_Parser_AST.range = uu____12263;
                             FStar_Parser_AST.level = uu____12264;_},uu____12265)::uu____12266::[])
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
                             FStar_Parser_AST.range = uu____12305;
                             FStar_Parser_AST.level = uu____12306;_},uu____12307)::uu____12308::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
               | uu____12333 -> false)
           in
        let is_decreases = is_app "decreases"  in
        let pre_process_comp_typ t1 =
          let uu____12365 = head_and_args t1  in
          match uu____12365 with
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
                   let thunk_ens uu____12463 =
                     match uu____12463 with
                     | (e,i) ->
                         let uu____12474 = thunk_ens_ e  in (uu____12474, i)
                      in
                   let fail_lemma uu____12486 =
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
                         let uu____12566 =
                           let uu____12573 =
                             let uu____12580 = thunk_ens ens  in
                             [uu____12580; nil_pat]  in
                           req_true :: uu____12573  in
                         unit_tm :: uu____12566
                     | req::ens::[] when
                         (is_requires req) && (is_ensures ens) ->
                         let uu____12627 =
                           let uu____12634 =
                             let uu____12641 = thunk_ens ens  in
                             [uu____12641; nil_pat]  in
                           req :: uu____12634  in
                         unit_tm :: uu____12627
                     | ens::smtpat::[] when
                         (((let uu____12690 = is_requires ens  in
                            Prims.op_Negation uu____12690) &&
                             (let uu____12692 = is_smt_pat ens  in
                              Prims.op_Negation uu____12692))
                            &&
                            (let uu____12694 = is_decreases ens  in
                             Prims.op_Negation uu____12694))
                           && (is_smt_pat smtpat)
                         ->
                         let uu____12695 =
                           let uu____12702 =
                             let uu____12709 = thunk_ens ens  in
                             [uu____12709; smtpat]  in
                           req_true :: uu____12702  in
                         unit_tm :: uu____12695
                     | ens::dec::[] when
                         (is_ensures ens) && (is_decreases dec) ->
                         let uu____12756 =
                           let uu____12763 =
                             let uu____12770 = thunk_ens ens  in
                             [uu____12770; nil_pat; dec]  in
                           req_true :: uu____12763  in
                         unit_tm :: uu____12756
                     | ens::dec::smtpat::[] when
                         ((is_ensures ens) && (is_decreases dec)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____12830 =
                           let uu____12837 =
                             let uu____12844 = thunk_ens ens  in
                             [uu____12844; smtpat; dec]  in
                           req_true :: uu____12837  in
                         unit_tm :: uu____12830
                     | req::ens::dec::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_decreases dec)
                         ->
                         let uu____12904 =
                           let uu____12911 =
                             let uu____12918 = thunk_ens ens  in
                             [uu____12918; nil_pat; dec]  in
                           req :: uu____12911  in
                         unit_tm :: uu____12904
                     | req::ens::smtpat::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____12978 =
                           let uu____12985 =
                             let uu____12992 = thunk_ens ens  in
                             [uu____12992; smtpat]  in
                           req :: uu____12985  in
                         unit_tm :: uu____12978
                     | req::ens::dec::smtpat::[] when
                         (((is_requires req) && (is_ensures ens)) &&
                            (is_smt_pat smtpat))
                           && (is_decreases dec)
                         ->
                         let uu____13057 =
                           let uu____13064 =
                             let uu____13071 = thunk_ens ens  in
                             [uu____13071; dec; smtpat]  in
                           req :: uu____13064  in
                         unit_tm :: uu____13057
                     | _other -> fail_lemma ()  in
                   let head_and_attributes =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) lemma
                      in
                   (head_and_attributes, args1)
               | FStar_Parser_AST.Name l when
                   FStar_Syntax_DsEnv.is_effect_name env l ->
                   let uu____13133 =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) l
                      in
                   (uu____13133, args)
               | FStar_Parser_AST.Name l when
                   (let uu____13161 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____13161
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   let uu____13162 =
                     let uu____13169 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_Tot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____13169, [])  in
                   (uu____13162, args)
               | FStar_Parser_AST.Name l when
                   (let uu____13187 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____13187
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                   ->
                   let uu____13188 =
                     let uu____13195 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_GTot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____13195, [])  in
                   (uu____13188, args)
               | FStar_Parser_AST.Name l when
                   (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                      ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                     || ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                   ->
                   let uu____13211 =
                     let uu____13218 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_Tot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____13218, [])  in
                   (uu____13211, [(t1, FStar_Parser_AST.Nothing)])
               | uu____13241 ->
                   let default_effect =
                     let uu____13243 = FStar_Options.ml_ish ()  in
                     if uu____13243
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____13246 =
                           FStar_Options.warn_default_effects ()  in
                         if uu____13246
                         then
                           FStar_Errors.log_issue
                             head1.FStar_Parser_AST.range
                             (FStar_Errors.Warning_UseDefaultEffect,
                               "Using default effect Tot")
                         else ());
                        FStar_Parser_Const.effect_Tot_lid)
                      in
                   let uu____13248 =
                     let uu____13255 =
                       FStar_Ident.set_lid_range default_effect
                         head1.FStar_Parser_AST.range
                        in
                     (uu____13255, [])  in
                   (uu____13248, [(t1, FStar_Parser_AST.Nothing)]))
           in
        let uu____13278 = pre_process_comp_typ t  in
        match uu____13278 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____13328 =
                  let uu____13333 =
                    let uu____13334 = FStar_Syntax_Print.lid_to_string eff
                       in
                    FStar_Util.format1 "Not enough args to effect %s"
                      uu____13334
                     in
                  (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____13333)  in
                fail1 uu____13328)
             else ();
             (let is_universe uu____13345 =
                match uu____13345 with
                | (uu____13350,imp) -> imp = FStar_Parser_AST.UnivApp  in
              let uu____13352 = FStar_Util.take is_universe args  in
              match uu____13352 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____13411  ->
                         match uu____13411 with
                         | (u,imp) -> desugar_universe u) universes
                     in
                  let uu____13418 =
                    let uu____13433 = FStar_List.hd args1  in
                    let uu____13442 = FStar_List.tl args1  in
                    (uu____13433, uu____13442)  in
                  (match uu____13418 with
                   | (result_arg,rest) ->
                       let result_typ =
                         desugar_typ env
                           (FStar_Pervasives_Native.fst result_arg)
                          in
                       let rest1 = desugar_args env rest  in
                       let uu____13497 =
                         let is_decrease uu____13535 =
                           match uu____13535 with
                           | (t1,uu____13545) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.pos = uu____13555;
                                       FStar_Syntax_Syntax.vars = uu____13556;_},uu____13557::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.decreases_lid
                                | uu____13588 -> false)
                            in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease)
                          in
                       (match uu____13497 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____13704  ->
                                      match uu____13704 with
                                      | (t1,uu____13714) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____13723,(arg,uu____13725)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____13754 -> failwith "impos")))
                               in
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
                                | uu____13771 -> false  in
                              (((is_empty decreases_clause) &&
                                  (is_empty rest2))
                                 && (is_empty cattributes))
                                && (is_empty universes1)
                               in
                            let uu____13782 =
                              no_additional_args &&
                                (FStar_Ident.lid_equals eff
                                   FStar_Parser_Const.effect_Tot_lid)
                               in
                            if uu____13782
                            then FStar_Syntax_Syntax.mk_Total result_typ
                            else
                              (let uu____13786 =
                                 no_additional_args &&
                                   (FStar_Ident.lid_equals eff
                                      FStar_Parser_Const.effect_GTot_lid)
                                  in
                               if uu____13786
                               then FStar_Syntax_Syntax.mk_GTotal result_typ
                               else
                                 (let flags1 =
                                    let uu____13793 =
                                      FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_Lemma_lid
                                       in
                                    if uu____13793
                                    then [FStar_Syntax_Syntax.LEMMA]
                                    else
                                      (let uu____13797 =
                                         FStar_Ident.lid_equals eff
                                           FStar_Parser_Const.effect_Tot_lid
                                          in
                                       if uu____13797
                                       then [FStar_Syntax_Syntax.TOTAL]
                                       else
                                         (let uu____13801 =
                                            FStar_Ident.lid_equals eff
                                              FStar_Parser_Const.effect_ML_lid
                                             in
                                          if uu____13801
                                          then [FStar_Syntax_Syntax.MLEFFECT]
                                          else
                                            (let uu____13805 =
                                               FStar_Ident.lid_equals eff
                                                 FStar_Parser_Const.effect_GTot_lid
                                                in
                                             if uu____13805
                                             then
                                               [FStar_Syntax_Syntax.SOMETRIVIAL]
                                             else [])))
                                     in
                                  let flags2 =
                                    FStar_List.append flags1 cattributes  in
                                  let rest3 =
                                    let uu____13821 =
                                      FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_Lemma_lid
                                       in
                                    if uu____13821
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
                                                  let uu____13906 =
                                                    FStar_Ident.set_lid_range
                                                      FStar_Parser_Const.pattern_lid
                                                      pat.FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_Syntax.fvar
                                                    uu____13906
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
                                            | uu____13921 -> pat  in
                                          let uu____13922 =
                                            let uu____13933 =
                                              let uu____13944 =
                                                let uu____13953 =
                                                  FStar_Syntax_Syntax.mk
                                                    (FStar_Syntax_Syntax.Tm_meta
                                                       (pat1,
                                                         (FStar_Syntax_Syntax.Meta_desugared
                                                            FStar_Syntax_Syntax.Meta_smt_pat)))
                                                    FStar_Pervasives_Native.None
                                                    pat1.FStar_Syntax_Syntax.pos
                                                   in
                                                (uu____13953, aq)  in
                                              [uu____13944]  in
                                            ens :: uu____13933  in
                                          req :: uu____13922
                                      | uu____13994 -> rest2
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
        | uu____14018 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___247_14039 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___247_14039.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___247_14039.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___248_14081 = b  in
             {
               FStar_Parser_AST.b = (uu___248_14081.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___248_14081.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___248_14081.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____14144 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____14144)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____14157 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____14157 with
             | (env1,a1) ->
                 let a2 =
                   let uu___249_14167 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___249_14167.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___249_14167.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____14193 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____14207 =
                     let uu____14210 =
                       let uu____14211 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____14211]  in
                     no_annot_abs uu____14210 body2  in
                   FStar_All.pipe_left setpos uu____14207  in
                 let uu____14226 =
                   let uu____14227 =
                     let uu____14242 =
                       let uu____14245 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____14245
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____14246 =
                       let uu____14255 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____14255]  in
                     (uu____14242, uu____14246)  in
                   FStar_Syntax_Syntax.Tm_app uu____14227  in
                 FStar_All.pipe_left mk1 uu____14226)
        | uu____14286 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____14366 = q (rest, pats, body)  in
              let uu____14373 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____14366 uu____14373
                FStar_Parser_AST.Formula
               in
            let uu____14374 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____14374 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____14383 -> failwith "impossible"  in
      let uu____14386 =
        let uu____14387 = unparen f  in uu____14387.FStar_Parser_AST.tm  in
      match uu____14386 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____14394,uu____14395) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____14406,uu____14407) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____14438 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____14438
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____14474 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____14474
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____14517 -> desugar_term env f

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
      let uu____14522 =
        FStar_List.fold_left
          (fun uu____14558  ->
             fun b  ->
               match uu____14558 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___250_14610 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___250_14610.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___250_14610.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___250_14610.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____14627 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____14627 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___251_14647 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___251_14647.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___251_14647.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____14664 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____14522 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

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
          let uu____14751 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____14751)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____14756 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____14756)
      | FStar_Parser_AST.TVariable x ->
          let uu____14760 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____14760)
      | FStar_Parser_AST.NoName t ->
          let uu____14764 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____14764)
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
               (fun uu___213_14803  ->
                  match uu___213_14803 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____14804 -> false))
           in
        let quals2 q =
          let uu____14817 =
            (let uu____14820 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____14820) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____14817
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____14834 = FStar_Ident.range_of_lid disc_name  in
                let uu____14835 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____14834;
                  FStar_Syntax_Syntax.sigquals = uu____14835;
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
            let uu____14874 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____14908  ->
                        match uu____14908 with
                        | (x,uu____14916) ->
                            let uu____14917 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____14917 with
                             | (field_name,uu____14925) ->
                                 let only_decl =
                                   ((let uu____14929 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____14929)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____14931 =
                                        let uu____14932 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____14932.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____14931)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____14948 =
                                       FStar_List.filter
                                         (fun uu___214_14952  ->
                                            match uu___214_14952 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____14953 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____14948
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___215_14966  ->
                                             match uu___215_14966 with
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____14967 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____14969 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____14969;
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____14974 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____14974
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          (FStar_Syntax_Syntax.Delta_equational_at_level
                                             (Prims.parse_int "1"))
                                      else
                                        FStar_Syntax_Syntax.Delta_equational_at_level
                                          (Prims.parse_int "1")
                                       in
                                    let lb =
                                      let uu____14979 =
                                        let uu____14984 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____14984  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____14979;
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
                                      let uu____14988 =
                                        let uu____14989 =
                                          let uu____14996 =
                                            let uu____14999 =
                                              let uu____15000 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____15000
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____14999]  in
                                          ((false, [lb]), uu____14996)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____14989
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____14988;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____14874 FStar_List.flatten
  
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
            (lid,uu____15044,t,uu____15046,n1,uu____15048) when
            let uu____15053 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____15053 ->
            let uu____15054 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____15054 with
             | (formals,uu____15070) ->
                 (match formals with
                  | [] -> []
                  | uu____15093 ->
                      let filter_records uu___216_15107 =
                        match uu___216_15107 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____15110,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____15122 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____15124 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____15124 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Syntax_Syntax.Data_ctor
                        | FStar_Pervasives_Native.Some q -> q  in
                      let iquals1 =
                        if
                          FStar_List.contains FStar_Syntax_Syntax.Abstract
                            iquals
                        then FStar_Syntax_Syntax.Private :: iquals
                        else iquals  in
                      let uu____15134 = FStar_Util.first_N n1 formals  in
                      (match uu____15134 with
                       | (uu____15157,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____15183 -> []
  
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
                    let uu____15253 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____15253
                    then
                      let uu____15256 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____15256
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____15259 =
                      let uu____15264 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____15264  in
                    let uu____15265 =
                      let uu____15268 = FStar_Syntax_Syntax.mk_Total k  in
                      FStar_Syntax_Util.arrow typars uu____15268  in
                    let uu____15271 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____15259;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____15265;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____15271;
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
          let tycon_id uu___217_15322 =
            match uu___217_15322 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____15324,uu____15325) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____15335,uu____15336,uu____15337) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____15347,uu____15348,uu____15349) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____15379,uu____15380,uu____15381) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____15425) ->
                let uu____15426 =
                  let uu____15427 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____15427  in
                FStar_Parser_AST.mk_term uu____15426 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____15429 =
                  let uu____15430 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____15430  in
                FStar_Parser_AST.mk_term uu____15429 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____15432) ->
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
              | uu____15463 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____15469 =
                     let uu____15470 =
                       let uu____15477 = binder_to_term b  in
                       (out, uu____15477, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____15470  in
                   FStar_Parser_AST.mk_term uu____15469
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___218_15489 =
            match uu___218_15489 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____15545  ->
                       match uu____15545 with
                       | (x,t,uu____15556) ->
                           let uu____15561 =
                             let uu____15562 =
                               let uu____15567 =
                                 FStar_Syntax_Util.mangle_field_name x  in
                               (uu____15567, t)  in
                             FStar_Parser_AST.Annotated uu____15562  in
                           FStar_Parser_AST.mk_binder uu____15561
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____15569 =
                    let uu____15570 =
                      let uu____15571 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____15571  in
                    FStar_Parser_AST.mk_term uu____15570
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____15569 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let uu____15575 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____15602  ->
                          match uu____15602 with
                          | (x,uu____15612,uu____15613) ->
                              FStar_Syntax_Util.unmangle_field_name x))
                   in
                ((FStar_Parser_AST.TyconVariant
                    (id1, parms, kopt,
                      [(constrName, (FStar_Pervasives_Native.Some constrTyp),
                         FStar_Pervasives_Native.None, false)])),
                  uu____15575)
            | uu____15666 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___219_15705 =
            match uu___219_15705 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____15729 = typars_of_binders _env binders  in
                (match uu____15729 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____15771 =
                         let uu____15772 =
                           let uu____15773 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____15773  in
                         FStar_Parser_AST.mk_term uu____15772
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____15771 binders  in
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
            | uu____15784 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____15832 =
              FStar_List.fold_left
                (fun uu____15872  ->
                   fun uu____15873  ->
                     match (uu____15872, uu____15873) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____15964 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____15964 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____15832 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____16077 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____16077
                | uu____16078 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____16086 = desugar_abstract_tc quals env [] tc  in
              (match uu____16086 with
               | (uu____16099,uu____16100,se,uu____16102) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____16105,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____16122 =
                                 let uu____16123 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____16123  in
                               if uu____16122
                               then
                                 let uu____16124 =
                                   let uu____16129 =
                                     let uu____16130 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____16130
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____16129)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____16124
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
                           | uu____16137 ->
                               let uu____16138 =
                                 let uu____16145 =
                                   let uu____16146 =
                                     let uu____16159 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____16159)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____16146
                                    in
                                 FStar_Syntax_Syntax.mk uu____16145  in
                               uu____16138 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___252_16173 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___252_16173.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___252_16173.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___252_16173.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____16174 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____16177 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____16177
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____16190 = typars_of_binders env binders  in
              (match uu____16190 with
               | (env',typars) ->
                   let k =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____16226 =
                           FStar_Util.for_some
                             (fun uu___220_16228  ->
                                match uu___220_16228 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____16229 -> false) quals
                            in
                         if uu____16226
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Util.ktype
                     | FStar_Pervasives_Native.Some k -> desugar_term env' k
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____16236 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___221_16240  ->
                               match uu___221_16240 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____16241 -> false))
                        in
                     if uu____16236
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____16250 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____16250
                     then
                       let uu____16253 =
                         let uu____16260 =
                           let uu____16261 = unparen t  in
                           uu____16261.FStar_Parser_AST.tm  in
                         match uu____16260 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____16282 =
                               match FStar_List.rev args with
                               | (last_arg,uu____16312)::args_rev ->
                                   let uu____16324 =
                                     let uu____16325 = unparen last_arg  in
                                     uu____16325.FStar_Parser_AST.tm  in
                                   (match uu____16324 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____16353 -> ([], args))
                               | uu____16362 -> ([], args)  in
                             (match uu____16282 with
                              | (cattributes,args1) ->
                                  let uu____16401 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____16401))
                         | uu____16412 -> (t, [])  in
                       match uu____16253 with
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
                                  (fun uu___222_16434  ->
                                     match uu___222_16434 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____16435 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____16442)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____16466 = tycon_record_as_variant trec  in
              (match uu____16466 with
               | (t,fs) ->
                   let uu____16483 =
                     let uu____16486 =
                       let uu____16487 =
                         let uu____16496 =
                           let uu____16499 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____16499  in
                         (uu____16496, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____16487  in
                     uu____16486 :: quals  in
                   desugar_tycon env d uu____16483 [t])
          | uu____16504::uu____16505 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____16672 = et  in
                match uu____16672 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____16897 ->
                         let trec = tc  in
                         let uu____16921 = tycon_record_as_variant trec  in
                         (match uu____16921 with
                          | (t,fs) ->
                              let uu____16980 =
                                let uu____16983 =
                                  let uu____16984 =
                                    let uu____16993 =
                                      let uu____16996 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____16996  in
                                    (uu____16993, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____16984
                                   in
                                uu____16983 :: quals1  in
                              collect_tcs uu____16980 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____17083 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____17083 with
                          | (env2,uu____17143,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____17292 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____17292 with
                          | (env2,uu____17352,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____17477 ->
                         failwith "Unrecognized mutual type definition")
                 in
              let uu____17524 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____17524 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___224_18035  ->
                             match uu___224_18035 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____18102,uu____18103);
                                    FStar_Syntax_Syntax.sigrng = uu____18104;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____18105;
                                    FStar_Syntax_Syntax.sigmeta = uu____18106;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____18107;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____18168 =
                                     typars_of_binders env1 binders  in
                                   match uu____18168 with
                                   | (env2,tpars1) ->
                                       let uu____18199 =
                                         push_tparams env2 tpars1  in
                                       (match uu____18199 with
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
                                 let uu____18232 =
                                   let uu____18253 =
                                     mk_typ_abbrev id1 uvs tpars k t1 
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____18253)
                                    in
                                 [uu____18232]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____18321);
                                    FStar_Syntax_Syntax.sigrng = uu____18322;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____18324;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____18325;_},constrs,tconstr,quals1)
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
                                 let uu____18423 = push_tparams env1 tpars
                                    in
                                 (match uu____18423 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____18500  ->
                                             match uu____18500 with
                                             | (x,uu____18514) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____18522 =
                                        let uu____18551 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____18665  ->
                                                  match uu____18665 with
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
                                                        let uu____18721 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____18721
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
                                                                uu___223_18732
                                                                 ->
                                                                match uu___223_18732
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____18744
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____18752 =
                                                        let uu____18773 =
                                                          let uu____18774 =
                                                            let uu____18775 =
                                                              let uu____18790
                                                                =
                                                                let uu____18791
                                                                  =
                                                                  let uu____18794
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____18794
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____18791
                                                                 in
                                                              (name, univs1,
                                                                uu____18790,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____18775
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____18774;
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
                                                          uu____18773)
                                                         in
                                                      (name, uu____18752)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____18551
                                         in
                                      (match uu____18522 with
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
                             | uu____19031 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____19163  ->
                             match uu____19163 with
                             | (name_doc,uu____19191,uu____19192) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____19272  ->
                             match uu____19272 with
                             | (uu____19293,uu____19294,se) -> se))
                      in
                   let uu____19324 =
                     let uu____19331 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____19331 rng
                      in
                   (match uu____19324 with
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
                               (fun uu____19397  ->
                                  match uu____19397 with
                                  | (uu____19420,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____19471,tps,k,uu____19474,constrs)
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
                                  | uu____19493 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____19510  ->
                                 match uu____19510 with
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
      let uu____19553 =
        FStar_List.fold_left
          (fun uu____19588  ->
             fun b  ->
               match uu____19588 with
               | (env1,binders1) ->
                   let uu____19632 = desugar_binder env1 b  in
                   (match uu____19632 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____19655 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____19655 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____19710 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____19553 with
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
          let uu____19811 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___225_19816  ->
                    match uu___225_19816 with
                    | FStar_Syntax_Syntax.Reflectable uu____19817 -> true
                    | uu____19818 -> false))
             in
          if uu____19811
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____19821 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____19821
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
      let uu____19853 = FStar_Syntax_Util.head_and_args at1  in
      match uu____19853 with
      | (hd1,args) ->
          let uu____19898 =
            let uu____19911 =
              let uu____19912 = FStar_Syntax_Subst.compress hd1  in
              uu____19912.FStar_Syntax_Syntax.n  in
            (uu____19911, args)  in
          (match uu____19898 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(a1,uu____19933)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr
               ->
               let uu____19958 =
                 let uu____19963 =
                   FStar_Syntax_Embeddings.e_list
                     FStar_Syntax_Embeddings.e_int
                    in
                 FStar_Syntax_Embeddings.unembed uu____19963 a1  in
               (match uu____19958 with
                | FStar_Pervasives_Native.Some [] ->
                    FStar_Errors.raise_error
                      (FStar_Errors.Error_EmptyFailErrs,
                        "Found ill-applied fail, argument should be a non-empty list of integers")
                      at1.FStar_Syntax_Syntax.pos
                | FStar_Pervasives_Native.Some es ->
                    let uu____19993 =
                      let uu____20000 =
                        FStar_List.map FStar_BigInt.to_int_fs es  in
                      (uu____20000, false)  in
                    FStar_Pervasives_Native.Some uu____19993
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
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____20045) when
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
           | uu____20093 -> FStar_Pervasives_Native.None)
  
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
                  let uu____20248 = desugar_binders monad_env eff_binders  in
                  match uu____20248 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let for_free =
                        let uu____20287 =
                          let uu____20289 =
                            let uu____20296 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____20296  in
                          FStar_List.length uu____20289  in
                        uu____20287 = (Prims.parse_int "1")  in
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
                            (uu____20337,(FStar_Parser_AST.TyconAbbrev
                                          (name,uu____20339,uu____20340,uu____20341),uu____20342)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____20375 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____20376 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____20388 = name_of_eff_decl decl  in
                             FStar_List.mem uu____20388 mandatory_members)
                          eff_decls
                         in
                      (match uu____20376 with
                       | (mandatory_members_decls,actions) ->
                           let uu____20405 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____20434  ->
                                     fun decl  ->
                                       match uu____20434 with
                                       | (env2,out) ->
                                           let uu____20454 =
                                             desugar_decl env2 decl  in
                                           (match uu____20454 with
                                            | (env3,ses) ->
                                                let uu____20467 =
                                                  let uu____20470 =
                                                    FStar_List.hd ses  in
                                                  uu____20470 :: out  in
                                                (env3, uu____20467)))
                                  (env1, []))
                              in
                           (match uu____20405 with
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
                                              (uu____20538,(FStar_Parser_AST.TyconAbbrev
                                                            (name,action_params,uu____20541,
                                                             {
                                                               FStar_Parser_AST.tm
                                                                 =
                                                                 FStar_Parser_AST.Construct
                                                                 (uu____20542,
                                                                  (def,uu____20544)::
                                                                  (cps_type,uu____20546)::[]);
                                                               FStar_Parser_AST.range
                                                                 =
                                                                 uu____20547;
                                                               FStar_Parser_AST.level
                                                                 =
                                                                 uu____20548;_}),doc1)::[])
                                              when Prims.op_Negation for_free
                                              ->
                                              let uu____20600 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____20600 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____20638 =
                                                     let uu____20639 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____20640 =
                                                       let uu____20641 =
                                                         desugar_term env3
                                                           def
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____20641
                                                        in
                                                     let uu____20646 =
                                                       let uu____20647 =
                                                         desugar_typ env3
                                                           cps_type
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____20647
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____20639;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____20640;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____20646
                                                     }  in
                                                   (uu____20638, doc1))
                                          | FStar_Parser_AST.Tycon
                                              (uu____20654,(FStar_Parser_AST.TyconAbbrev
                                                            (name,action_params,uu____20657,defn),doc1)::[])
                                              when for_free ->
                                              let uu____20692 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____20692 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____20730 =
                                                     let uu____20731 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____20732 =
                                                       let uu____20733 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____20733
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____20731;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____20732;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____20730, doc1))
                                          | uu____20740 ->
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
                                    let uu____20772 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____20772
                                     in
                                  let uu____20773 =
                                    let uu____20774 =
                                      FStar_Syntax_DsEnv.fail_or env2
                                        (FStar_Syntax_DsEnv.try_lookup_definition
                                           env2) l
                                       in
                                    FStar_All.pipe_left
                                      (FStar_Syntax_Subst.close binders1)
                                      uu____20774
                                     in
                                  ([], uu____20773)  in
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
                                      let uu____20791 =
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      ([], uu____20791)  in
                                    let uu____20798 =
                                      let uu____20799 =
                                        let uu____20800 =
                                          let uu____20801 = lookup1 "repr"
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____20801
                                           in
                                        let uu____20810 = lookup1 "return"
                                           in
                                        let uu____20811 = lookup1 "bind"  in
                                        let uu____20812 =
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
                                            uu____20800;
                                          FStar_Syntax_Syntax.return_repr =
                                            uu____20810;
                                          FStar_Syntax_Syntax.bind_repr =
                                            uu____20811;
                                          FStar_Syntax_Syntax.actions =
                                            actions1;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            uu____20812
                                        }  in
                                      FStar_Syntax_Syntax.Sig_new_effect_for_free
                                        uu____20799
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____20798;
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
                                         (fun uu___226_20818  ->
                                            match uu___226_20818 with
                                            | FStar_Syntax_Syntax.Reifiable 
                                                -> true
                                            | FStar_Syntax_Syntax.Reflectable
                                                uu____20819 -> true
                                            | uu____20820 -> false)
                                         qualifiers
                                        in
                                     let un_ts =
                                       ([], FStar_Syntax_Syntax.tun)  in
                                     let uu____20834 =
                                       let uu____20835 =
                                         let uu____20836 =
                                           lookup1 "return_wp"  in
                                         let uu____20837 = lookup1 "bind_wp"
                                            in
                                         let uu____20838 =
                                           lookup1 "if_then_else"  in
                                         let uu____20839 = lookup1 "ite_wp"
                                            in
                                         let uu____20840 = lookup1 "stronger"
                                            in
                                         let uu____20841 = lookup1 "close_wp"
                                            in
                                         let uu____20842 = lookup1 "assert_p"
                                            in
                                         let uu____20843 = lookup1 "assume_p"
                                            in
                                         let uu____20844 = lookup1 "null_wp"
                                            in
                                         let uu____20845 = lookup1 "trivial"
                                            in
                                         let uu____20846 =
                                           if rr
                                           then
                                             let uu____20847 = lookup1 "repr"
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.snd
                                               uu____20847
                                           else FStar_Syntax_Syntax.tun  in
                                         let uu____20863 =
                                           if rr
                                           then lookup1 "return"
                                           else un_ts  in
                                         let uu____20865 =
                                           if rr
                                           then lookup1 "bind"
                                           else un_ts  in
                                         let uu____20867 =
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
                                             uu____20836;
                                           FStar_Syntax_Syntax.bind_wp =
                                             uu____20837;
                                           FStar_Syntax_Syntax.if_then_else =
                                             uu____20838;
                                           FStar_Syntax_Syntax.ite_wp =
                                             uu____20839;
                                           FStar_Syntax_Syntax.stronger =
                                             uu____20840;
                                           FStar_Syntax_Syntax.close_wp =
                                             uu____20841;
                                           FStar_Syntax_Syntax.assert_p =
                                             uu____20842;
                                           FStar_Syntax_Syntax.assume_p =
                                             uu____20843;
                                           FStar_Syntax_Syntax.null_wp =
                                             uu____20844;
                                           FStar_Syntax_Syntax.trivial =
                                             uu____20845;
                                           FStar_Syntax_Syntax.repr =
                                             uu____20846;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____20863;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____20865;
                                           FStar_Syntax_Syntax.actions =
                                             actions1;
                                           FStar_Syntax_Syntax.eff_attrs =
                                             uu____20867
                                         }  in
                                       FStar_Syntax_Syntax.Sig_new_effect
                                         uu____20835
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         uu____20834;
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
                                          fun uu____20893  ->
                                            match uu____20893 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____20907 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____20907
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
                let uu____20931 = desugar_binders env1 eff_binders  in
                match uu____20931 with
                | (env2,binders) ->
                    let uu____20968 =
                      let uu____20987 = head_and_args defn  in
                      match uu____20987 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____21032 ->
                                let uu____21033 =
                                  let uu____21038 =
                                    let uu____21039 =
                                      let uu____21040 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.strcat uu____21040 " not found"
                                       in
                                    Prims.strcat "Effect " uu____21039  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____21038)
                                   in
                                FStar_Errors.raise_error uu____21033
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____21042 =
                            match FStar_List.rev args with
                            | (last_arg,uu____21072)::args_rev ->
                                let uu____21084 =
                                  let uu____21085 = unparen last_arg  in
                                  uu____21085.FStar_Parser_AST.tm  in
                                (match uu____21084 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____21113 -> ([], args))
                            | uu____21122 -> ([], args)  in
                          (match uu____21042 with
                           | (cattributes,args1) ->
                               let uu____21173 = desugar_args env2 args1  in
                               let uu____21182 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____21173, uu____21182))
                       in
                    (match uu____20968 with
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
                          (let uu____21238 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____21238 with
                           | (ed_binders,uu____21252,ed_binders_opening) ->
                               let sub1 uu____21265 =
                                 match uu____21265 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____21279 =
                                         FStar_Syntax_Subst.shift_subst
                                           (FStar_List.length us)
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____21279 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____21283 =
                                       let uu____21284 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____21284)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____21283
                                  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____21293 =
                                   let uu____21294 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____21294
                                    in
                                 let uu____21309 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____21310 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____21311 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____21312 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____21313 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____21314 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____21315 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____21316 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____21317 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____21318 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____21319 =
                                   let uu____21320 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____21320
                                    in
                                 let uu____21335 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____21336 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____21337 =
                                   FStar_List.map
                                     (fun action  ->
                                        let uu____21345 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____21346 =
                                          let uu____21347 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____21347
                                           in
                                        let uu____21362 =
                                          let uu____21363 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____21363
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____21345;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____21346;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____21362
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
                                     uu____21293;
                                   FStar_Syntax_Syntax.ret_wp = uu____21309;
                                   FStar_Syntax_Syntax.bind_wp = uu____21310;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____21311;
                                   FStar_Syntax_Syntax.ite_wp = uu____21312;
                                   FStar_Syntax_Syntax.stronger = uu____21313;
                                   FStar_Syntax_Syntax.close_wp = uu____21314;
                                   FStar_Syntax_Syntax.assert_p = uu____21315;
                                   FStar_Syntax_Syntax.assume_p = uu____21316;
                                   FStar_Syntax_Syntax.null_wp = uu____21317;
                                   FStar_Syntax_Syntax.trivial = uu____21318;
                                   FStar_Syntax_Syntax.repr = uu____21319;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____21335;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____21336;
                                   FStar_Syntax_Syntax.actions = uu____21337;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____21380 =
                                     let uu____21382 =
                                       let uu____21389 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____21389
                                        in
                                     FStar_List.length uu____21382  in
                                   uu____21380 = (Prims.parse_int "1")  in
                                 let uu____21415 =
                                   let uu____21418 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____21418 quals  in
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
                                   FStar_Syntax_Syntax.sigquals = uu____21415;
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
                                             let uu____21440 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____21440
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____21442 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____21442
                                 then
                                   let reflect_lid =
                                     let uu____21446 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____21446
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
    let uu____21456 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____21456 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.strcat "  " (Prims.strcat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____21507 ->
              let uu____21508 =
                let uu____21509 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____21509
                 in
              Prims.strcat "\n  " uu____21508
          | uu____21510 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____21523  ->
               match uu____21523 with
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
          let uu____21541 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____21541
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____21543 =
          let uu____21552 = FStar_Syntax_Syntax.as_arg arg  in [uu____21552]
           in
        FStar_Syntax_Util.mk_app fv uu____21543

and (desugar_decl :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      let uu____21577 = desugar_decl_noattrs env d  in
      match uu____21577 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____21595 = mk_comment_attr d  in uu____21595 :: attrs1  in
          let uu____21596 =
            FStar_List.mapi
              (fun i  ->
                 fun sigelt  ->
                   if i = (Prims.parse_int "0")
                   then
                     let uu___253_21602 = sigelt  in
                     {
                       FStar_Syntax_Syntax.sigel =
                         (uu___253_21602.FStar_Syntax_Syntax.sigel);
                       FStar_Syntax_Syntax.sigrng =
                         (uu___253_21602.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___253_21602.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___253_21602.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs = attrs2
                     }
                   else
                     (let uu___254_21604 = sigelt  in
                      let uu____21605 =
                        FStar_List.filter
                          (fun at1  ->
                             let uu____21611 = get_fail_attr false at1  in
                             FStar_Option.isNone uu____21611) attrs2
                         in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___254_21604.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___254_21604.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___254_21604.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___254_21604.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs = uu____21605
                      })) sigelts
             in
          (env1, uu____21596)

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
      | FStar_Parser_AST.Fsdoc uu____21651 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____21659 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____21659, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals  in
          let tcs1 =
            FStar_List.map
              (fun uu____21696  ->
                 match uu____21696 with | (x,uu____21704) -> x) tcs
             in
          let uu____21709 =
            FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals
             in
          desugar_tycon env d uu____21709 tcs1
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals  in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____21731;
                    FStar_Parser_AST.prange = uu____21732;_},uu____21733)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____21742;
                    FStar_Parser_AST.prange = uu____21743;_},uu____21744)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____21759;
                         FStar_Parser_AST.prange = uu____21760;_},uu____21761);
                    FStar_Parser_AST.prange = uu____21762;_},uu____21763)::[]
                   -> false
               | (p,uu____21791)::[] ->
                   let uu____21800 = is_app_pattern p  in
                   Prims.op_Negation uu____21800
               | uu____21801 -> false)
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
            let uu____21874 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____21874 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____21886 =
                     let uu____21887 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____21887.FStar_Syntax_Syntax.n  in
                   match uu____21886 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____21897) ->
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
                         | uu____21930::uu____21931 ->
                             FStar_List.map
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____21934 ->
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.collect
                                  (fun uu___227_21949  ->
                                     match uu___227_21949 with
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inl uu____21952;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____21953;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____21954;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____21955;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____21956;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____21957;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____21958;_}
                                         -> []
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____21970;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____21971;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____21972;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____21973;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____21974;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____21975;_}
                                         ->
                                         FStar_Syntax_DsEnv.lookup_letbinding_quals
                                           env
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                          in
                       let quals2 =
                         let uu____21989 =
                           FStar_All.pipe_right lets1
                             (FStar_Util.for_some
                                (fun uu____22020  ->
                                   match uu____22020 with
                                   | (uu____22033,(uu____22034,t)) ->
                                       t.FStar_Parser_AST.level =
                                         FStar_Parser_AST.Formula))
                            in
                         if uu____21989
                         then FStar_Syntax_Syntax.Logic :: quals1
                         else quals1  in
                       let lbs1 =
                         let uu____22052 =
                           FStar_All.pipe_right quals2
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract)
                            in
                         if uu____22052
                         then
                           let uu____22055 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu___255_22069 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___256_22071 = fv  in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___256_22071.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___256_22071.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___255_22069.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___255_22069.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___255_22069.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___255_22069.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___255_22069.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___255_22069.FStar_Syntax_Syntax.lbpos)
                                     }))
                              in
                           ((FStar_Pervasives_Native.fst lbs), uu____22055)
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
                   | uu____22098 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____22104 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____22123 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____22104 with
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
                       let uu___257_22159 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___257_22159.FStar_Parser_AST.prange)
                       }
                   | uu____22166 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___258_22173 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___258_22173.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___258_22173.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___258_22173.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____22209 id1 =
                   match uu____22209 with
                   | (env1,ses) ->
                       let main =
                         let uu____22230 =
                           let uu____22231 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____22231  in
                         FStar_Parser_AST.mk_term uu____22230
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
                       let uu____22281 = desugar_decl env1 id_decl  in
                       (match uu____22281 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____22299 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____22299 FStar_Util.set_elements
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
            let uu____22324 = close_fun env t  in
            desugar_term env uu____22324  in
          let quals1 =
            let uu____22328 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____22328
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let se =
            let uu____22334 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____22334;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in
          let env2 =
            FStar_Syntax_DsEnv.push_doc env1 lid d.FStar_Parser_AST.doc  in
          (env2, [se])
      | FStar_Parser_AST.Exception (id1,FStar_Pervasives_Native.None ) ->
          let uu____22342 =
            FStar_Syntax_DsEnv.fail_or env
              (FStar_Syntax_DsEnv.try_lookup_lid env)
              FStar_Parser_Const.exn_lid
             in
          (match uu____22342 with
           | (t,uu____22356) ->
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
            let uu____22386 =
              let uu____22393 = FStar_Syntax_Syntax.null_binder t  in
              [uu____22393]  in
            let uu____22406 =
              let uu____22409 =
                let uu____22410 =
                  FStar_Syntax_DsEnv.fail_or env
                    (FStar_Syntax_DsEnv.try_lookup_lid env)
                    FStar_Parser_Const.exn_lid
                   in
                FStar_Pervasives_Native.fst uu____22410  in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____22409
               in
            FStar_Syntax_Util.arrow uu____22386 uu____22406  in
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
            let uu____22471 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____22471 with
            | FStar_Pervasives_Native.None  ->
                let uu____22474 =
                  let uu____22479 =
                    let uu____22480 =
                      let uu____22481 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.strcat uu____22481 " not found"  in
                    Prims.strcat "Effect name " uu____22480  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____22479)  in
                FStar_Errors.raise_error uu____22474
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____22485 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____22527 =
                  let uu____22536 =
                    let uu____22543 = desugar_term env t  in
                    ([], uu____22543)  in
                  FStar_Pervasives_Native.Some uu____22536  in
                (uu____22527, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____22576 =
                  let uu____22585 =
                    let uu____22592 = desugar_term env wp  in
                    ([], uu____22592)  in
                  FStar_Pervasives_Native.Some uu____22585  in
                let uu____22601 =
                  let uu____22610 =
                    let uu____22617 = desugar_term env t  in
                    ([], uu____22617)  in
                  FStar_Pervasives_Native.Some uu____22610  in
                (uu____22576, uu____22601)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____22643 =
                  let uu____22652 =
                    let uu____22659 = desugar_term env t  in
                    ([], uu____22659)  in
                  FStar_Pervasives_Native.Some uu____22652  in
                (FStar_Pervasives_Native.None, uu____22643)
             in
          (match uu____22485 with
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
            let uu____22737 =
              let uu____22738 =
                let uu____22745 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____22745, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____22738  in
            {
              FStar_Syntax_Syntax.sigel = uu____22737;
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
      let uu____22771 =
        FStar_List.fold_left
          (fun uu____22791  ->
             fun d  ->
               match uu____22791 with
               | (env1,sigelts) ->
                   let uu____22811 = desugar_decl env1 d  in
                   (match uu____22811 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____22771 with
      | (env1,sigelts) ->
          let rec forward acc uu___229_22856 =
            match uu___229_22856 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____22870,FStar_Syntax_Syntax.Sig_let uu____22871) ->
                     let uu____22884 =
                       let uu____22887 =
                         let uu___259_22888 = se2  in
                         let uu____22889 =
                           let uu____22892 =
                             FStar_List.filter
                               (fun uu___228_22906  ->
                                  match uu___228_22906 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____22910;
                                           FStar_Syntax_Syntax.vars =
                                             uu____22911;_},uu____22912);
                                      FStar_Syntax_Syntax.pos = uu____22913;
                                      FStar_Syntax_Syntax.vars = uu____22914;_}
                                      when
                                      let uu____22937 =
                                        let uu____22938 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____22938
                                         in
                                      uu____22937 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____22939 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____22892
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___259_22888.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___259_22888.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___259_22888.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___259_22888.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____22889
                         }  in
                       uu____22887 :: se1 :: acc  in
                     forward uu____22884 sigelts1
                 | uu____22944 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____22952 = forward [] sigelts  in (env1, uu____22952)
  
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
      let uu____22994 =
        let uu____23007 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____23024  ->
               match uu____23024 with
               | ({ FStar_Syntax_Syntax.ppname = uu____23033;
                    FStar_Syntax_Syntax.index = uu____23034;
                    FStar_Syntax_Syntax.sort = t;_},uu____23036)
                   ->
                   let uu____23039 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____23039) uu____23007
         in
      FStar_All.pipe_right bs uu____22994  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____23053 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____23070 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____23096 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____23117,uu____23118,bs,t,uu____23121,uu____23122)
                            ->
                            let uu____23131 = bs_univnames bs  in
                            let uu____23134 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____23131 uu____23134
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____23137,uu____23138,t,uu____23140,uu____23141,uu____23142)
                            -> FStar_Syntax_Free.univnames t
                        | uu____23147 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____23096 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___260_23155 = s  in
        let uu____23156 =
          let uu____23157 =
            let uu____23166 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____23184,bs,t,lids1,lids2) ->
                          let uu___261_23197 = se  in
                          let uu____23198 =
                            let uu____23199 =
                              let uu____23216 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____23217 =
                                let uu____23218 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____23218 t  in
                              (lid, uvs, uu____23216, uu____23217, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____23199
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____23198;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___261_23197.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___261_23197.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___261_23197.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___261_23197.FStar_Syntax_Syntax.sigattrs)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____23230,t,tlid,n1,lids1) ->
                          let uu___262_23239 = se  in
                          let uu____23240 =
                            let uu____23241 =
                              let uu____23256 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____23256, tlid, n1, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____23241  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____23240;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___262_23239.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___262_23239.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___262_23239.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___262_23239.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____23259 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____23166, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____23157  in
        {
          FStar_Syntax_Syntax.sigel = uu____23156;
          FStar_Syntax_Syntax.sigrng =
            (uu___260_23155.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___260_23155.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___260_23155.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___260_23155.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____23265,t) ->
        let uvs =
          let uu____23268 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____23268 FStar_Util.set_elements  in
        let uu___263_23273 = s  in
        let uu____23274 =
          let uu____23275 =
            let uu____23282 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____23282)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____23275  in
        {
          FStar_Syntax_Syntax.sigel = uu____23274;
          FStar_Syntax_Syntax.sigrng =
            (uu___263_23273.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___263_23273.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___263_23273.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___263_23273.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____23304 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____23307 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____23314) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____23343,(FStar_Util.Inl t,uu____23345),uu____23346)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____23393,(FStar_Util.Inr c,uu____23395),uu____23396)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____23443 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____23444,(FStar_Util.Inl t,uu____23446),uu____23447) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____23494,(FStar_Util.Inr c,uu____23496),uu____23497) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____23544 -> empty_set  in
          FStar_Util.set_union uu____23304 uu____23307  in
        let all_lb_univs =
          let uu____23548 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____23564 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____23564) empty_set)
             in
          FStar_All.pipe_right uu____23548 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___264_23574 = s  in
        let uu____23575 =
          let uu____23576 =
            let uu____23583 =
              let uu____23584 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___265_23596 = lb  in
                        let uu____23597 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____23600 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___265_23596.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____23597;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___265_23596.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____23600;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___265_23596.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___265_23596.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____23584)  in
            (uu____23583, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____23576  in
        {
          FStar_Syntax_Syntax.sigel = uu____23575;
          FStar_Syntax_Syntax.sigrng =
            (uu___264_23574.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___264_23574.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___264_23574.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___264_23574.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____23608,fml) ->
        let uvs =
          let uu____23611 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____23611 FStar_Util.set_elements  in
        let uu___266_23616 = s  in
        let uu____23617 =
          let uu____23618 =
            let uu____23625 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____23625)  in
          FStar_Syntax_Syntax.Sig_assume uu____23618  in
        {
          FStar_Syntax_Syntax.sigel = uu____23617;
          FStar_Syntax_Syntax.sigrng =
            (uu___266_23616.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___266_23616.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___266_23616.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___266_23616.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____23627,bs,c,flags1) ->
        let uvs =
          let uu____23636 =
            let uu____23639 = bs_univnames bs  in
            let uu____23642 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____23639 uu____23642  in
          FStar_All.pipe_right uu____23636 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___267_23650 = s  in
        let uu____23651 =
          let uu____23652 =
            let uu____23665 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____23666 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____23665, uu____23666, flags1)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____23652  in
        {
          FStar_Syntax_Syntax.sigel = uu____23651;
          FStar_Syntax_Syntax.sigrng =
            (uu___267_23650.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___267_23650.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___267_23650.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___267_23650.FStar_Syntax_Syntax.sigattrs)
        }
    | uu____23669 -> s
  
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
          | (FStar_Pervasives_Native.None ,uu____23704) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____23708;
               FStar_Syntax_Syntax.exports = uu____23709;
               FStar_Syntax_Syntax.is_interface = uu____23710;_},FStar_Parser_AST.Module
             (current_lid,uu____23712)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____23720) ->
              let uu____23723 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____23723
           in
        let uu____23728 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____23764 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____23764, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____23781 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____23781, mname, decls, false)
           in
        match uu____23728 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____23811 = desugar_decls env2 decls  in
            (match uu____23811 with
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
          let uu____23876 =
            (FStar_Options.interactive ()) &&
              (let uu____23878 =
                 let uu____23879 =
                   let uu____23880 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____23880  in
                 FStar_Util.get_file_extension uu____23879  in
               FStar_List.mem uu____23878 ["fsti"; "fsi"])
             in
          if uu____23876 then as_interface m else m  in
        let uu____23884 = desugar_modul_common curmod env m1  in
        match uu____23884 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____23902 = FStar_Syntax_DsEnv.pop ()  in
              (uu____23902, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul ->
      (env_t,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun m  ->
      let uu____23922 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____23922 with
      | (env1,modul,pop_when_done) ->
          let uu____23936 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____23936 with
           | (env2,modul1) ->
               ((let uu____23948 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____23948
                 then
                   let uu____23949 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____23949
                 else ());
                (let uu____23951 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____23951, modul1))))
  
let (ast_modul_to_modul :
  FStar_Parser_AST.modul ->
    FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun env  ->
      let uu____23969 = desugar_modul env modul  in
      match uu____23969 with | (env1,modul1) -> (modul1, env1)
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      let uu____24000 = desugar_decls env decls  in
      match uu____24000 with | (env1,sigelts) -> (sigelts, env1)
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        let uu____24042 = desugar_partial_modul modul env a_modul  in
        match uu____24042 with | (env1,modul1) -> (modul1, env1)
  
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
              | uu____24128 ->
                  let t =
                    let uu____24136 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____24136  in
                  let uu____24147 =
                    let uu____24148 = FStar_Syntax_Subst.compress t  in
                    uu____24148.FStar_Syntax_Syntax.n  in
                  (match uu____24147 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____24158,uu____24159)
                       -> bs1
                   | uu____24180 -> failwith "Impossible")
               in
            let uu____24187 =
              let uu____24194 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____24194
                FStar_Syntax_Syntax.t_unit
               in
            match uu____24187 with
            | (binders,uu____24196,binders_opening) ->
                let erase_term t =
                  let uu____24204 =
                    let uu____24205 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____24205  in
                  FStar_Syntax_Subst.close binders uu____24204  in
                let erase_tscheme uu____24223 =
                  match uu____24223 with
                  | (us,t) ->
                      let t1 =
                        let uu____24243 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____24243 t  in
                      let uu____24246 =
                        let uu____24247 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____24247  in
                      ([], uu____24246)
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
                    | uu____24266 ->
                        let bs =
                          let uu____24274 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____24274  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____24306 =
                          let uu____24307 =
                            let uu____24310 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____24310  in
                          uu____24307.FStar_Syntax_Syntax.n  in
                        (match uu____24306 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____24312,uu____24313) -> bs1
                         | uu____24334 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____24341 =
                      let uu____24342 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____24342  in
                    FStar_Syntax_Subst.close binders uu____24341  in
                  let uu___268_24343 = action  in
                  let uu____24344 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____24345 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___268_24343.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___268_24343.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____24344;
                    FStar_Syntax_Syntax.action_typ = uu____24345
                  }  in
                let uu___269_24346 = ed  in
                let uu____24347 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____24348 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____24349 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____24350 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____24351 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____24352 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____24353 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____24354 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____24355 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____24356 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____24357 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____24358 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____24359 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____24360 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____24361 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____24362 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___269_24346.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___269_24346.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____24347;
                  FStar_Syntax_Syntax.signature = uu____24348;
                  FStar_Syntax_Syntax.ret_wp = uu____24349;
                  FStar_Syntax_Syntax.bind_wp = uu____24350;
                  FStar_Syntax_Syntax.if_then_else = uu____24351;
                  FStar_Syntax_Syntax.ite_wp = uu____24352;
                  FStar_Syntax_Syntax.stronger = uu____24353;
                  FStar_Syntax_Syntax.close_wp = uu____24354;
                  FStar_Syntax_Syntax.assert_p = uu____24355;
                  FStar_Syntax_Syntax.assume_p = uu____24356;
                  FStar_Syntax_Syntax.null_wp = uu____24357;
                  FStar_Syntax_Syntax.trivial = uu____24358;
                  FStar_Syntax_Syntax.repr = uu____24359;
                  FStar_Syntax_Syntax.return_repr = uu____24360;
                  FStar_Syntax_Syntax.bind_repr = uu____24361;
                  FStar_Syntax_Syntax.actions = uu____24362;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___269_24346.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___270_24378 = se  in
                  let uu____24379 =
                    let uu____24380 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____24380  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____24379;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___270_24378.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___270_24378.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___270_24378.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___270_24378.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___271_24384 = se  in
                  let uu____24385 =
                    let uu____24386 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____24386
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____24385;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___271_24384.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___271_24384.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___271_24384.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___271_24384.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____24388 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____24389 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____24389 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____24401 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____24401
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____24403 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____24403)
  