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
                   let uu____1055 =
                     let uu____1056 =
                       let uu____1061 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____1061)  in
                     FStar_Parser_AST.TAnnotated uu____1056  in
                   FStar_Parser_AST.mk_binder uu____1055
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
        let uu____1078 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1078  in
      if (FStar_List.length ftv) = (Prims.parse_int "0")
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1096 =
                     let uu____1097 =
                       let uu____1102 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____1102)  in
                     FStar_Parser_AST.TAnnotated uu____1097  in
                   FStar_Parser_AST.mk_binder uu____1096
                     x.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____1104 =
             let uu____1105 = unparen t  in uu____1105.FStar_Parser_AST.tm
              in
           match uu____1104 with
           | FStar_Parser_AST.Product uu____1106 -> t
           | uu____1113 ->
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
      | uu____1149 -> (bs, t)
  
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild  -> true
    | FStar_Parser_AST.PatTvar (uu____1157,uu____1158) -> true
    | FStar_Parser_AST.PatVar (uu____1163,uu____1164) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____1170) -> is_var_pattern p1
    | uu____1183 -> false
  
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____1190) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____1203;
           FStar_Parser_AST.prange = uu____1204;_},uu____1205)
        -> true
    | uu____1216 -> false
  
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
    | uu____1230 -> p
  
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
            let uu____1300 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____1300 with
             | (name,args,uu____1343) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1393);
               FStar_Parser_AST.prange = uu____1394;_},args)
            when is_top_level1 ->
            let uu____1404 =
              let uu____1409 = FStar_Syntax_DsEnv.qualify env id1  in
              FStar_Util.Inr uu____1409  in
            (uu____1404, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1431);
               FStar_Parser_AST.prange = uu____1432;_},args)
            -> ((FStar_Util.Inl id1), args, FStar_Pervasives_Native.None)
        | uu____1462 -> failwith "Not an app pattern"
  
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
      | FStar_Parser_AST.PatConst uu____1512 -> acc
      | FStar_Parser_AST.PatVar
          (uu____1513,FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit
           ))
          -> acc
      | FStar_Parser_AST.PatName uu____1516 -> acc
      | FStar_Parser_AST.PatTvar uu____1517 -> acc
      | FStar_Parser_AST.PatOp uu____1524 -> acc
      | FStar_Parser_AST.PatApp (phead,pats) ->
          gather_pattern_bound_vars_from_list (phead :: pats)
      | FStar_Parser_AST.PatVar (x,uu____1532) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatTuple (pats,uu____1541) ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu____1556 =
            FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
          gather_pattern_bound_vars_from_list uu____1556
      | FStar_Parser_AST.PatAscribed (pat,uu____1564) ->
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
    match projectee with | LocalBinder _0 -> true | uu____1626 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____1662 -> false
  
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
  fun uu___115_1708  ->
    match uu___115_1708 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____1715 -> failwith "Impossible"
  
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
      fun uu___116_1754  ->
        match uu___116_1754 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____1782 = FStar_Syntax_Syntax.null_binder k  in
            (uu____1782, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____1791 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____1791 with
             | (env1,a1) ->
                 (((let uu___140_1817 = a1  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___140_1817.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___140_1817.FStar_Syntax_Syntax.index);
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
  fun uu____1846  ->
    match uu____1846 with
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
      let uu____1926 =
        let uu____1941 =
          let uu____1944 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____1944  in
        let uu____1945 =
          let uu____1954 =
            let uu____1961 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____1961)  in
          [uu____1954]  in
        (uu____1941, uu____1945)  in
      FStar_Syntax_Syntax.Tm_app uu____1926  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____1998 =
        let uu____2013 =
          let uu____2016 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____2016  in
        let uu____2017 =
          let uu____2026 =
            let uu____2033 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2033)  in
          [uu____2026]  in
        (uu____2013, uu____2017)  in
      FStar_Syntax_Syntax.Tm_app uu____1998  in
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
          let uu____2084 =
            let uu____2099 =
              let uu____2102 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____2102  in
            let uu____2103 =
              let uu____2112 =
                let uu____2119 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____2119)  in
              let uu____2122 =
                let uu____2131 =
                  let uu____2138 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____2138)  in
                [uu____2131]  in
              uu____2112 :: uu____2122  in
            (uu____2099, uu____2103)  in
          FStar_Syntax_Syntax.Tm_app uu____2084  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let (generalize_annotated_univs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun s  ->
    let bs_univnames bs =
      let uu____2184 =
        let uu____2197 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____2214  ->
               match uu____2214 with
               | ({ FStar_Syntax_Syntax.ppname = uu____2223;
                    FStar_Syntax_Syntax.index = uu____2224;
                    FStar_Syntax_Syntax.sort = t;_},uu____2226)
                   ->
                   let uu____2229 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____2229) uu____2197
         in
      FStar_All.pipe_right bs uu____2184  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____2243 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____2260 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____2286 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____2307,uu____2308,bs,t,uu____2311,uu____2312)
                            ->
                            let uu____2321 = bs_univnames bs  in
                            let uu____2324 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____2321 uu____2324
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____2327,uu____2328,t,uu____2330,uu____2331,uu____2332)
                            -> FStar_Syntax_Free.univnames t
                        | uu____2337 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____2286 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___141_2345 = s  in
        let uu____2346 =
          let uu____2347 =
            let uu____2356 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____2374,bs,t,lids1,lids2) ->
                          let uu___142_2387 = se  in
                          let uu____2388 =
                            let uu____2389 =
                              let uu____2406 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____2407 =
                                let uu____2408 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____2408 t  in
                              (lid, uvs, uu____2406, uu____2407, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____2389
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____2388;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___142_2387.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___142_2387.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___142_2387.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___142_2387.FStar_Syntax_Syntax.sigattrs)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____2420,t,tlid,n1,lids1) ->
                          let uu___143_2429 = se  in
                          let uu____2430 =
                            let uu____2431 =
                              let uu____2446 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____2446, tlid, n1, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____2431  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____2430;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___143_2429.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___143_2429.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___143_2429.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___143_2429.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____2449 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____2356, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____2347  in
        {
          FStar_Syntax_Syntax.sigel = uu____2346;
          FStar_Syntax_Syntax.sigrng =
            (uu___141_2345.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___141_2345.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___141_2345.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___141_2345.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2455,t) ->
        let uvs =
          let uu____2458 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____2458 FStar_Util.set_elements  in
        let uu___144_2463 = s  in
        let uu____2464 =
          let uu____2465 =
            let uu____2472 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____2472)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____2465  in
        {
          FStar_Syntax_Syntax.sigel = uu____2464;
          FStar_Syntax_Syntax.sigrng =
            (uu___144_2463.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___144_2463.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___144_2463.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___144_2463.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____2494 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____2497 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____2504) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____2533,(FStar_Util.Inl t,uu____2535),uu____2536)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____2583,(FStar_Util.Inr c,uu____2585),uu____2586)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____2633 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____2634,(FStar_Util.Inl t,uu____2636),uu____2637) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____2684,(FStar_Util.Inr c,uu____2686),uu____2687) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____2734 -> empty_set  in
          FStar_Util.set_union uu____2494 uu____2497  in
        let all_lb_univs =
          let uu____2738 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____2754 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____2754) empty_set)
             in
          FStar_All.pipe_right uu____2738 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___145_2764 = s  in
        let uu____2765 =
          let uu____2766 =
            let uu____2773 =
              let uu____2774 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___146_2786 = lb  in
                        let uu____2787 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____2790 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___146_2786.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____2787;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___146_2786.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____2790;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___146_2786.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___146_2786.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____2774)  in
            (uu____2773, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____2766  in
        {
          FStar_Syntax_Syntax.sigel = uu____2765;
          FStar_Syntax_Syntax.sigrng =
            (uu___145_2764.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___145_2764.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___145_2764.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___145_2764.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____2798,fml) ->
        let uvs =
          let uu____2801 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____2801 FStar_Util.set_elements  in
        let uu___147_2806 = s  in
        let uu____2807 =
          let uu____2808 =
            let uu____2815 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____2815)  in
          FStar_Syntax_Syntax.Sig_assume uu____2808  in
        {
          FStar_Syntax_Syntax.sigel = uu____2807;
          FStar_Syntax_Syntax.sigrng =
            (uu___147_2806.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___147_2806.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___147_2806.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___147_2806.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____2817,bs,c,flags1) ->
        let uvs =
          let uu____2826 =
            let uu____2829 = bs_univnames bs  in
            let uu____2832 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____2829 uu____2832  in
          FStar_All.pipe_right uu____2826 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___148_2840 = s  in
        let uu____2841 =
          let uu____2842 =
            let uu____2855 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____2856 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____2855, uu____2856, flags1)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____2842  in
        {
          FStar_Syntax_Syntax.sigel = uu____2841;
          FStar_Syntax_Syntax.sigrng =
            (uu___148_2840.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___148_2840.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___148_2840.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___148_2840.FStar_Syntax_Syntax.sigattrs)
        }
    | uu____2859 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___117_2864  ->
    match uu___117_2864 with
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
    | uu____2865 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = (Prims.parse_int "0")
      then u
      else
        (let uu____2877 = sum_to_universe u (n1 - (Prims.parse_int "1"))  in
         FStar_Syntax_Syntax.U_succ uu____2877)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____2896 =
      let uu____2897 = unparen t  in uu____2897.FStar_Parser_AST.tm  in
    match uu____2896 with
    | FStar_Parser_AST.Wild  ->
        let uu____2902 =
          let uu____2903 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____2903  in
        FStar_Util.Inr uu____2902
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____2914)) ->
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
             let uu____2979 = sum_to_universe u n1  in
             FStar_Util.Inr uu____2979
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____2990 = sum_to_universe u n1  in
             FStar_Util.Inr uu____2990
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____3001 =
               let uu____3006 =
                 let uu____3007 = FStar_Parser_AST.term_to_string t  in
                 Prims.strcat
                   "This universe might contain a sum of two universe variables "
                   uu____3007
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____3006)
                in
             FStar_Errors.raise_error uu____3001 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____3012 ->
        let rec aux t1 univargs =
          let uu____3046 =
            let uu____3047 = unparen t1  in uu____3047.FStar_Parser_AST.tm
             in
          match uu____3046 with
          | FStar_Parser_AST.App (t2,targ,uu____3054) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___118_3077  ->
                     match uu___118_3077 with
                     | FStar_Util.Inr uu____3082 -> true
                     | uu____3083 -> false) univargs
              then
                let uu____3088 =
                  let uu____3089 =
                    FStar_List.map
                      (fun uu___119_3098  ->
                         match uu___119_3098 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____3089  in
                FStar_Util.Inr uu____3088
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___120_3115  ->
                        match uu___120_3115 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____3121 -> failwith "impossible")
                     univargs
                    in
                 let uu____3122 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     (Prims.parse_int "0") nargs
                    in
                 FStar_Util.Inl uu____3122)
          | uu____3128 ->
              let uu____3129 =
                let uu____3134 =
                  let uu____3135 =
                    let uu____3136 = FStar_Parser_AST.term_to_string t1  in
                    Prims.strcat uu____3136 " in universe context"  in
                  Prims.strcat "Unexpected term " uu____3135  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3134)  in
              FStar_Errors.raise_error uu____3129 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____3145 ->
        let uu____3146 =
          let uu____3151 =
            let uu____3152 =
              let uu____3153 = FStar_Parser_AST.term_to_string t  in
              Prims.strcat uu____3153 " in universe context"  in
            Prims.strcat "Unexpected term " uu____3152  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3151)  in
        FStar_Errors.raise_error uu____3146 t.FStar_Parser_AST.range
  
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
    | (bv,b,e)::uu____3186 ->
        let uu____3209 =
          let uu____3214 =
            let uu____3215 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format2 "Unexpected antiquotation: %s(%s)"
              (if b then "`@" else "`#") uu____3215
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____3214)  in
        FStar_Errors.raise_error uu____3209 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'Auu____3225 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident,'Auu____3225) FStar_Pervasives_Native.tuple2
        Prims.list -> FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____3253 = FStar_List.hd fields  in
        match uu____3253 with
        | (f,uu____3263) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____3275 =
                match uu____3275 with
                | (f',uu____3281) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____3283 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____3283
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
              (let uu____3287 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____3287);
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
            | FStar_Syntax_Syntax.Pat_dot_term uu____3638 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_wild uu____3645 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_constant uu____3646 ->
                FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_var x ->
                FStar_Util.set_add x FStar_Syntax_Syntax.no_names
            | FStar_Syntax_Syntax.Pat_cons (uu____3648,pats1) ->
                let aux out uu____3686 =
                  match uu____3686 with
                  | (p2,uu____3698) ->
                      let intersection =
                        let uu____3706 = pat_vars p2  in
                        FStar_Util.set_intersect uu____3706 out  in
                      let uu____3709 = FStar_Util.set_is_empty intersection
                         in
                      if uu____3709
                      then
                        let uu____3712 = pat_vars p2  in
                        FStar_Util.set_union out uu____3712
                      else
                        (let duplicate_bv =
                           let uu____3717 =
                             FStar_Util.set_elements intersection  in
                           FStar_List.hd uu____3717  in
                         let uu____3720 =
                           let uu____3725 =
                             FStar_Util.format1
                               "Non-linear patterns are not permitted. %s appears more than once in this pattern."
                               (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                              in
                           (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                             uu____3725)
                            in
                         FStar_Errors.raise_error uu____3720 r)
                   in
                FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
             in
          match pats with
          | [] -> ()
          | p1::[] ->
              let uu____3745 = pat_vars p1  in
              FStar_All.pipe_right uu____3745 (fun a237  -> ())
          | p1::ps ->
              let pvars = pat_vars p1  in
              let aux p2 =
                let uu____3773 =
                  let uu____3774 = pat_vars p2  in
                  FStar_Util.set_eq pvars uu____3774  in
                if uu____3773
                then ()
                else
                  (let nonlinear_vars =
                     let uu____3781 = pat_vars p2  in
                     FStar_Util.set_symmetric_difference pvars uu____3781  in
                   let first_nonlinear_var =
                     let uu____3785 = FStar_Util.set_elements nonlinear_vars
                        in
                     FStar_List.hd uu____3785  in
                   let uu____3788 =
                     let uu____3793 =
                       FStar_Util.format1
                         "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                         (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                        in
                     (FStar_Errors.Fatal_IncoherentPatterns, uu____3793)  in
                   FStar_Errors.raise_error uu____3788 r)
                 in
              FStar_List.iter aux ps
           in
        (match (is_mut, (p.FStar_Parser_AST.pat)) with
         | (false ,uu____3797) -> ()
         | (true ,FStar_Parser_AST.PatVar uu____3798) -> ()
         | (true ,uu____3805) ->
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_LetMutableForVariablesOnly,
                 "let-mutable is for variables only")
               p.FStar_Parser_AST.prange);
        (let resolvex l e x =
           let uu____3828 =
             FStar_All.pipe_right l
               (FStar_Util.find_opt
                  (fun y  ->
                     (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                       x.FStar_Ident.idText))
              in
           match uu____3828 with
           | FStar_Pervasives_Native.Some y -> (l, e, y)
           | uu____3844 ->
               let uu____3847 =
                 if is_mut
                 then FStar_Syntax_DsEnv.push_bv_mutable e x
                 else FStar_Syntax_DsEnv.push_bv e x  in
               (match uu____3847 with | (e1,x1) -> ((x1 :: l), e1, x1))
            in
         let rec aux' top loc env1 p1 =
           let pos q =
             FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange  in
           let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
           let orig = p1  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr uu____3959 -> failwith "impossible"
           | FStar_Parser_AST.PatOp op ->
               let uu____3975 =
                 let uu____3976 =
                   let uu____3977 =
                     let uu____3984 =
                       let uu____3985 =
                         let uu____3990 =
                           FStar_Parser_AST.compile_op (Prims.parse_int "0")
                             op.FStar_Ident.idText op.FStar_Ident.idRange
                            in
                         (uu____3990, (op.FStar_Ident.idRange))  in
                       FStar_Ident.mk_ident uu____3985  in
                     (uu____3984, FStar_Pervasives_Native.None)  in
                   FStar_Parser_AST.PatVar uu____3977  in
                 {
                   FStar_Parser_AST.pat = uu____3976;
                   FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
                 }  in
               aux loc env1 uu____3975
           | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
               ((match tacopt with
                 | FStar_Pervasives_Native.None  -> ()
                 | FStar_Pervasives_Native.Some uu____4007 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                         "Type ascriptions within patterns are cannot be associated with a tactic")
                       orig.FStar_Parser_AST.prange);
                (let uu____4008 = aux loc env1 p2  in
                 match uu____4008 with
                 | (loc1,env',binder,p3,imp) ->
                     let annot_pat_var p4 t1 =
                       match p4.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let uu___149_4066 = p4  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_var
                                  (let uu___150_4071 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___150_4071.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___150_4071.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }));
                             FStar_Syntax_Syntax.p =
                               (uu___149_4066.FStar_Syntax_Syntax.p)
                           }
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let uu___151_4073 = p4  in
                           {
                             FStar_Syntax_Syntax.v =
                               (FStar_Syntax_Syntax.Pat_wild
                                  (let uu___152_4078 = x  in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___152_4078.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___152_4078.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = t1
                                   }));
                             FStar_Syntax_Syntax.p =
                               (uu___151_4073.FStar_Syntax_Syntax.p)
                           }
                       | uu____4079 when top -> p4
                       | uu____4080 ->
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                               "Type ascriptions within patterns are only allowed on variables")
                             orig.FStar_Parser_AST.prange
                        in
                     let uu____4083 =
                       match binder with
                       | LetBinder uu____4096 -> failwith "impossible"
                       | LocalBinder (x,aq) ->
                           let t1 =
                             let uu____4116 = close_fun env1 t  in
                             desugar_term env1 uu____4116  in
                           (if
                              (match (x.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n
                               with
                               | FStar_Syntax_Syntax.Tm_unknown  -> false
                               | uu____4118 -> true)
                            then
                              (let uu____4119 =
                                 let uu____4124 =
                                   let uu____4125 =
                                     FStar_Syntax_Print.bv_to_string x  in
                                   let uu____4126 =
                                     FStar_Syntax_Print.term_to_string
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____4127 =
                                     FStar_Syntax_Print.term_to_string t1  in
                                   FStar_Util.format3
                                     "Multiple ascriptions for %s in pattern, type %s was shadowed by %s\n"
                                     uu____4125 uu____4126 uu____4127
                                    in
                                 (FStar_Errors.Warning_MultipleAscriptions,
                                   uu____4124)
                                  in
                               FStar_Errors.log_issue
                                 orig.FStar_Parser_AST.prange uu____4119)
                            else ();
                            (let uu____4129 = annot_pat_var p3 t1  in
                             (uu____4129,
                               (LocalBinder
                                  ((let uu___153_4135 = x  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___153_4135.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___153_4135.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    }), aq)))))
                        in
                     (match uu____4083 with
                      | (p4,binder1) -> (loc1, env', binder1, p4, imp))))
           | FStar_Parser_AST.PatWild  ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____4157 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____4157, false)
           | FStar_Parser_AST.PatConst c ->
               let x =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                   FStar_Syntax_Syntax.tun
                  in
               let uu____4166 =
                 FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____4166, false)
           | FStar_Parser_AST.PatTvar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual aq  in
               let uu____4185 = resolvex loc env1 x  in
               (match uu____4185 with
                | (loc1,env2,xbv) ->
                    let uu____4207 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____4207, imp))
           | FStar_Parser_AST.PatVar (x,aq) ->
               let imp =
                 aq =
                   (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
                  in
               let aq1 = trans_aqual aq  in
               let uu____4226 = resolvex loc env1 x  in
               (match uu____4226 with
                | (loc1,env2,xbv) ->
                    let uu____4248 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_var xbv)
                       in
                    (loc1, env2, (LocalBinder (xbv, aq1)), uu____4248, imp))
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
               let uu____4258 =
                 FStar_All.pipe_left pos
                   (FStar_Syntax_Syntax.Pat_cons (l1, []))
                  in
               (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                 uu____4258, false)
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                  FStar_Parser_AST.prange = uu____4280;_},args)
               ->
               let uu____4286 =
                 FStar_List.fold_right
                   (fun arg  ->
                      fun uu____4327  ->
                        match uu____4327 with
                        | (loc1,env2,args1) ->
                            let uu____4375 = aux loc1 env2 arg  in
                            (match uu____4375 with
                             | (loc2,env3,uu____4404,arg1,imp) ->
                                 (loc2, env3, ((arg1, imp) :: args1)))) args
                   (loc, env1, [])
                  in
               (match uu____4286 with
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
                    let uu____4474 =
                      FStar_All.pipe_left pos
                        (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                       in
                    (loc1, env2,
                      (LocalBinder (x, FStar_Pervasives_Native.None)),
                      uu____4474, false))
           | FStar_Parser_AST.PatApp uu____4489 ->
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                 p1.FStar_Parser_AST.prange
           | FStar_Parser_AST.PatList pats ->
               let uu____4511 =
                 FStar_List.fold_right
                   (fun pat  ->
                      fun uu____4544  ->
                        match uu____4544 with
                        | (loc1,env2,pats1) ->
                            let uu____4576 = aux loc1 env2 pat  in
                            (match uu____4576 with
                             | (loc2,env3,uu____4601,pat1,uu____4603) ->
                                 (loc2, env3, (pat1 :: pats1)))) pats
                   (loc, env1, [])
                  in
               (match uu____4511 with
                | (loc1,env2,pats1) ->
                    let pat =
                      let uu____4646 =
                        let uu____4649 =
                          let uu____4656 =
                            FStar_Range.end_range p1.FStar_Parser_AST.prange
                             in
                          pos_r uu____4656  in
                        let uu____4657 =
                          let uu____4658 =
                            let uu____4671 =
                              FStar_Syntax_Syntax.lid_as_fv
                                FStar_Parser_Const.nil_lid
                                FStar_Syntax_Syntax.delta_constant
                                (FStar_Pervasives_Native.Some
                                   FStar_Syntax_Syntax.Data_ctor)
                               in
                            (uu____4671, [])  in
                          FStar_Syntax_Syntax.Pat_cons uu____4658  in
                        FStar_All.pipe_left uu____4649 uu____4657  in
                      FStar_List.fold_right
                        (fun hd1  ->
                           fun tl1  ->
                             let r =
                               FStar_Range.union_ranges
                                 hd1.FStar_Syntax_Syntax.p
                                 tl1.FStar_Syntax_Syntax.p
                                in
                             let uu____4703 =
                               let uu____4704 =
                                 let uu____4717 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.cons_lid
                                     FStar_Syntax_Syntax.delta_constant
                                     (FStar_Pervasives_Native.Some
                                        FStar_Syntax_Syntax.Data_ctor)
                                    in
                                 (uu____4717, [(hd1, false); (tl1, false)])
                                  in
                               FStar_Syntax_Syntax.Pat_cons uu____4704  in
                             FStar_All.pipe_left (pos_r r) uu____4703) pats1
                        uu____4646
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
               let uu____4759 =
                 FStar_List.fold_left
                   (fun uu____4799  ->
                      fun p2  ->
                        match uu____4799 with
                        | (loc1,env2,pats) ->
                            let uu____4848 = aux loc1 env2 p2  in
                            (match uu____4848 with
                             | (loc2,env3,uu____4877,pat,uu____4879) ->
                                 (loc2, env3, ((pat, false) :: pats))))
                   (loc, env1, []) args
                  in
               (match uu____4759 with
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
                    let uu____4974 =
                      FStar_Syntax_DsEnv.fail_or env2
                        (FStar_Syntax_DsEnv.try_lookup_lid env2) l
                       in
                    (match uu____4974 with
                     | (constr,uu____4996) ->
                         let l1 =
                           match constr.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                           | uu____4999 -> failwith "impossible"  in
                         let x =
                           FStar_Syntax_Syntax.new_bv
                             (FStar_Pervasives_Native.Some
                                (p1.FStar_Parser_AST.prange))
                             FStar_Syntax_Syntax.tun
                            in
                         let uu____5001 =
                           FStar_All.pipe_left pos
                             (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                            in
                         (loc1, env2,
                           (LocalBinder (x, FStar_Pervasives_Native.None)),
                           uu____5001, false)))
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
                      (fun uu____5070  ->
                         match uu____5070 with
                         | (f,p2) -> ((f.FStar_Ident.ident), p2)))
                  in
               let args =
                 FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                   (FStar_List.map
                      (fun uu____5100  ->
                         match uu____5100 with
                         | (f,uu____5106) ->
                             let uu____5107 =
                               FStar_All.pipe_right fields1
                                 (FStar_List.tryFind
                                    (fun uu____5133  ->
                                       match uu____5133 with
                                       | (g,uu____5139) ->
                                           f.FStar_Ident.idText =
                                             g.FStar_Ident.idText))
                                in
                             (match uu____5107 with
                              | FStar_Pervasives_Native.None  ->
                                  FStar_Parser_AST.mk_pattern
                                    FStar_Parser_AST.PatWild
                                    p1.FStar_Parser_AST.prange
                              | FStar_Pervasives_Native.Some (uu____5144,p2)
                                  -> p2)))
                  in
               let app =
                 let uu____5151 =
                   let uu____5152 =
                     let uu____5159 =
                       let uu____5160 =
                         let uu____5161 =
                           FStar_Ident.lid_of_ids
                             (FStar_List.append
                                (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                                [record.FStar_Syntax_DsEnv.constrname])
                            in
                         FStar_Parser_AST.PatName uu____5161  in
                       FStar_Parser_AST.mk_pattern uu____5160
                         p1.FStar_Parser_AST.prange
                        in
                     (uu____5159, args)  in
                   FStar_Parser_AST.PatApp uu____5152  in
                 FStar_Parser_AST.mk_pattern uu____5151
                   p1.FStar_Parser_AST.prange
                  in
               let uu____5164 = aux loc env1 app  in
               (match uu____5164 with
                | (env2,e,b,p2,uu____5193) ->
                    let p3 =
                      match p2.FStar_Syntax_Syntax.v with
                      | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                          let uu____5221 =
                            let uu____5222 =
                              let uu____5235 =
                                let uu___154_5236 = fv  in
                                let uu____5237 =
                                  let uu____5240 =
                                    let uu____5241 =
                                      let uu____5248 =
                                        FStar_All.pipe_right
                                          record.FStar_Syntax_DsEnv.fields
                                          (FStar_List.map
                                             FStar_Pervasives_Native.fst)
                                         in
                                      ((record.FStar_Syntax_DsEnv.typename),
                                        uu____5248)
                                       in
                                    FStar_Syntax_Syntax.Record_ctor
                                      uu____5241
                                     in
                                  FStar_Pervasives_Native.Some uu____5240  in
                                {
                                  FStar_Syntax_Syntax.fv_name =
                                    (uu___154_5236.FStar_Syntax_Syntax.fv_name);
                                  FStar_Syntax_Syntax.fv_delta =
                                    (uu___154_5236.FStar_Syntax_Syntax.fv_delta);
                                  FStar_Syntax_Syntax.fv_qual = uu____5237
                                }  in
                              (uu____5235, args1)  in
                            FStar_Syntax_Syntax.Pat_cons uu____5222  in
                          FStar_All.pipe_left pos uu____5221
                      | uu____5275 -> p2  in
                    (env2, e, b, p3, false))
         
         and aux loc env1 p1 = aux' false loc env1 p1
          in
         let aux_maybe_or env1 p1 =
           let loc = []  in
           match p1.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr [] -> failwith "impossible"
           | FStar_Parser_AST.PatOr (p2::ps) ->
               let uu____5329 = aux' true loc env1 p2  in
               (match uu____5329 with
                | (loc1,env2,var,p3,uu____5356) ->
                    let uu____5361 =
                      FStar_List.fold_left
                        (fun uu____5393  ->
                           fun p4  ->
                             match uu____5393 with
                             | (loc2,env3,ps1) ->
                                 let uu____5426 = aux' true loc2 env3 p4  in
                                 (match uu____5426 with
                                  | (loc3,env4,uu____5451,p5,uu____5453) ->
                                      (loc3, env4, (p5 :: ps1))))
                        (loc1, env2, []) ps
                       in
                    (match uu____5361 with
                     | (loc2,env3,ps1) ->
                         let pats = p3 :: (FStar_List.rev ps1)  in
                         (env3, var, pats)))
           | uu____5504 ->
               let uu____5505 = aux' true loc env1 p1  in
               (match uu____5505 with
                | (loc1,env2,vars,pat,b) -> (env2, vars, [pat]))
            in
         let uu____5545 = aux_maybe_or env p  in
         match uu____5545 with
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
            let uu____5604 =
              let uu____5605 =
                let uu____5616 = FStar_Syntax_DsEnv.qualify env x  in
                (uu____5616,
                  (FStar_Syntax_Syntax.tun, FStar_Pervasives_Native.None))
                 in
              LetBinder uu____5605  in
            (env, uu____5604, [])  in
          if top
          then
            match p.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatOp x ->
                let uu____5644 =
                  let uu____5645 =
                    let uu____5650 =
                      FStar_Parser_AST.compile_op (Prims.parse_int "0")
                        x.FStar_Ident.idText x.FStar_Ident.idRange
                       in
                    (uu____5650, (x.FStar_Ident.idRange))  in
                  FStar_Ident.mk_ident uu____5645  in
                mklet uu____5644
            | FStar_Parser_AST.PatVar (x,uu____5652) -> mklet x
            | FStar_Parser_AST.PatAscribed
                ({
                   FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                     (x,uu____5658);
                   FStar_Parser_AST.prange = uu____5659;_},(t,tacopt))
                ->
                let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)
                   in
                let uu____5679 =
                  let uu____5680 =
                    let uu____5691 = FStar_Syntax_DsEnv.qualify env x  in
                    let uu____5692 =
                      let uu____5699 = desugar_term env t  in
                      (uu____5699, tacopt1)  in
                    (uu____5691, uu____5692)  in
                  LetBinder uu____5680  in
                (env, uu____5679, [])
            | uu____5710 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_UnexpectedPattern,
                    "Unexpected pattern at the top-level")
                  p.FStar_Parser_AST.prange
          else
            (let uu____5720 = desugar_data_pat env p is_mut  in
             match uu____5720 with
             | (env1,binder,p1) ->
                 let p2 =
                   match p1 with
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                         uu____5749;
                       FStar_Syntax_Syntax.p = uu____5750;_}::[] -> []
                   | {
                       FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                         uu____5751;
                       FStar_Syntax_Syntax.p = uu____5752;_}::[] -> []
                   | uu____5753 -> p1  in
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
  fun uu____5760  ->
    fun env  ->
      fun pat  ->
        let uu____5763 = desugar_data_pat env pat false  in
        match uu____5763 with | (env1,uu____5779,pat1) -> (env1, pat1)

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
      let uu____5798 = desugar_term_aq env e  in
      match uu____5798 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____5815 = desugar_typ_aq env e  in
      match uu____5815 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness,FStar_Const.width)
        FStar_Pervasives_Native.tuple2 ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____5825  ->
        fun range  ->
          match uu____5825 with
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
              ((let uu____5835 =
                  let uu____5836 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____5836  in
                if uu____5835
                then
                  let uu____5837 =
                    let uu____5842 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____5842)  in
                  FStar_Errors.log_issue range uu____5837
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
                  let uu____5847 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____5847 range  in
                let lid1 =
                  let uu____5851 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____5851 with
                  | FStar_Pervasives_Native.Some (intro_term,uu____5861) ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____5870 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____5870 range  in
                           let private_fv =
                             let uu____5872 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____5872 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___155_5873 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___155_5873.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___155_5873.FStar_Syntax_Syntax.vars)
                           }
                       | uu____5874 ->
                           failwith
                             (Prims.strcat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____5881 =
                        let uu____5886 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____5886)
                         in
                      FStar_Errors.raise_error uu____5881 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____5902 =
                  let uu____5909 =
                    let uu____5910 =
                      let uu____5925 =
                        let uu____5934 =
                          let uu____5941 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____5941)  in
                        [uu____5934]  in
                      (lid1, uu____5925)  in
                    FStar_Syntax_Syntax.Tm_app uu____5910  in
                  FStar_Syntax_Syntax.mk uu____5909  in
                uu____5902 FStar_Pervasives_Native.None range))

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
            let uu____5980 =
              let uu____5989 =
                (if resolve
                 then FStar_Syntax_DsEnv.try_lookup_lid_with_attributes
                 else
                   FStar_Syntax_DsEnv.try_lookup_lid_with_attributes_no_resolve)
                  env
                 in
              FStar_Syntax_DsEnv.fail_or env uu____5989 l  in
            match uu____5980 with
            | (tm,mut,attrs) ->
                let warn_if_deprecated attrs1 =
                  FStar_List.iter
                    (fun a  ->
                       match a.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_app
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____6044;
                              FStar_Syntax_Syntax.vars = uu____6045;_},args)
                           when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____6068 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____6068 " is deprecated"  in
                           let msg1 =
                             if
                               (FStar_List.length args) >
                                 (Prims.parse_int "0")
                             then
                               let uu____6076 =
                                 let uu____6077 =
                                   let uu____6080 = FStar_List.hd args  in
                                   FStar_Pervasives_Native.fst uu____6080  in
                                 uu____6077.FStar_Syntax_Syntax.n  in
                               match uu____6076 with
                               | FStar_Syntax_Syntax.Tm_constant
                                   (FStar_Const.Const_string (s,uu____6096))
                                   when
                                   Prims.op_Negation
                                     ((FStar_Util.trim_string s) = "")
                                   ->
                                   Prims.strcat msg
                                     (Prims.strcat ", use "
                                        (Prims.strcat s " instead"))
                               | uu____6097 -> msg
                             else msg  in
                           let uu____6099 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____6099
                             (FStar_Errors.Warning_DeprecatedDefinition,
                               msg1)
                       | FStar_Syntax_Syntax.Tm_fvar fv when
                           FStar_Ident.lid_equals
                             (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             FStar_Parser_Const.deprecated_attr
                           ->
                           let msg =
                             let uu____6102 =
                               FStar_Syntax_Print.term_to_string tm  in
                             Prims.strcat uu____6102 " is deprecated"  in
                           let uu____6103 = FStar_Ident.range_of_lid l  in
                           FStar_Errors.log_issue uu____6103
                             (FStar_Errors.Warning_DeprecatedDefinition, msg)
                       | uu____6104 -> ()) attrs1
                   in
                (warn_if_deprecated attrs;
                 (let tm1 = setpos tm  in
                  if mut
                  then
                    let uu____6109 =
                      let uu____6110 =
                        let uu____6117 = mk_ref_read tm1  in
                        (uu____6117,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Mutable_rval))
                         in
                      FStar_Syntax_Syntax.Tm_meta uu____6110  in
                    FStar_All.pipe_left mk1 uu____6109
                  else tm1))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____6135 =
          let uu____6136 = unparen t  in uu____6136.FStar_Parser_AST.tm  in
        match uu____6135 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____6137; FStar_Ident.ident = uu____6138;
              FStar_Ident.nsstr = uu____6139; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____6142 ->
            let uu____6143 =
              let uu____6148 =
                let uu____6149 = FStar_Parser_AST.term_to_string t  in
                Prims.strcat "Unknown attribute " uu____6149  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____6148)  in
            FStar_Errors.raise_error uu____6143 t.FStar_Parser_AST.range
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
          let uu___156_6244 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___156_6244.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___156_6244.FStar_Syntax_Syntax.vars)
          }  in
        let uu____6247 =
          let uu____6248 = unparen top  in uu____6248.FStar_Parser_AST.tm  in
        match uu____6247 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____6253 ->
            let uu____6260 = desugar_formula env top  in (uu____6260, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____6267 = desugar_formula env t  in (uu____6267, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____6274 = desugar_formula env t  in (uu____6274, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____6298 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____6298, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____6300 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____6300, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____6308 =
                let uu____6309 =
                  let uu____6316 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____6316, args)  in
                FStar_Parser_AST.Op uu____6309  in
              FStar_Parser_AST.mk_term uu____6308 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____6319 =
              let uu____6320 =
                let uu____6321 =
                  let uu____6328 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____6328, [e])  in
                FStar_Parser_AST.Op uu____6321  in
              FStar_Parser_AST.mk_term uu____6320 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____6319
        | FStar_Parser_AST.Op (op_star,uu____6332::uu____6333::[]) when
            (let uu____6338 = FStar_Ident.text_of_id op_star  in
             uu____6338 = "*") &&
              (let uu____6340 =
                 op_as_term env (Prims.parse_int "2")
                   top.FStar_Parser_AST.range op_star
                  in
               FStar_All.pipe_right uu____6340 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____6355;_},t1::t2::[])
                  ->
                  let uu____6360 = flatten1 t1  in
                  FStar_List.append uu____6360 [t2]
              | uu____6363 -> [t]  in
            let uu____6364 =
              let uu____6389 =
                let uu____6412 =
                  let uu____6415 = unparen top  in flatten1 uu____6415  in
                FStar_All.pipe_right uu____6412
                  (FStar_List.map
                     (fun t  ->
                        let uu____6434 = desugar_typ_aq env t  in
                        match uu____6434 with
                        | (t',aq) ->
                            let uu____6445 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____6445, aq)))
                 in
              FStar_All.pipe_right uu____6389 FStar_List.unzip  in
            (match uu____6364 with
             | (targs,aqs) ->
                 let uu____6554 =
                   let uu____6559 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____6559
                    in
                 (match uu____6554 with
                  | (tup,uu____6575) ->
                      let uu____6576 =
                        mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                      (uu____6576, (join_aqs aqs))))
        | FStar_Parser_AST.Tvar a ->
            let uu____6588 =
              let uu____6589 =
                let uu____6592 =
                  FStar_Syntax_DsEnv.fail_or2
                    (FStar_Syntax_DsEnv.try_lookup_id env) a
                   in
                FStar_Pervasives_Native.fst uu____6592  in
              FStar_All.pipe_left setpos uu____6589  in
            (uu____6588, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____6604 =
              let uu____6609 =
                let uu____6610 =
                  let uu____6611 = FStar_Ident.text_of_id u  in
                  Prims.strcat uu____6611 " in non-universe context"  in
                Prims.strcat "Unexpected universe variable " uu____6610  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____6609)  in
            FStar_Errors.raise_error uu____6604 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____6622 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____6622 with
             | FStar_Pervasives_Native.None  ->
                 let uu____6629 =
                   let uu____6634 =
                     let uu____6635 = FStar_Ident.text_of_id s  in
                     Prims.strcat "Unexpected or unbound operator: "
                       uu____6635
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____6634)
                    in
                 FStar_Errors.raise_error uu____6629
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > (Prims.parse_int "0")
                 then
                   let uu____6645 =
                     let uu____6670 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____6722 = desugar_term_aq env t  in
                               match uu____6722 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____6670 FStar_List.unzip  in
                   (match uu____6645 with
                    | (args1,aqs) ->
                        let uu____6855 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____6855, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____6869)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____6884 =
              let uu___157_6885 = top  in
              let uu____6886 =
                let uu____6887 =
                  let uu____6894 =
                    let uu___158_6895 = top  in
                    let uu____6896 =
                      let uu____6897 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____6897  in
                    {
                      FStar_Parser_AST.tm = uu____6896;
                      FStar_Parser_AST.range =
                        (uu___158_6895.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___158_6895.FStar_Parser_AST.level)
                    }  in
                  (uu____6894, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____6887  in
              {
                FStar_Parser_AST.tm = uu____6886;
                FStar_Parser_AST.range =
                  (uu___157_6885.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___157_6885.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____6884
        | FStar_Parser_AST.Construct (n1,(a,uu____6900)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____6916 =
                let uu___159_6917 = top  in
                let uu____6918 =
                  let uu____6919 =
                    let uu____6926 =
                      let uu___160_6927 = top  in
                      let uu____6928 =
                        let uu____6929 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____6929  in
                      {
                        FStar_Parser_AST.tm = uu____6928;
                        FStar_Parser_AST.range =
                          (uu___160_6927.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___160_6927.FStar_Parser_AST.level)
                      }  in
                    (uu____6926, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____6919  in
                {
                  FStar_Parser_AST.tm = uu____6918;
                  FStar_Parser_AST.range =
                    (uu___159_6917.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___159_6917.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____6916))
        | FStar_Parser_AST.Construct (n1,(a,uu____6932)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____6947 =
              let uu___161_6948 = top  in
              let uu____6949 =
                let uu____6950 =
                  let uu____6957 =
                    let uu___162_6958 = top  in
                    let uu____6959 =
                      let uu____6960 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____6960  in
                    {
                      FStar_Parser_AST.tm = uu____6959;
                      FStar_Parser_AST.range =
                        (uu___162_6958.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___162_6958.FStar_Parser_AST.level)
                    }  in
                  (uu____6957, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____6950  in
              {
                FStar_Parser_AST.tm = uu____6949;
                FStar_Parser_AST.range =
                  (uu___161_6948.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___161_6948.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____6947
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____6961; FStar_Ident.ident = uu____6962;
              FStar_Ident.nsstr = uu____6963; FStar_Ident.str = "Type0";_}
            ->
            let uu____6966 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____6966, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____6967; FStar_Ident.ident = uu____6968;
              FStar_Ident.nsstr = uu____6969; FStar_Ident.str = "Type";_}
            ->
            let uu____6972 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____6972, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____6973; FStar_Ident.ident = uu____6974;
               FStar_Ident.nsstr = uu____6975; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____6993 =
              let uu____6994 =
                let uu____6995 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____6995  in
              mk1 uu____6994  in
            (uu____6993, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____6996; FStar_Ident.ident = uu____6997;
              FStar_Ident.nsstr = uu____6998; FStar_Ident.str = "Effect";_}
            ->
            let uu____7001 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____7001, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____7002; FStar_Ident.ident = uu____7003;
              FStar_Ident.nsstr = uu____7004; FStar_Ident.str = "True";_}
            ->
            let uu____7007 =
              let uu____7008 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____7008
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____7007, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____7009; FStar_Ident.ident = uu____7010;
              FStar_Ident.nsstr = uu____7011; FStar_Ident.str = "False";_}
            ->
            let uu____7014 =
              let uu____7015 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____7015
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____7014, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____7018;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____7020 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____7020 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____7029 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_constant_at_level
                         (Prims.parse_int "1")) FStar_Pervasives_Native.None
                     in
                  (uu____7029, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____7030 =
                    let uu____7031 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____7031 txt
                     in
                  failwith uu____7030))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____7038 = desugar_name mk1 setpos env true l  in
              (uu____7038, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____7041 = desugar_name mk1 setpos env true l  in
              (uu____7041, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____7052 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____7052 with
                | FStar_Pervasives_Native.Some uu____7061 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____7066 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____7066 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____7080 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____7097 =
                    let uu____7098 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____7098  in
                  (uu____7097, noaqs)
              | uu____7099 ->
                  let uu____7106 =
                    let uu____7111 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____7111)  in
                  FStar_Errors.raise_error uu____7106
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____7118 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____7118 with
              | FStar_Pervasives_Native.None  ->
                  let uu____7125 =
                    let uu____7130 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____7130)
                     in
                  FStar_Errors.raise_error uu____7125
                    top.FStar_Parser_AST.range
              | uu____7135 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____7139 = desugar_name mk1 setpos env true lid'  in
                  (uu____7139, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____7155 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____7155 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____7174 ->
                       let uu____7181 =
                         FStar_Util.take
                           (fun uu____7205  ->
                              match uu____7205 with
                              | (uu____7210,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____7181 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____7255 =
                              let uu____7280 =
                                FStar_List.map
                                  (fun uu____7323  ->
                                     match uu____7323 with
                                     | (t,imp) ->
                                         let uu____7340 =
                                           desugar_term_aq env t  in
                                         (match uu____7340 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____7280
                                FStar_List.unzip
                               in
                            (match uu____7255 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____7481 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____7481, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____7497 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____7497 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.strcat "Constructor "
                             (Prims.strcat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____7504 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.strcat "Effect "
                             (Prims.strcat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____7515 =
              FStar_List.fold_left
                (fun uu____7560  ->
                   fun b  ->
                     match uu____7560 with
                     | (env1,tparams,typs) ->
                         let uu____7617 = desugar_binder env1 b  in
                         (match uu____7617 with
                          | (xopt,t1) ->
                              let uu____7646 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____7655 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____7655)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____7646 with
                               | (env2,x) ->
                                   let uu____7675 =
                                     let uu____7678 =
                                       let uu____7681 =
                                         let uu____7682 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____7682
                                          in
                                       [uu____7681]  in
                                     FStar_List.append typs uu____7678  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___163_7708 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___163_7708.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___163_7708.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____7675)))) (env, [], [])
                (FStar_List.append binders
                   [FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                      t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                      FStar_Pervasives_Native.None])
               in
            (match uu____7515 with
             | (env1,uu____7736,targs) ->
                 let uu____7758 =
                   let uu____7763 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____7763
                    in
                 (match uu____7758 with
                  | (tup,uu____7773) ->
                      let uu____7774 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_app (tup, targs))
                         in
                      (uu____7774, noaqs)))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____7791 = uncurry binders t  in
            (match uu____7791 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___121_7833 =
                   match uu___121_7833 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range env1 t1  in
                       let uu____7847 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____7847
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____7869 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____7869 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____7902 = aux env [] bs  in (uu____7902, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____7909 = desugar_binder env b  in
            (match uu____7909 with
             | (FStar_Pervasives_Native.None ,uu____7920) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____7934 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____7934 with
                  | ((x,uu____7950),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____7963 =
                        let uu____7964 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____7964  in
                      (uu____7963, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let binders1 =
              FStar_All.pipe_right binders
                (FStar_List.map replace_unit_pattern)
               in
            let uu____7982 =
              FStar_List.fold_left
                (fun uu____8002  ->
                   fun pat  ->
                     match uu____8002 with
                     | (env1,ftvs) ->
                         (match pat.FStar_Parser_AST.pat with
                          | FStar_Parser_AST.PatAscribed
                              (uu____8028,(t,FStar_Pervasives_Native.None ))
                              ->
                              let uu____8038 =
                                let uu____8041 = free_type_vars env1 t  in
                                FStar_List.append uu____8041 ftvs  in
                              (env1, uu____8038)
                          | FStar_Parser_AST.PatAscribed
                              (uu____8046,(t,FStar_Pervasives_Native.Some
                                           tac))
                              ->
                              let uu____8057 =
                                let uu____8060 = free_type_vars env1 t  in
                                let uu____8063 =
                                  let uu____8066 = free_type_vars env1 tac
                                     in
                                  FStar_List.append uu____8066 ftvs  in
                                FStar_List.append uu____8060 uu____8063  in
                              (env1, uu____8057)
                          | uu____8071 -> (env1, ftvs))) (env, []) binders1
               in
            (match uu____7982 with
             | (uu____8080,ftv) ->
                 let ftv1 = sort_ftv ftv  in
                 let binders2 =
                   let uu____8092 =
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
                   FStar_List.append uu____8092 binders1  in
                 let rec aux env1 bs sc_pat_opt uu___122_8147 =
                   match uu___122_8147 with
                   | [] ->
                       let uu____8172 = desugar_term_aq env1 body  in
                       (match uu____8172 with
                        | (body1,aq) ->
                            let body2 =
                              match sc_pat_opt with
                              | FStar_Pervasives_Native.Some (sc,pat) ->
                                  let body2 =
                                    let uu____8209 =
                                      let uu____8210 =
                                        FStar_Syntax_Syntax.pat_bvs pat  in
                                      FStar_All.pipe_right uu____8210
                                        (FStar_List.map
                                           FStar_Syntax_Syntax.mk_binder)
                                       in
                                    FStar_Syntax_Subst.close uu____8209 body1
                                     in
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_match
                                       (sc,
                                         [(pat, FStar_Pervasives_Native.None,
                                            body2)]))
                                    FStar_Pervasives_Native.None
                                    body2.FStar_Syntax_Syntax.pos
                              | FStar_Pervasives_Native.None  -> body1  in
                            let uu____8279 =
                              let uu____8282 =
                                no_annot_abs (FStar_List.rev bs) body2  in
                              setpos uu____8282  in
                            (uu____8279, aq))
                   | p::rest ->
                       let uu____8295 = desugar_binding_pat env1 p  in
                       (match uu____8295 with
                        | (env2,b,pat) ->
                            let pat1 =
                              match pat with
                              | [] -> FStar_Pervasives_Native.None
                              | p1::[] -> FStar_Pervasives_Native.Some p1
                              | uu____8329 ->
                                  FStar_Errors.raise_error
                                    (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                      "Disjunctive patterns are not supported in abstractions")
                                    p.FStar_Parser_AST.prange
                               in
                            let uu____8336 =
                              match b with
                              | LetBinder uu____8373 -> failwith "Impossible"
                              | LocalBinder (x,aq) ->
                                  let sc_pat_opt1 =
                                    match (pat1, sc_pat_opt) with
                                    | (FStar_Pervasives_Native.None
                                       ,uu____8439) -> sc_pat_opt
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.None ) ->
                                        let uu____8493 =
                                          let uu____8500 =
                                            FStar_Syntax_Syntax.bv_to_name x
                                             in
                                          (uu____8500, p1)  in
                                        FStar_Pervasives_Native.Some
                                          uu____8493
                                    | (FStar_Pervasives_Native.Some
                                       p1,FStar_Pervasives_Native.Some
                                       (sc,p')) ->
                                        (match ((sc.FStar_Syntax_Syntax.n),
                                                 (p'.FStar_Syntax_Syntax.v))
                                         with
                                         | (FStar_Syntax_Syntax.Tm_name
                                            uu____8556,uu____8557) ->
                                             let tup2 =
                                               let uu____8559 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   (Prims.parse_int "2")
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____8559
                                                 FStar_Syntax_Syntax.delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____8563 =
                                                 let uu____8570 =
                                                   let uu____8571 =
                                                     let uu____8586 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            tup2)
                                                        in
                                                     let uu____8589 =
                                                       let uu____8598 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           sc
                                                          in
                                                       let uu____8605 =
                                                         let uu____8614 =
                                                           let uu____8621 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               x
                                                              in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.as_arg
                                                             uu____8621
                                                            in
                                                         [uu____8614]  in
                                                       uu____8598 ::
                                                         uu____8605
                                                        in
                                                     (uu____8586, uu____8589)
                                                      in
                                                   FStar_Syntax_Syntax.Tm_app
                                                     uu____8571
                                                    in
                                                 FStar_Syntax_Syntax.mk
                                                   uu____8570
                                                  in
                                               uu____8563
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Parser_AST.range
                                                in
                                             let p2 =
                                               let uu____8656 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tup2,
                                                      [(p', false);
                                                      (p1, false)]))
                                                 uu____8656
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | (FStar_Syntax_Syntax.Tm_app
                                            (uu____8699,args),FStar_Syntax_Syntax.Pat_cons
                                            (uu____8701,pats)) ->
                                             let tupn =
                                               let uu____8740 =
                                                 FStar_Parser_Const.mk_tuple_data_lid
                                                   ((Prims.parse_int "1") +
                                                      (FStar_List.length args))
                                                   top.FStar_Parser_AST.range
                                                  in
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 uu____8740
                                                 FStar_Syntax_Syntax.delta_constant
                                                 (FStar_Pervasives_Native.Some
                                                    FStar_Syntax_Syntax.Data_ctor)
                                                in
                                             let sc1 =
                                               let uu____8750 =
                                                 let uu____8751 =
                                                   let uu____8766 =
                                                     mk1
                                                       (FStar_Syntax_Syntax.Tm_fvar
                                                          tupn)
                                                      in
                                                   let uu____8769 =
                                                     let uu____8778 =
                                                       let uu____8787 =
                                                         let uu____8794 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x
                                                            in
                                                         FStar_All.pipe_left
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____8794
                                                          in
                                                       [uu____8787]  in
                                                     FStar_List.append args
                                                       uu____8778
                                                      in
                                                   (uu____8766, uu____8769)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____8751
                                                  in
                                               mk1 uu____8750  in
                                             let p2 =
                                               let uu____8832 =
                                                 FStar_Range.union_ranges
                                                   p'.FStar_Syntax_Syntax.p
                                                   p1.FStar_Syntax_Syntax.p
                                                  in
                                               FStar_Syntax_Syntax.withinfo
                                                 (FStar_Syntax_Syntax.Pat_cons
                                                    (tupn,
                                                      (FStar_List.append pats
                                                         [(p1, false)])))
                                                 uu____8832
                                                in
                                             FStar_Pervasives_Native.Some
                                               (sc1, p2)
                                         | uu____8873 ->
                                             failwith "Impossible")
                                     in
                                  ((x, aq), sc_pat_opt1)
                               in
                            (match uu____8336 with
                             | (b1,sc_pat_opt1) ->
                                 aux env2 (b1 :: bs) sc_pat_opt1 rest))
                    in
                 aux env [] FStar_Pervasives_Native.None binders2)
        | FStar_Parser_AST.App
            (uu____8954,uu____8955,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____8977 =
                let uu____8978 = unparen e  in uu____8978.FStar_Parser_AST.tm
                 in
              match uu____8977 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____8988 ->
                  let uu____8989 = desugar_term_aq env e  in
                  (match uu____8989 with
                   | (head1,aq) ->
                       let uu____9002 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____9002, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____9009 ->
            let rec aux args aqs e =
              let uu____9068 =
                let uu____9069 = unparen e  in uu____9069.FStar_Parser_AST.tm
                 in
              match uu____9068 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____9089 = desugar_term_aq env t  in
                  (match uu____9089 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____9125 ->
                  let uu____9126 = desugar_term_aq env e  in
                  (match uu____9126 with
                   | (head1,aq) ->
                       let uu____9149 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____9149, (join_aqs (aq :: aqs))))
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
            let uu____9201 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____9201
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
            let uu____9253 = desugar_term_aq env t  in
            (match uu____9253 with
             | (tm,s) ->
                 let uu____9264 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____9264, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____9270 =
              let uu____9283 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____9283 then desugar_typ_aq else desugar_term_aq  in
            uu____9270 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____9338 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____9481  ->
                        match uu____9481 with
                        | (attr_opt,(p,def)) ->
                            let uu____9539 = is_app_pattern p  in
                            if uu____9539
                            then
                              let uu____9570 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____9570, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____9652 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____9652, def1)
                               | uu____9697 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____9735);
                                           FStar_Parser_AST.prange =
                                             uu____9736;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____9784 =
                                            let uu____9805 =
                                              let uu____9810 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____9810  in
                                            (uu____9805, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____9784, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____9901) ->
                                        if top_level
                                        then
                                          let uu____9936 =
                                            let uu____9957 =
                                              let uu____9962 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____9962  in
                                            (uu____9957, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____9936, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____10052 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____10083 =
                FStar_List.fold_left
                  (fun uu____10156  ->
                     fun uu____10157  ->
                       match (uu____10156, uu____10157) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____10265,uu____10266),uu____10267))
                           ->
                           let uu____10384 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____10410 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____10410 with
                                  | (env2,xx) ->
                                      let uu____10429 =
                                        let uu____10432 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____10432 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____10429))
                             | FStar_Util.Inr l ->
                                 let uu____10440 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (uu____10440, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____10384 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____10083 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____10588 =
                    match uu____10588 with
                    | (attrs_opt,(uu____10624,args,result_t),def) ->
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
                                let uu____10712 = is_comp_type env1 t  in
                                if uu____10712
                                then
                                  ((let uu____10714 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____10724 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____10724))
                                       in
                                    match uu____10714 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____10727 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____10729 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____10729))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             (Prims.parse_int "0")))
                                      in
                                   if uu____10727
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t)
                                 in
                              let uu____10733 =
                                FStar_Range.union_ranges
                                  t1.FStar_Parser_AST.range
                                  def.FStar_Parser_AST.range
                                 in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed (def, t1, tacopt))
                                uu____10733 FStar_Parser_AST.Expr
                           in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____10737 ->
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
                              let uu____10752 =
                                let uu____10753 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____10753
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____10752
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
                  let uu____10828 = desugar_term_aq env' body  in
                  (match uu____10828 with
                   | (body1,aq) ->
                       let uu____10841 =
                         let uu____10844 =
                           let uu____10845 =
                             let uu____10858 =
                               FStar_Syntax_Subst.close rec_bindings1 body1
                                in
                             ((is_rec, lbs1), uu____10858)  in
                           FStar_Syntax_Syntax.Tm_let uu____10845  in
                         FStar_All.pipe_left mk1 uu____10844  in
                       (uu____10841, aq))
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
              let uu____10936 =
                desugar_binding_pat_maybe_top top_level env pat is_mutable
                 in
              match uu____10936 with
              | (env1,binder,pat1) ->
                  let uu____10958 =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let uu____10984 = desugar_term_aq env1 t2  in
                        (match uu____10984 with
                         | (body1,aq) ->
                             let fv =
                               let uu____10998 =
                                 FStar_Syntax_Util.incr_delta_qualifier t12
                                  in
                               FStar_Syntax_Syntax.lid_as_fv l uu____10998
                                 FStar_Pervasives_Native.None
                                in
                             let uu____10999 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t12,
                                            (t12.FStar_Syntax_Syntax.pos))]),
                                      body1))
                                in
                             (uu____10999, aq))
                    | LocalBinder (x,uu____11029) ->
                        let uu____11030 = desugar_term_aq env1 t2  in
                        (match uu____11030 with
                         | (body1,aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | {
                                   FStar_Syntax_Syntax.v =
                                     FStar_Syntax_Syntax.Pat_wild uu____11044;
                                   FStar_Syntax_Syntax.p = uu____11045;_}::[]
                                   -> body1
                               | uu____11046 ->
                                   let uu____11049 =
                                     let uu____11056 =
                                       let uu____11057 =
                                         let uu____11080 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         let uu____11083 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1
                                            in
                                         (uu____11080, uu____11083)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____11057
                                        in
                                     FStar_Syntax_Syntax.mk uu____11056  in
                                   uu____11049 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range
                                in
                             let uu____11123 =
                               let uu____11126 =
                                 let uu____11127 =
                                   let uu____11140 =
                                     let uu____11143 =
                                       let uu____11144 =
                                         FStar_Syntax_Syntax.mk_binder x  in
                                       [uu____11144]  in
                                     FStar_Syntax_Subst.close uu____11143
                                       body2
                                      in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t12,
                                           (t12.FStar_Syntax_Syntax.pos))]),
                                     uu____11140)
                                    in
                                 FStar_Syntax_Syntax.Tm_let uu____11127  in
                               FStar_All.pipe_left mk1 uu____11126  in
                             (uu____11123, aq))
                     in
                  (match uu____10958 with
                   | (tm,aq) ->
                       if is_mutable
                       then
                         let uu____11201 =
                           FStar_All.pipe_left mk1
                             (FStar_Syntax_Syntax.Tm_meta
                                (tm,
                                  (FStar_Syntax_Syntax.Meta_desugared
                                     FStar_Syntax_Syntax.Mutable_alloc)))
                            in
                         (uu____11201, aq)
                       else (tm, aq))
               in
            let uu____11213 = FStar_List.hd lbs  in
            (match uu____11213 with
             | (attrs,(head_pat,defn)) ->
                 let uu____11257 = is_rec || (is_app_pattern head_pat)  in
                 if uu____11257
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____11270 =
                let uu____11271 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____11271  in
              mk1 uu____11270  in
            let uu____11272 = desugar_term_aq env t1  in
            (match uu____11272 with
             | (t1',aq1) ->
                 let uu____11283 = desugar_term_aq env t2  in
                 (match uu____11283 with
                  | (t2',aq2) ->
                      let uu____11294 = desugar_term_aq env t3  in
                      (match uu____11294 with
                       | (t3',aq3) ->
                           let uu____11305 =
                             let uu____11306 =
                               let uu____11307 =
                                 let uu____11330 =
                                   let uu____11347 =
                                     let uu____11362 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t2.FStar_Parser_AST.range
                                        in
                                     (uu____11362,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____11375 =
                                     let uu____11392 =
                                       let uu____11407 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t3.FStar_Parser_AST.range
                                          in
                                       (uu____11407,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____11392]  in
                                   uu____11347 :: uu____11375  in
                                 (t1', uu____11330)  in
                               FStar_Syntax_Syntax.Tm_match uu____11307  in
                             mk1 uu____11306  in
                           (uu____11305, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____11606 =
              match uu____11606 with
              | (pat,wopt,b) ->
                  let uu____11628 = desugar_match_pat env pat  in
                  (match uu____11628 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____11659 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____11659
                          in
                       let uu____11660 = desugar_term_aq env1 b  in
                       (match uu____11660 with
                        | (b1,aq) ->
                            let uu____11673 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____11673, aq)))
               in
            let uu____11678 = desugar_term_aq env e  in
            (match uu____11678 with
             | (e1,aq) ->
                 let uu____11689 =
                   let uu____11712 =
                     let uu____11737 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____11737 FStar_List.unzip  in
                   FStar_All.pipe_right uu____11712
                     (fun uu____11843  ->
                        match uu____11843 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____11689 with
                  | (brs,aqs) ->
                      let uu____12006 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____12006, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let annot =
              let uu____12051 = is_comp_type env t  in
              if uu____12051
              then
                let uu____12060 = desugar_comp t.FStar_Parser_AST.range env t
                   in
                FStar_Util.Inr uu____12060
              else
                (let uu____12068 = desugar_term env t  in
                 FStar_Util.Inl uu____12068)
               in
            let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)  in
            let uu____12078 = desugar_term_aq env e  in
            (match uu____12078 with
             | (e1,aq) ->
                 let uu____12089 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_ascribed
                        (e1, (annot, tac_opt1), FStar_Pervasives_Native.None))
                    in
                 (uu____12089, aq))
        | FStar_Parser_AST.Record (uu____12122,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____12163 = FStar_List.hd fields  in
              match uu____12163 with | (f,uu____12175) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____12221  ->
                        match uu____12221 with
                        | (g,uu____12227) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____12233,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____12247 =
                         let uu____12252 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____12252)
                          in
                       FStar_Errors.raise_error uu____12247
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
                  let uu____12260 =
                    let uu____12271 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____12302  ->
                              match uu____12302 with
                              | (f,uu____12312) ->
                                  let uu____12313 =
                                    let uu____12314 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____12314
                                     in
                                  (uu____12313, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____12271)  in
                  FStar_Parser_AST.Construct uu____12260
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____12332 =
                      let uu____12333 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____12333  in
                    FStar_Parser_AST.mk_term uu____12332
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____12335 =
                      let uu____12348 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____12378  ->
                                match uu____12378 with
                                | (f,uu____12388) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____12348)  in
                    FStar_Parser_AST.Record uu____12335  in
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
            let uu____12448 = desugar_term_aq env recterm1  in
            (match uu____12448 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____12464;
                         FStar_Syntax_Syntax.vars = uu____12465;_},args)
                      ->
                      let uu____12487 =
                        let uu____12488 =
                          let uu____12489 =
                            let uu____12504 =
                              let uu____12507 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____12508 =
                                let uu____12511 =
                                  let uu____12512 =
                                    let uu____12519 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____12519)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____12512
                                   in
                                FStar_Pervasives_Native.Some uu____12511  in
                              FStar_Syntax_Syntax.fvar uu____12507
                                FStar_Syntax_Syntax.delta_constant
                                uu____12508
                               in
                            (uu____12504, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____12489  in
                        FStar_All.pipe_left mk1 uu____12488  in
                      (uu____12487, s)
                  | uu____12546 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____12550 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____12550 with
              | (constrname,is_rec) ->
                  let uu____12565 = desugar_term_aq env e  in
                  (match uu____12565 with
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
                       let uu____12583 =
                         let uu____12584 =
                           let uu____12585 =
                             let uu____12600 =
                               let uu____12603 =
                                 let uu____12604 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____12604
                                  in
                               FStar_Syntax_Syntax.fvar uu____12603
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    (Prims.parse_int "1")) qual
                                in
                             let uu____12605 =
                               let uu____12614 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____12614]  in
                             (uu____12600, uu____12605)  in
                           FStar_Syntax_Syntax.Tm_app uu____12585  in
                         FStar_All.pipe_left mk1 uu____12584  in
                       (uu____12583, s))))
        | FStar_Parser_AST.NamedTyp (uu____12643,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____12652 =
              let uu____12653 = FStar_Syntax_Subst.compress tm  in
              uu____12653.FStar_Syntax_Syntax.n  in
            (match uu____12652 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____12661 =
                   let uu___164_12662 =
                     let uu____12663 =
                       let uu____12664 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____12664  in
                     FStar_Syntax_Util.exp_string uu____12663  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___164_12662.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___164_12662.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____12661, noaqs)
             | uu____12665 ->
                 let uu____12666 =
                   let uu____12671 =
                     let uu____12672 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.strcat "VQuote, expected an fvar, got: "
                       uu____12672
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____12671)  in
                 FStar_Errors.raise_error uu____12666
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____12678 = desugar_term_aq env e  in
            (match uu____12678 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____12690 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____12690, noaqs))
        | FStar_Parser_AST.Antiquote (b,e) ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____12696 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____12697 =
              let uu____12698 =
                let uu____12707 = desugar_term env e  in (bv, b, uu____12707)
                 in
              [uu____12698]  in
            (uu____12696, uu____12697)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____12738 =
              let uu____12739 =
                let uu____12740 =
                  let uu____12747 = desugar_term env e  in (uu____12747, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____12740  in
              FStar_All.pipe_left mk1 uu____12739  in
            (uu____12738, noaqs)
        | uu____12752 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____12753 = desugar_formula env top  in
            (uu____12753, noaqs)
        | uu____12754 ->
            let uu____12755 =
              let uu____12760 =
                let uu____12761 = FStar_Parser_AST.term_to_string top  in
                Prims.strcat "Unexpected term: " uu____12761  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____12760)  in
            FStar_Errors.raise_error uu____12755 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____12767 -> false
    | uu____12776 -> true

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
           (fun uu____12813  ->
              match uu____12813 with
              | (a,imp) ->
                  let uu____12826 = desugar_term env a  in
                  arg_withimp_e imp uu____12826))

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
        let is_requires uu____12858 =
          match uu____12858 with
          | (t1,uu____12864) ->
              let uu____12865 =
                let uu____12866 = unparen t1  in
                uu____12866.FStar_Parser_AST.tm  in
              (match uu____12865 with
               | FStar_Parser_AST.Requires uu____12867 -> true
               | uu____12874 -> false)
           in
        let is_ensures uu____12884 =
          match uu____12884 with
          | (t1,uu____12890) ->
              let uu____12891 =
                let uu____12892 = unparen t1  in
                uu____12892.FStar_Parser_AST.tm  in
              (match uu____12891 with
               | FStar_Parser_AST.Ensures uu____12893 -> true
               | uu____12900 -> false)
           in
        let is_app head1 uu____12915 =
          match uu____12915 with
          | (t1,uu____12921) ->
              let uu____12922 =
                let uu____12923 = unparen t1  in
                uu____12923.FStar_Parser_AST.tm  in
              (match uu____12922 with
               | FStar_Parser_AST.App
                   ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                      FStar_Parser_AST.range = uu____12925;
                      FStar_Parser_AST.level = uu____12926;_},uu____12927,uu____12928)
                   -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
               | uu____12929 -> false)
           in
        let is_smt_pat uu____12939 =
          match uu____12939 with
          | (t1,uu____12945) ->
              let uu____12946 =
                let uu____12947 = unparen t1  in
                uu____12947.FStar_Parser_AST.tm  in
              (match uu____12946 with
               | FStar_Parser_AST.Construct
                   (cons1,({
                             FStar_Parser_AST.tm = FStar_Parser_AST.Construct
                               (smtpat,uu____12950);
                             FStar_Parser_AST.range = uu____12951;
                             FStar_Parser_AST.level = uu____12952;_},uu____12953)::uu____12954::[])
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
                             FStar_Parser_AST.range = uu____12993;
                             FStar_Parser_AST.level = uu____12994;_},uu____12995)::uu____12996::[])
                   ->
                   (FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid)
                     &&
                     (FStar_Util.for_some
                        (fun s  -> smtpat.FStar_Ident.str = s)
                        ["smt_pat"; "smt_pat_or"])
               | uu____13021 -> false)
           in
        let is_decreases = is_app "decreases"  in
        let pre_process_comp_typ t1 =
          let uu____13053 = head_and_args t1  in
          match uu____13053 with
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
                   let thunk_ens uu____13151 =
                     match uu____13151 with
                     | (e,i) ->
                         let uu____13162 = thunk_ens_ e  in (uu____13162, i)
                      in
                   let fail_lemma uu____13174 =
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
                         let uu____13254 =
                           let uu____13261 =
                             let uu____13268 = thunk_ens ens  in
                             [uu____13268; nil_pat]  in
                           req_true :: uu____13261  in
                         unit_tm :: uu____13254
                     | req::ens::[] when
                         (is_requires req) && (is_ensures ens) ->
                         let uu____13315 =
                           let uu____13322 =
                             let uu____13329 = thunk_ens ens  in
                             [uu____13329; nil_pat]  in
                           req :: uu____13322  in
                         unit_tm :: uu____13315
                     | ens::smtpat::[] when
                         (((let uu____13378 = is_requires ens  in
                            Prims.op_Negation uu____13378) &&
                             (let uu____13380 = is_smt_pat ens  in
                              Prims.op_Negation uu____13380))
                            &&
                            (let uu____13382 = is_decreases ens  in
                             Prims.op_Negation uu____13382))
                           && (is_smt_pat smtpat)
                         ->
                         let uu____13383 =
                           let uu____13390 =
                             let uu____13397 = thunk_ens ens  in
                             [uu____13397; smtpat]  in
                           req_true :: uu____13390  in
                         unit_tm :: uu____13383
                     | ens::dec::[] when
                         (is_ensures ens) && (is_decreases dec) ->
                         let uu____13444 =
                           let uu____13451 =
                             let uu____13458 = thunk_ens ens  in
                             [uu____13458; nil_pat; dec]  in
                           req_true :: uu____13451  in
                         unit_tm :: uu____13444
                     | ens::dec::smtpat::[] when
                         ((is_ensures ens) && (is_decreases dec)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____13518 =
                           let uu____13525 =
                             let uu____13532 = thunk_ens ens  in
                             [uu____13532; smtpat; dec]  in
                           req_true :: uu____13525  in
                         unit_tm :: uu____13518
                     | req::ens::dec::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_decreases dec)
                         ->
                         let uu____13592 =
                           let uu____13599 =
                             let uu____13606 = thunk_ens ens  in
                             [uu____13606; nil_pat; dec]  in
                           req :: uu____13599  in
                         unit_tm :: uu____13592
                     | req::ens::smtpat::[] when
                         ((is_requires req) && (is_ensures ens)) &&
                           (is_smt_pat smtpat)
                         ->
                         let uu____13666 =
                           let uu____13673 =
                             let uu____13680 = thunk_ens ens  in
                             [uu____13680; smtpat]  in
                           req :: uu____13673  in
                         unit_tm :: uu____13666
                     | req::ens::dec::smtpat::[] when
                         (((is_requires req) && (is_ensures ens)) &&
                            (is_smt_pat smtpat))
                           && (is_decreases dec)
                         ->
                         let uu____13745 =
                           let uu____13752 =
                             let uu____13759 = thunk_ens ens  in
                             [uu____13759; dec; smtpat]  in
                           req :: uu____13752  in
                         unit_tm :: uu____13745
                     | _other -> fail_lemma ()  in
                   let head_and_attributes =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) lemma
                      in
                   (head_and_attributes, args1)
               | FStar_Parser_AST.Name l when
                   FStar_Syntax_DsEnv.is_effect_name env l ->
                   let uu____13821 =
                     FStar_Syntax_DsEnv.fail_or env
                       (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                          env) l
                      in
                   (uu____13821, args)
               | FStar_Parser_AST.Name l when
                   (let uu____13849 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____13849
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                   ->
                   let uu____13850 =
                     let uu____13857 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_Tot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____13857, [])  in
                   (uu____13850, args)
               | FStar_Parser_AST.Name l when
                   (let uu____13875 = FStar_Syntax_DsEnv.current_module env
                       in
                    FStar_Ident.lid_equals uu____13875
                      FStar_Parser_Const.prims_lid)
                     && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                   ->
                   let uu____13876 =
                     let uu____13883 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_GTot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____13883, [])  in
                   (uu____13876, args)
               | FStar_Parser_AST.Name l when
                   (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                      ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                     || ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                   ->
                   let uu____13899 =
                     let uu____13906 =
                       FStar_Ident.set_lid_range
                         FStar_Parser_Const.effect_Tot_lid
                         head1.FStar_Parser_AST.range
                        in
                     (uu____13906, [])  in
                   (uu____13899, [(t1, FStar_Parser_AST.Nothing)])
               | uu____13929 ->
                   let default_effect =
                     let uu____13931 = FStar_Options.ml_ish ()  in
                     if uu____13931
                     then FStar_Parser_Const.effect_ML_lid
                     else
                       ((let uu____13934 =
                           FStar_Options.warn_default_effects ()  in
                         if uu____13934
                         then
                           FStar_Errors.log_issue
                             head1.FStar_Parser_AST.range
                             (FStar_Errors.Warning_UseDefaultEffect,
                               "Using default effect Tot")
                         else ());
                        FStar_Parser_Const.effect_Tot_lid)
                      in
                   let uu____13936 =
                     let uu____13943 =
                       FStar_Ident.set_lid_range default_effect
                         head1.FStar_Parser_AST.range
                        in
                     (uu____13943, [])  in
                   (uu____13936, [(t1, FStar_Parser_AST.Nothing)]))
           in
        let uu____13966 = pre_process_comp_typ t  in
        match uu____13966 with
        | ((eff,cattributes),args) ->
            (if (FStar_List.length args) = (Prims.parse_int "0")
             then
               (let uu____14015 =
                  let uu____14020 =
                    let uu____14021 = FStar_Syntax_Print.lid_to_string eff
                       in
                    FStar_Util.format1 "Not enough args to effect %s"
                      uu____14021
                     in
                  (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____14020)  in
                fail1 uu____14015)
             else ();
             (let is_universe uu____14032 =
                match uu____14032 with
                | (uu____14037,imp) -> imp = FStar_Parser_AST.UnivApp  in
              let uu____14039 = FStar_Util.take is_universe args  in
              match uu____14039 with
              | (universes,args1) ->
                  let universes1 =
                    FStar_List.map
                      (fun uu____14098  ->
                         match uu____14098 with
                         | (u,imp) -> desugar_universe u) universes
                     in
                  let uu____14105 =
                    let uu____14120 = FStar_List.hd args1  in
                    let uu____14129 = FStar_List.tl args1  in
                    (uu____14120, uu____14129)  in
                  (match uu____14105 with
                   | (result_arg,rest) ->
                       let result_typ =
                         desugar_typ env
                           (FStar_Pervasives_Native.fst result_arg)
                          in
                       let rest1 = desugar_args env rest  in
                       let uu____14184 =
                         let is_decrease uu____14222 =
                           match uu____14222 with
                           | (t1,uu____14232) ->
                               (match t1.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_app
                                    ({
                                       FStar_Syntax_Syntax.n =
                                         FStar_Syntax_Syntax.Tm_fvar fv;
                                       FStar_Syntax_Syntax.pos = uu____14242;
                                       FStar_Syntax_Syntax.vars = uu____14243;_},uu____14244::[])
                                    ->
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.decreases_lid
                                | uu____14275 -> false)
                            in
                         FStar_All.pipe_right rest1
                           (FStar_List.partition is_decrease)
                          in
                       (match uu____14184 with
                        | (dec,rest2) ->
                            let decreases_clause =
                              FStar_All.pipe_right dec
                                (FStar_List.map
                                   (fun uu____14391  ->
                                      match uu____14391 with
                                      | (t1,uu____14401) ->
                                          (match t1.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (uu____14410,(arg,uu____14412)::[])
                                               ->
                                               FStar_Syntax_Syntax.DECREASES
                                                 arg
                                           | uu____14441 -> failwith "impos")))
                               in
                            let no_additional_args =
                              let is_empty l =
                                match l with
                                | [] -> true
                                | uu____14458 -> false  in
                              (((is_empty decreases_clause) &&
                                  (is_empty rest2))
                                 && (is_empty cattributes))
                                && (is_empty universes1)
                               in
                            let uu____14469 =
                              no_additional_args &&
                                (FStar_Ident.lid_equals eff
                                   FStar_Parser_Const.effect_Tot_lid)
                               in
                            if uu____14469
                            then FStar_Syntax_Syntax.mk_Total result_typ
                            else
                              (let uu____14473 =
                                 no_additional_args &&
                                   (FStar_Ident.lid_equals eff
                                      FStar_Parser_Const.effect_GTot_lid)
                                  in
                               if uu____14473
                               then FStar_Syntax_Syntax.mk_GTotal result_typ
                               else
                                 (let flags1 =
                                    let uu____14480 =
                                      FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_Lemma_lid
                                       in
                                    if uu____14480
                                    then [FStar_Syntax_Syntax.LEMMA]
                                    else
                                      (let uu____14484 =
                                         FStar_Ident.lid_equals eff
                                           FStar_Parser_Const.effect_Tot_lid
                                          in
                                       if uu____14484
                                       then [FStar_Syntax_Syntax.TOTAL]
                                       else
                                         (let uu____14488 =
                                            FStar_Ident.lid_equals eff
                                              FStar_Parser_Const.effect_ML_lid
                                             in
                                          if uu____14488
                                          then [FStar_Syntax_Syntax.MLEFFECT]
                                          else
                                            (let uu____14492 =
                                               FStar_Ident.lid_equals eff
                                                 FStar_Parser_Const.effect_GTot_lid
                                                in
                                             if uu____14492
                                             then
                                               [FStar_Syntax_Syntax.SOMETRIVIAL]
                                             else [])))
                                     in
                                  let flags2 =
                                    FStar_List.append flags1 cattributes  in
                                  let rest3 =
                                    let uu____14508 =
                                      FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_Lemma_lid
                                       in
                                    if uu____14508
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
                                                  let uu____14593 =
                                                    FStar_Ident.set_lid_range
                                                      FStar_Parser_Const.pattern_lid
                                                      pat.FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_Syntax.fvar
                                                    uu____14593
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
                                            | uu____14608 -> pat  in
                                          let uu____14609 =
                                            let uu____14620 =
                                              let uu____14631 =
                                                let uu____14640 =
                                                  FStar_Syntax_Syntax.mk
                                                    (FStar_Syntax_Syntax.Tm_meta
                                                       (pat1,
                                                         (FStar_Syntax_Syntax.Meta_desugared
                                                            FStar_Syntax_Syntax.Meta_smt_pat)))
                                                    FStar_Pervasives_Native.None
                                                    pat1.FStar_Syntax_Syntax.pos
                                                   in
                                                (uu____14640, aq)  in
                                              [uu____14631]  in
                                            ens :: uu____14620  in
                                          req :: uu____14609
                                      | uu____14681 -> rest2
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
        | uu____14705 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___165_14726 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___165_14726.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___165_14726.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___166_14768 = b  in
             {
               FStar_Parser_AST.b = (uu___166_14768.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___166_14768.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___166_14768.FStar_Parser_AST.aqual)
             })
           in
        let desugar_pats env1 pats1 =
          FStar_List.map
            (fun es  ->
               FStar_All.pipe_right es
                 (FStar_List.map
                    (fun e  ->
                       let uu____14831 = desugar_term env1 e  in
                       FStar_All.pipe_left
                         (arg_withimp_t FStar_Parser_AST.Nothing) uu____14831)))
            pats1
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____14844 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____14844 with
             | (env1,a1) ->
                 let a2 =
                   let uu___167_14854 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___167_14854.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___167_14854.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let pats1 = desugar_pats env1 pats  in
                 let body1 = desugar_formula env1 body  in
                 let body2 =
                   match pats1 with
                   | [] -> body1
                   | uu____14880 ->
                       mk1
                         (FStar_Syntax_Syntax.Tm_meta
                            (body1, (FStar_Syntax_Syntax.Meta_pattern pats1)))
                    in
                 let body3 =
                   let uu____14894 =
                     let uu____14897 =
                       let uu____14898 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____14898]  in
                     no_annot_abs uu____14897 body2  in
                   FStar_All.pipe_left setpos uu____14894  in
                 let uu____14913 =
                   let uu____14914 =
                     let uu____14929 =
                       let uu____14932 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____14932
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            (Prims.parse_int "1"))
                         FStar_Pervasives_Native.None
                        in
                     let uu____14933 =
                       let uu____14942 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____14942]  in
                     (uu____14929, uu____14933)  in
                   FStar_Syntax_Syntax.Tm_app uu____14914  in
                 FStar_All.pipe_left mk1 uu____14913)
        | uu____14973 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____15053 = q (rest, pats, body)  in
              let uu____15060 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____15053 uu____15060
                FStar_Parser_AST.Formula
               in
            let uu____15061 = q ([b], [], body1)  in
            FStar_Parser_AST.mk_term uu____15061 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____15070 -> failwith "impossible"  in
      let uu____15073 =
        let uu____15074 = unparen f  in uu____15074.FStar_Parser_AST.tm  in
      match uu____15073 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____15081,uu____15082) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____15093,uu____15094) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____15125 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____15125
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____15161 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____15161
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____15204 -> desugar_term env f

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
      let uu____15209 =
        FStar_List.fold_left
          (fun uu____15245  ->
             fun b  ->
               match uu____15245 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___168_15297 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___168_15297.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___168_15297.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___168_15297.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____15314 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____15314 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___169_15334 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___169_15334.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___169_15334.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             (env2,
                               ((a2, (trans_aqual b.FStar_Parser_AST.aqual))
                               :: out)))
                    | uu____15351 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____15209 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

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
          let uu____15438 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____15438)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____15443 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____15443)
      | FStar_Parser_AST.TVariable x ->
          let uu____15447 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____15447)
      | FStar_Parser_AST.NoName t ->
          let uu____15451 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____15451)
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
               (fun uu___123_15490  ->
                  match uu___123_15490 with
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____15491 -> false))
           in
        let quals2 q =
          let uu____15504 =
            (let uu____15507 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____15507) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____15504
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____15521 = FStar_Ident.range_of_lid disc_name  in
                let uu____15522 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____15521;
                  FStar_Syntax_Syntax.sigquals = uu____15522;
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
            let uu____15561 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____15595  ->
                        match uu____15595 with
                        | (x,uu____15603) ->
                            let uu____15604 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____15604 with
                             | (field_name,uu____15612) ->
                                 let only_decl =
                                   ((let uu____15616 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____15616)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____15618 =
                                        let uu____15619 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____15619.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____15618)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____15635 =
                                       FStar_List.filter
                                         (fun uu___124_15639  ->
                                            match uu___124_15639 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____15640 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____15635
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___125_15653  ->
                                             match uu___125_15653 with
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____15654 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____15656 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____15656;
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____15661 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____15661
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          (FStar_Syntax_Syntax.Delta_equational_at_level
                                             (Prims.parse_int "1"))
                                      else
                                        FStar_Syntax_Syntax.Delta_equational_at_level
                                          (Prims.parse_int "1")
                                       in
                                    let lb =
                                      let uu____15666 =
                                        let uu____15671 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____15671  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____15666;
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
                                      let uu____15675 =
                                        let uu____15676 =
                                          let uu____15683 =
                                            let uu____15686 =
                                              let uu____15687 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____15687
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____15686]  in
                                          ((false, [lb]), uu____15683)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____15676
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____15675;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____15561 FStar_List.flatten
  
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
            (lid,uu____15731,t,uu____15733,n1,uu____15735) when
            let uu____15740 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____15740 ->
            let uu____15741 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____15741 with
             | (formals,uu____15757) ->
                 (match formals with
                  | [] -> []
                  | uu____15780 ->
                      let filter_records uu___126_15794 =
                        match uu___126_15794 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____15797,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____15809 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____15811 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____15811 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Syntax_Syntax.Data_ctor
                        | FStar_Pervasives_Native.Some q -> q  in
                      let iquals1 =
                        if
                          FStar_List.contains FStar_Syntax_Syntax.Abstract
                            iquals
                        then FStar_Syntax_Syntax.Private :: iquals
                        else iquals  in
                      let uu____15821 = FStar_Util.first_N n1 formals  in
                      (match uu____15821 with
                       | (uu____15844,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____15870 -> []
  
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
                    let uu____15940 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____15940
                    then
                      let uu____15943 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____15943
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____15946 =
                      let uu____15951 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____15951  in
                    let uu____15952 =
                      let uu____15955 = FStar_Syntax_Syntax.mk_Total k  in
                      FStar_Syntax_Util.arrow typars uu____15955  in
                    let uu____15958 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____15946;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____15952;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____15958;
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
          let tycon_id uu___127_16009 =
            match uu___127_16009 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____16011,uu____16012) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____16022,uu____16023,uu____16024) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____16034,uu____16035,uu____16036) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____16066,uu____16067,uu____16068) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____16112) ->
                let uu____16113 =
                  let uu____16114 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____16114  in
                FStar_Parser_AST.mk_term uu____16113 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____16116 =
                  let uu____16117 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____16117  in
                FStar_Parser_AST.mk_term uu____16116 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____16119) ->
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
              | uu____16150 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____16156 =
                     let uu____16157 =
                       let uu____16164 = binder_to_term b  in
                       (out, uu____16164, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____16157  in
                   FStar_Parser_AST.mk_term uu____16156
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___128_16176 =
            match uu___128_16176 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.strcat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____16232  ->
                       match uu____16232 with
                       | (x,t,uu____16243) ->
                           let uu____16248 =
                             let uu____16249 =
                               let uu____16254 =
                                 FStar_Syntax_Util.mangle_field_name x  in
                               (uu____16254, t)  in
                             FStar_Parser_AST.Annotated uu____16249  in
                           FStar_Parser_AST.mk_binder uu____16248
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____16256 =
                    let uu____16257 =
                      let uu____16258 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____16258  in
                    FStar_Parser_AST.mk_term uu____16257
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____16256 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let uu____16262 =
                  FStar_All.pipe_right fields
                    (FStar_List.map
                       (fun uu____16289  ->
                          match uu____16289 with
                          | (x,uu____16299,uu____16300) ->
                              FStar_Syntax_Util.unmangle_field_name x))
                   in
                ((FStar_Parser_AST.TyconVariant
                    (id1, parms, kopt,
                      [(constrName, (FStar_Pervasives_Native.Some constrTyp),
                         FStar_Pervasives_Native.None, false)])),
                  uu____16262)
            | uu____16353 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___129_16392 =
            match uu___129_16392 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____16416 = typars_of_binders _env binders  in
                (match uu____16416 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____16458 =
                         let uu____16459 =
                           let uu____16460 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____16460  in
                         FStar_Parser_AST.mk_term uu____16459
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____16458 binders  in
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
            | uu____16471 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____16519 =
              FStar_List.fold_left
                (fun uu____16559  ->
                   fun uu____16560  ->
                     match (uu____16559, uu____16560) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____16651 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____16651 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____16519 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____16764 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____16764
                | uu____16765 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____16773 = desugar_abstract_tc quals env [] tc  in
              (match uu____16773 with
               | (uu____16786,uu____16787,se,uu____16789) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____16792,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____16809 =
                                 let uu____16810 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____16810  in
                               if uu____16809
                               then
                                 let uu____16811 =
                                   let uu____16816 =
                                     let uu____16817 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____16817
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____16816)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____16811
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
                           | uu____16824 ->
                               let uu____16825 =
                                 let uu____16832 =
                                   let uu____16833 =
                                     let uu____16846 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____16846)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____16833
                                    in
                                 FStar_Syntax_Syntax.mk uu____16832  in
                               uu____16825 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___170_16860 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___170_16860.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___170_16860.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___170_16860.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____16861 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____16864 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____16864
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____16877 = typars_of_binders env binders  in
              (match uu____16877 with
               | (env',typars) ->
                   let k =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____16913 =
                           FStar_Util.for_some
                             (fun uu___130_16915  ->
                                match uu___130_16915 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____16916 -> false) quals
                            in
                         if uu____16913
                         then FStar_Syntax_Syntax.teff
                         else FStar_Syntax_Util.ktype
                     | FStar_Pervasives_Native.Some k -> desugar_term env' k
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____16923 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___131_16927  ->
                               match uu___131_16927 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____16928 -> false))
                        in
                     if uu____16923
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____16937 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____16937
                     then
                       let uu____16940 =
                         let uu____16947 =
                           let uu____16948 = unparen t  in
                           uu____16948.FStar_Parser_AST.tm  in
                         match uu____16947 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____16969 =
                               match FStar_List.rev args with
                               | (last_arg,uu____16999)::args_rev ->
                                   let uu____17011 =
                                     let uu____17012 = unparen last_arg  in
                                     uu____17012.FStar_Parser_AST.tm  in
                                   (match uu____17011 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____17040 -> ([], args))
                               | uu____17049 -> ([], args)  in
                             (match uu____16969 with
                              | (cattributes,args1) ->
                                  let uu____17088 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____17088))
                         | uu____17099 -> (t, [])  in
                       match uu____16940 with
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
                                  (fun uu___132_17121  ->
                                     match uu___132_17121 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____17122 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____17129)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____17153 = tycon_record_as_variant trec  in
              (match uu____17153 with
               | (t,fs) ->
                   let uu____17170 =
                     let uu____17173 =
                       let uu____17174 =
                         let uu____17183 =
                           let uu____17186 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____17186  in
                         (uu____17183, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____17174  in
                     uu____17173 :: quals  in
                   desugar_tycon env d uu____17170 [t])
          | uu____17191::uu____17192 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____17359 = et  in
                match uu____17359 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____17584 ->
                         let trec = tc  in
                         let uu____17608 = tycon_record_as_variant trec  in
                         (match uu____17608 with
                          | (t,fs) ->
                              let uu____17667 =
                                let uu____17670 =
                                  let uu____17671 =
                                    let uu____17680 =
                                      let uu____17683 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____17683  in
                                    (uu____17680, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____17671
                                   in
                                uu____17670 :: quals1  in
                              collect_tcs uu____17667 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____17770 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____17770 with
                          | (env2,uu____17830,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____17979 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____17979 with
                          | (env2,uu____18039,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____18164 ->
                         failwith "Unrecognized mutual type definition")
                 in
              let uu____18211 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____18211 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___134_18722  ->
                             match uu___134_18722 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____18789,uu____18790);
                                    FStar_Syntax_Syntax.sigrng = uu____18791;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____18792;
                                    FStar_Syntax_Syntax.sigmeta = uu____18793;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____18794;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____18855 =
                                     typars_of_binders env1 binders  in
                                   match uu____18855 with
                                   | (env2,tpars1) ->
                                       let uu____18886 =
                                         push_tparams env2 tpars1  in
                                       (match uu____18886 with
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
                                 let uu____18919 =
                                   let uu____18940 =
                                     mk_typ_abbrev id1 uvs tpars k t1 
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____18940)
                                    in
                                 [uu____18919]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____19008);
                                    FStar_Syntax_Syntax.sigrng = uu____19009;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____19011;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____19012;_},constrs,tconstr,quals1)
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
                                 let uu____19110 = push_tparams env1 tpars
                                    in
                                 (match uu____19110 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____19187  ->
                                             match uu____19187 with
                                             | (x,uu____19201) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____19209 =
                                        let uu____19238 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____19352  ->
                                                  match uu____19352 with
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
                                                        let uu____19408 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____19408
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
                                                                uu___133_19419
                                                                 ->
                                                                match uu___133_19419
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____19431
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____19439 =
                                                        let uu____19460 =
                                                          let uu____19461 =
                                                            let uu____19462 =
                                                              let uu____19477
                                                                =
                                                                let uu____19478
                                                                  =
                                                                  let uu____19481
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____19481
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____19478
                                                                 in
                                                              (name, univs1,
                                                                uu____19477,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____19462
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____19461;
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
                                                          uu____19460)
                                                         in
                                                      (name, uu____19439)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____19238
                                         in
                                      (match uu____19209 with
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
                             | uu____19718 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____19850  ->
                             match uu____19850 with
                             | (name_doc,uu____19878,uu____19879) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____19959  ->
                             match uu____19959 with
                             | (uu____19980,uu____19981,se) -> se))
                      in
                   let uu____20011 =
                     let uu____20018 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____20018 rng
                      in
                   (match uu____20011 with
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
                               (fun uu____20084  ->
                                  match uu____20084 with
                                  | (uu____20107,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____20158,tps,k,uu____20161,constrs)
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
                                  | uu____20180 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____20197  ->
                                 match uu____20197 with
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
      let uu____20240 =
        FStar_List.fold_left
          (fun uu____20275  ->
             fun b  ->
               match uu____20275 with
               | (env1,binders1) ->
                   let uu____20319 = desugar_binder env1 b  in
                   (match uu____20319 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____20342 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____20342 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____20397 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____20240 with
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
          let uu____20498 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___135_20503  ->
                    match uu___135_20503 with
                    | FStar_Syntax_Syntax.Reflectable uu____20504 -> true
                    | uu____20505 -> false))
             in
          if uu____20498
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____20508 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____20508
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
      let uu____20540 = FStar_Syntax_Util.head_and_args at1  in
      match uu____20540 with
      | (hd1,args) ->
          let uu____20585 =
            let uu____20598 =
              let uu____20599 = FStar_Syntax_Subst.compress hd1  in
              uu____20599.FStar_Syntax_Syntax.n  in
            (uu____20598, args)  in
          (match uu____20585 with
           | (FStar_Syntax_Syntax.Tm_fvar fv,(a1,uu____20620)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr
               ->
               let uu____20645 =
                 let uu____20650 =
                   FStar_Syntax_Embeddings.e_list
                     FStar_Syntax_Embeddings.e_int
                    in
                 FStar_Syntax_Embeddings.unembed uu____20650 a1  in
               (match uu____20645 with
                | FStar_Pervasives_Native.Some [] ->
                    FStar_Errors.raise_error
                      (FStar_Errors.Error_EmptyFailErrs,
                        "Found ill-applied fail, argument should be a non-empty list of integers")
                      at1.FStar_Syntax_Syntax.pos
                | FStar_Pervasives_Native.Some es ->
                    let uu____20680 =
                      let uu____20687 =
                        FStar_List.map FStar_BigInt.to_int_fs es  in
                      (uu____20687, false)  in
                    FStar_Pervasives_Native.Some uu____20680
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
           | (FStar_Syntax_Syntax.Tm_fvar fv,uu____20732) when
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
           | uu____20780 -> FStar_Pervasives_Native.None)
  
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
                  let uu____20947 = desugar_binders monad_env eff_binders  in
                  match uu____20947 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let for_free =
                        let uu____20986 =
                          let uu____20987 =
                            let uu____20994 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____20994  in
                          FStar_List.length uu____20987  in
                        uu____20986 = (Prims.parse_int "1")  in
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
                            (uu____21034,(FStar_Parser_AST.TyconAbbrev
                                          (name,uu____21036,uu____21037,uu____21038),uu____21039)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____21072 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____21073 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____21085 = name_of_eff_decl decl  in
                             FStar_List.mem uu____21085 mandatory_members)
                          eff_decls
                         in
                      (match uu____21073 with
                       | (mandatory_members_decls,actions) ->
                           let uu____21102 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____21131  ->
                                     fun decl  ->
                                       match uu____21131 with
                                       | (env2,out) ->
                                           let uu____21151 =
                                             desugar_decl env2 decl  in
                                           (match uu____21151 with
                                            | (env3,ses) ->
                                                let uu____21164 =
                                                  let uu____21167 =
                                                    FStar_List.hd ses  in
                                                  uu____21167 :: out  in
                                                (env3, uu____21164)))
                                  (env1, []))
                              in
                           (match uu____21102 with
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
                                              (uu____21235,(FStar_Parser_AST.TyconAbbrev
                                                            (name,action_params,uu____21238,
                                                             {
                                                               FStar_Parser_AST.tm
                                                                 =
                                                                 FStar_Parser_AST.Construct
                                                                 (uu____21239,
                                                                  (def,uu____21241)::
                                                                  (cps_type,uu____21243)::[]);
                                                               FStar_Parser_AST.range
                                                                 =
                                                                 uu____21244;
                                                               FStar_Parser_AST.level
                                                                 =
                                                                 uu____21245;_}),doc1)::[])
                                              when Prims.op_Negation for_free
                                              ->
                                              let uu____21297 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____21297 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____21335 =
                                                     let uu____21336 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____21337 =
                                                       let uu____21338 =
                                                         desugar_term env3
                                                           def
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____21338
                                                        in
                                                     let uu____21343 =
                                                       let uu____21344 =
                                                         desugar_typ env3
                                                           cps_type
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____21344
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____21336;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____21337;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____21343
                                                     }  in
                                                   (uu____21335, doc1))
                                          | FStar_Parser_AST.Tycon
                                              (uu____21351,(FStar_Parser_AST.TyconAbbrev
                                                            (name,action_params,uu____21354,defn),doc1)::[])
                                              when for_free ->
                                              let uu____21389 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____21389 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____21427 =
                                                     let uu____21428 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____21429 =
                                                       let uu____21430 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____21430
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____21428;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____21429;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____21427, doc1))
                                          | uu____21437 ->
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
                                    let uu____21469 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____21469
                                     in
                                  let uu____21470 =
                                    let uu____21471 =
                                      FStar_Syntax_DsEnv.fail_or env2
                                        (FStar_Syntax_DsEnv.try_lookup_definition
                                           env2) l
                                       in
                                    FStar_All.pipe_left
                                      (FStar_Syntax_Subst.close binders1)
                                      uu____21471
                                     in
                                  ([], uu____21470)  in
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
                                      let uu____21488 =
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      ([], uu____21488)  in
                                    let uu____21495 =
                                      let uu____21496 =
                                        let uu____21497 =
                                          let uu____21498 = lookup1 "repr"
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____21498
                                           in
                                        let uu____21507 = lookup1 "return"
                                           in
                                        let uu____21508 = lookup1 "bind"  in
                                        let uu____21509 =
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
                                            uu____21497;
                                          FStar_Syntax_Syntax.return_repr =
                                            uu____21507;
                                          FStar_Syntax_Syntax.bind_repr =
                                            uu____21508;
                                          FStar_Syntax_Syntax.actions =
                                            actions1;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            uu____21509
                                        }  in
                                      FStar_Syntax_Syntax.Sig_new_effect_for_free
                                        uu____21496
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____21495;
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
                                         (fun uu___136_21515  ->
                                            match uu___136_21515 with
                                            | FStar_Syntax_Syntax.Reifiable 
                                                -> true
                                            | FStar_Syntax_Syntax.Reflectable
                                                uu____21516 -> true
                                            | uu____21517 -> false)
                                         qualifiers
                                        in
                                     let un_ts =
                                       ([], FStar_Syntax_Syntax.tun)  in
                                     let uu____21531 =
                                       let uu____21532 =
                                         let uu____21533 =
                                           lookup1 "return_wp"  in
                                         let uu____21534 = lookup1 "bind_wp"
                                            in
                                         let uu____21535 =
                                           lookup1 "if_then_else"  in
                                         let uu____21536 = lookup1 "ite_wp"
                                            in
                                         let uu____21537 = lookup1 "stronger"
                                            in
                                         let uu____21538 = lookup1 "close_wp"
                                            in
                                         let uu____21539 = lookup1 "assert_p"
                                            in
                                         let uu____21540 = lookup1 "assume_p"
                                            in
                                         let uu____21541 = lookup1 "null_wp"
                                            in
                                         let uu____21542 = lookup1 "trivial"
                                            in
                                         let uu____21543 =
                                           if rr
                                           then
                                             let uu____21544 = lookup1 "repr"
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.snd
                                               uu____21544
                                           else FStar_Syntax_Syntax.tun  in
                                         let uu____21560 =
                                           if rr
                                           then lookup1 "return"
                                           else un_ts  in
                                         let uu____21562 =
                                           if rr
                                           then lookup1 "bind"
                                           else un_ts  in
                                         let uu____21564 =
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
                                             uu____21533;
                                           FStar_Syntax_Syntax.bind_wp =
                                             uu____21534;
                                           FStar_Syntax_Syntax.if_then_else =
                                             uu____21535;
                                           FStar_Syntax_Syntax.ite_wp =
                                             uu____21536;
                                           FStar_Syntax_Syntax.stronger =
                                             uu____21537;
                                           FStar_Syntax_Syntax.close_wp =
                                             uu____21538;
                                           FStar_Syntax_Syntax.assert_p =
                                             uu____21539;
                                           FStar_Syntax_Syntax.assume_p =
                                             uu____21540;
                                           FStar_Syntax_Syntax.null_wp =
                                             uu____21541;
                                           FStar_Syntax_Syntax.trivial =
                                             uu____21542;
                                           FStar_Syntax_Syntax.repr =
                                             uu____21543;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____21560;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____21562;
                                           FStar_Syntax_Syntax.actions =
                                             actions1;
                                           FStar_Syntax_Syntax.eff_attrs =
                                             uu____21564
                                         }  in
                                       FStar_Syntax_Syntax.Sig_new_effect
                                         uu____21532
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         uu____21531;
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
                                          fun uu____21590  ->
                                            match uu____21590 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____21604 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____21604
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
                let uu____21628 = desugar_binders env1 eff_binders  in
                match uu____21628 with
                | (env2,binders) ->
                    let uu____21665 =
                      let uu____21684 = head_and_args defn  in
                      match uu____21684 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____21729 ->
                                let uu____21730 =
                                  let uu____21735 =
                                    let uu____21736 =
                                      let uu____21737 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.strcat uu____21737 " not found"
                                       in
                                    Prims.strcat "Effect " uu____21736  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____21735)
                                   in
                                FStar_Errors.raise_error uu____21730
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____21739 =
                            match FStar_List.rev args with
                            | (last_arg,uu____21769)::args_rev ->
                                let uu____21781 =
                                  let uu____21782 = unparen last_arg  in
                                  uu____21782.FStar_Parser_AST.tm  in
                                (match uu____21781 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____21810 -> ([], args))
                            | uu____21819 -> ([], args)  in
                          (match uu____21739 with
                           | (cattributes,args1) ->
                               let uu____21870 = desugar_args env2 args1  in
                               let uu____21879 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____21870, uu____21879))
                       in
                    (match uu____21665 with
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
                          (let uu____21935 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____21935 with
                           | (ed_binders,uu____21949,ed_binders_opening) ->
                               let sub1 uu____21962 =
                                 match uu____21962 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____21976 =
                                         FStar_Syntax_Subst.shift_subst
                                           (FStar_List.length us)
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____21976 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____21980 =
                                       let uu____21981 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____21981)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____21980
                                  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____21990 =
                                   let uu____21991 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____21991
                                    in
                                 let uu____22006 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____22007 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____22008 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____22009 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____22010 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____22011 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____22012 =
                                   sub1 ed.FStar_Syntax_Syntax.assert_p  in
                                 let uu____22013 =
                                   sub1 ed.FStar_Syntax_Syntax.assume_p  in
                                 let uu____22014 =
                                   sub1 ed.FStar_Syntax_Syntax.null_wp  in
                                 let uu____22015 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____22016 =
                                   let uu____22017 =
                                     sub1 ([], (ed.FStar_Syntax_Syntax.repr))
                                      in
                                   FStar_Pervasives_Native.snd uu____22017
                                    in
                                 let uu____22032 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____22033 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____22034 =
                                   FStar_List.map
                                     (fun action  ->
                                        let uu____22042 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____22043 =
                                          let uu____22044 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____22044
                                           in
                                        let uu____22059 =
                                          let uu____22060 =
                                            sub1
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____22060
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____22042;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____22043;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____22059
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
                                     uu____21990;
                                   FStar_Syntax_Syntax.ret_wp = uu____22006;
                                   FStar_Syntax_Syntax.bind_wp = uu____22007;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____22008;
                                   FStar_Syntax_Syntax.ite_wp = uu____22009;
                                   FStar_Syntax_Syntax.stronger = uu____22010;
                                   FStar_Syntax_Syntax.close_wp = uu____22011;
                                   FStar_Syntax_Syntax.assert_p = uu____22012;
                                   FStar_Syntax_Syntax.assume_p = uu____22013;
                                   FStar_Syntax_Syntax.null_wp = uu____22014;
                                   FStar_Syntax_Syntax.trivial = uu____22015;
                                   FStar_Syntax_Syntax.repr = uu____22016;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____22032;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____22033;
                                   FStar_Syntax_Syntax.actions = uu____22034;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____22077 =
                                     let uu____22078 =
                                       let uu____22085 =
                                         FStar_Syntax_Util.arrow_formals
                                           ed1.FStar_Syntax_Syntax.signature
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____22085
                                        in
                                     FStar_List.length uu____22078  in
                                   uu____22077 = (Prims.parse_int "1")  in
                                 let uu____22110 =
                                   let uu____22113 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____22113 quals  in
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
                                   FStar_Syntax_Syntax.sigquals = uu____22110;
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
                                             let uu____22135 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____22135
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____22137 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____22137
                                 then
                                   let reflect_lid =
                                     let uu____22141 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____22141
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
    let uu____22151 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____22151 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.strcat "  " (Prims.strcat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____22202 ->
              let uu____22203 =
                let uu____22204 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.parse_int "80")
                  uu____22204
                 in
              Prims.strcat "\n  " uu____22203
          | uu____22205 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____22218  ->
               match uu____22218 with
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
          let uu____22236 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____22236
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let arg = FStar_Syntax_Util.exp_string str  in
        let uu____22238 =
          let uu____22247 = FStar_Syntax_Syntax.as_arg arg  in [uu____22247]
           in
        FStar_Syntax_Util.mk_app fv uu____22238

and (desugar_decl_aux :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      let uu____22272 = desugar_decl_noattrs env d  in
      match uu____22272 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let attrs2 =
            let uu____22290 = mk_comment_attr d  in uu____22290 :: attrs1  in
          let uu____22291 =
            FStar_List.mapi
              (fun i  ->
                 fun sigelt  ->
                   if i = (Prims.parse_int "0")
                   then
                     let uu___171_22297 = sigelt  in
                     {
                       FStar_Syntax_Syntax.sigel =
                         (uu___171_22297.FStar_Syntax_Syntax.sigel);
                       FStar_Syntax_Syntax.sigrng =
                         (uu___171_22297.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___171_22297.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___171_22297.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs = attrs2
                     }
                   else
                     (let uu___172_22299 = sigelt  in
                      let uu____22300 =
                        FStar_List.filter
                          (fun at1  ->
                             let uu____22306 = get_fail_attr false at1  in
                             FStar_Option.isNone uu____22306) attrs2
                         in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___172_22299.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___172_22299.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___172_22299.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___172_22299.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs = uu____22300
                      })) sigelts
             in
          (env1, uu____22291)

and (desugar_decl :
  env_t ->
    FStar_Parser_AST.decl ->
      (env_t,FStar_Syntax_Syntax.sigelts) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun d  ->
      let uu____22327 = desugar_decl_aux env d  in
      match uu____22327 with
      | (env1,ses) ->
          let uu____22338 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____22338)

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
      | FStar_Parser_AST.Fsdoc uu____22366 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____22374 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____22374, [])
      | FStar_Parser_AST.Tycon (is_effect,tcs) ->
          let quals =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: (d.FStar_Parser_AST.quals)
            else d.FStar_Parser_AST.quals  in
          let tcs1 =
            FStar_List.map
              (fun uu____22411  ->
                 match uu____22411 with | (x,uu____22419) -> x) tcs
             in
          let uu____22424 =
            FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals
             in
          desugar_tycon env d uu____22424 tcs1
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals  in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____22446;
                    FStar_Parser_AST.prange = uu____22447;_},uu____22448)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____22457;
                    FStar_Parser_AST.prange = uu____22458;_},uu____22459)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____22474;
                         FStar_Parser_AST.prange = uu____22475;_},uu____22476);
                    FStar_Parser_AST.prange = uu____22477;_},uu____22478)::[]
                   -> false
               | (p,uu____22506)::[] ->
                   let uu____22515 = is_app_pattern p  in
                   Prims.op_Negation uu____22515
               | uu____22516 -> false)
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
            let uu____22589 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____22589 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____22601 =
                     let uu____22602 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____22602.FStar_Syntax_Syntax.n  in
                   match uu____22601 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____22612) ->
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
                         | uu____22645::uu____22646 ->
                             FStar_List.map
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____22649 ->
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.collect
                                  (fun uu___137_22664  ->
                                     match uu___137_22664 with
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inl uu____22667;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____22668;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____22669;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____22670;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____22671;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____22672;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____22673;_}
                                         -> []
                                     | {
                                         FStar_Syntax_Syntax.lbname =
                                           FStar_Util.Inr fv;
                                         FStar_Syntax_Syntax.lbunivs =
                                           uu____22685;
                                         FStar_Syntax_Syntax.lbtyp =
                                           uu____22686;
                                         FStar_Syntax_Syntax.lbeff =
                                           uu____22687;
                                         FStar_Syntax_Syntax.lbdef =
                                           uu____22688;
                                         FStar_Syntax_Syntax.lbattrs =
                                           uu____22689;
                                         FStar_Syntax_Syntax.lbpos =
                                           uu____22690;_}
                                         ->
                                         FStar_Syntax_DsEnv.lookup_letbinding_quals
                                           env
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                          in
                       let quals2 =
                         let uu____22704 =
                           FStar_All.pipe_right lets1
                             (FStar_Util.for_some
                                (fun uu____22735  ->
                                   match uu____22735 with
                                   | (uu____22748,(uu____22749,t)) ->
                                       t.FStar_Parser_AST.level =
                                         FStar_Parser_AST.Formula))
                            in
                         if uu____22704
                         then FStar_Syntax_Syntax.Logic :: quals1
                         else quals1  in
                       let lbs1 =
                         let uu____22767 =
                           FStar_All.pipe_right quals2
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract)
                            in
                         if uu____22767
                         then
                           let uu____22770 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu___173_22784 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___174_22786 = fv  in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___174_22786.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___174_22786.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___173_22784.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___173_22784.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___173_22784.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___173_22784.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___173_22784.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___173_22784.FStar_Syntax_Syntax.lbpos)
                                     }))
                              in
                           ((FStar_Pervasives_Native.fst lbs), uu____22770)
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
                   | uu____22813 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____22819 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____22838 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____22819 with
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
                       let uu___175_22874 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___175_22874.FStar_Parser_AST.prange)
                       }
                   | uu____22881 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___176_22888 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___176_22888.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___176_22888.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___176_22888.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____22924 id1 =
                   match uu____22924 with
                   | (env1,ses) ->
                       let main =
                         let uu____22945 =
                           let uu____22946 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____22946  in
                         FStar_Parser_AST.mk_term uu____22945
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
                       let uu____22996 = desugar_decl env1 id_decl  in
                       (match uu____22996 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____23014 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____23014 FStar_Util.set_elements
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
            let uu____23039 = close_fun env t  in
            desugar_term env uu____23039  in
          let quals1 =
            let uu____23043 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____23043
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let se =
            let uu____23049 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____23049;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in
          let env2 =
            FStar_Syntax_DsEnv.push_doc env1 lid d.FStar_Parser_AST.doc  in
          (env2, [se])
      | FStar_Parser_AST.Exception (id1,FStar_Pervasives_Native.None ) ->
          let uu____23057 =
            FStar_Syntax_DsEnv.fail_or env
              (FStar_Syntax_DsEnv.try_lookup_lid env)
              FStar_Parser_Const.exn_lid
             in
          (match uu____23057 with
           | (t,uu____23071) ->
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
            let uu____23101 =
              let uu____23108 = FStar_Syntax_Syntax.null_binder t  in
              [uu____23108]  in
            let uu____23121 =
              let uu____23124 =
                let uu____23125 =
                  FStar_Syntax_DsEnv.fail_or env
                    (FStar_Syntax_DsEnv.try_lookup_lid env)
                    FStar_Parser_Const.exn_lid
                   in
                FStar_Pervasives_Native.fst uu____23125  in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____23124
               in
            FStar_Syntax_Util.arrow uu____23101 uu____23121  in
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
            let uu____23186 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____23186 with
            | FStar_Pervasives_Native.None  ->
                let uu____23189 =
                  let uu____23194 =
                    let uu____23195 =
                      let uu____23196 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.strcat uu____23196 " not found"  in
                    Prims.strcat "Effect name " uu____23195  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____23194)  in
                FStar_Errors.raise_error uu____23189
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____23200 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____23242 =
                  let uu____23251 =
                    let uu____23258 = desugar_term env t  in
                    ([], uu____23258)  in
                  FStar_Pervasives_Native.Some uu____23251  in
                (uu____23242, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____23291 =
                  let uu____23300 =
                    let uu____23307 = desugar_term env wp  in
                    ([], uu____23307)  in
                  FStar_Pervasives_Native.Some uu____23300  in
                let uu____23316 =
                  let uu____23325 =
                    let uu____23332 = desugar_term env t  in
                    ([], uu____23332)  in
                  FStar_Pervasives_Native.Some uu____23325  in
                (uu____23291, uu____23316)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____23358 =
                  let uu____23367 =
                    let uu____23374 = desugar_term env t  in
                    ([], uu____23374)  in
                  FStar_Pervasives_Native.Some uu____23367  in
                (FStar_Pervasives_Native.None, uu____23358)
             in
          (match uu____23200 with
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
            let uu____23452 =
              let uu____23453 =
                let uu____23460 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____23460, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____23453  in
            {
              FStar_Syntax_Syntax.sigel = uu____23452;
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
      let uu____23486 =
        FStar_List.fold_left
          (fun uu____23506  ->
             fun d  ->
               match uu____23506 with
               | (env1,sigelts) ->
                   let uu____23526 = desugar_decl env1 d  in
                   (match uu____23526 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____23486 with
      | (env1,sigelts) ->
          let rec forward acc uu___139_23571 =
            match uu___139_23571 with
            | se1::se2::sigelts1 ->
                (match ((se1.FStar_Syntax_Syntax.sigel),
                         (se2.FStar_Syntax_Syntax.sigel))
                 with
                 | (FStar_Syntax_Syntax.Sig_declare_typ
                    uu____23585,FStar_Syntax_Syntax.Sig_let uu____23586) ->
                     let uu____23599 =
                       let uu____23602 =
                         let uu___177_23603 = se2  in
                         let uu____23604 =
                           let uu____23607 =
                             FStar_List.filter
                               (fun uu___138_23621  ->
                                  match uu___138_23621 with
                                  | {
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_app
                                        ({
                                           FStar_Syntax_Syntax.n =
                                             FStar_Syntax_Syntax.Tm_fvar fv;
                                           FStar_Syntax_Syntax.pos =
                                             uu____23625;
                                           FStar_Syntax_Syntax.vars =
                                             uu____23626;_},uu____23627);
                                      FStar_Syntax_Syntax.pos = uu____23628;
                                      FStar_Syntax_Syntax.vars = uu____23629;_}
                                      when
                                      let uu____23652 =
                                        let uu____23653 =
                                          FStar_Syntax_Syntax.lid_of_fv fv
                                           in
                                        FStar_Ident.string_of_lid uu____23653
                                         in
                                      uu____23652 =
                                        "FStar.Pervasives.Comment"
                                      -> true
                                  | uu____23654 -> false)
                               se1.FStar_Syntax_Syntax.sigattrs
                              in
                           FStar_List.append uu____23607
                             se2.FStar_Syntax_Syntax.sigattrs
                            in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (uu___177_23603.FStar_Syntax_Syntax.sigel);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___177_23603.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___177_23603.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___177_23603.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs = uu____23604
                         }  in
                       uu____23602 :: se1 :: acc  in
                     forward uu____23599 sigelts1
                 | uu____23659 -> forward (se1 :: acc) (se2 :: sigelts1))
            | sigelts1 -> FStar_List.rev_append acc sigelts1  in
          let uu____23667 = forward [] sigelts  in (env1, uu____23667)
  
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
          | (FStar_Pervasives_Native.None ,uu____23728) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____23732;
               FStar_Syntax_Syntax.exports = uu____23733;
               FStar_Syntax_Syntax.is_interface = uu____23734;_},FStar_Parser_AST.Module
             (current_lid,uu____23736)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____23744) ->
              let uu____23747 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____23747
           in
        let uu____23752 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____23788 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____23788, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____23805 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____23805, mname, decls, false)
           in
        match uu____23752 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____23835 = desugar_decls env2 decls  in
            (match uu____23835 with
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
          let uu____23897 =
            (FStar_Options.interactive ()) &&
              (let uu____23899 =
                 let uu____23900 =
                   let uu____23901 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____23901  in
                 FStar_Util.get_file_extension uu____23900  in
               FStar_List.mem uu____23899 ["fsti"; "fsi"])
             in
          if uu____23897 then as_interface m else m  in
        let uu____23905 = desugar_modul_common curmod env m1  in
        match uu____23905 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____23923 = FStar_Syntax_DsEnv.pop ()  in
              (uu____23923, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul ->
      (env_t,FStar_Syntax_Syntax.modul) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun m  ->
      let uu____23943 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____23943 with
      | (env1,modul,pop_when_done) ->
          let uu____23957 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____23957 with
           | (env2,modul1) ->
               ((let uu____23969 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____23969
                 then
                   let uu____23970 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____23970
                 else ());
                (let uu____23972 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____23972, modul1))))
  
let (ast_modul_to_modul :
  FStar_Parser_AST.modul ->
    FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun env  ->
      let uu____23990 = desugar_modul env modul  in
      match uu____23990 with | (env1,modul1) -> (modul1, env1)
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      let uu____24021 = desugar_decls env decls  in
      match uu____24021 with | (env1,sigelts) -> (sigelts, env1)
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        let uu____24063 = desugar_partial_modul modul env a_modul  in
        match uu____24063 with | (env1,modul1) -> (modul1, env1)
  
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
              | uu____24149 ->
                  let t =
                    let uu____24157 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____24157  in
                  let uu____24168 =
                    let uu____24169 = FStar_Syntax_Subst.compress t  in
                    uu____24169.FStar_Syntax_Syntax.n  in
                  (match uu____24168 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____24179,uu____24180)
                       -> bs1
                   | uu____24201 -> failwith "Impossible")
               in
            let uu____24208 =
              let uu____24215 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____24215
                FStar_Syntax_Syntax.t_unit
               in
            match uu____24208 with
            | (binders,uu____24217,binders_opening) ->
                let erase_term t =
                  let uu____24225 =
                    let uu____24226 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____24226  in
                  FStar_Syntax_Subst.close binders uu____24225  in
                let erase_tscheme uu____24244 =
                  match uu____24244 with
                  | (us,t) ->
                      let t1 =
                        let uu____24264 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____24264 t  in
                      let uu____24267 =
                        let uu____24268 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____24268  in
                      ([], uu____24267)
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
                    | uu____24287 ->
                        let bs =
                          let uu____24295 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____24295  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____24327 =
                          let uu____24328 =
                            let uu____24331 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____24331  in
                          uu____24328.FStar_Syntax_Syntax.n  in
                        (match uu____24327 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____24333,uu____24334) -> bs1
                         | uu____24355 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____24362 =
                      let uu____24363 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____24363  in
                    FStar_Syntax_Subst.close binders uu____24362  in
                  let uu___178_24364 = action  in
                  let uu____24365 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____24366 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___178_24364.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___178_24364.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____24365;
                    FStar_Syntax_Syntax.action_typ = uu____24366
                  }  in
                let uu___179_24367 = ed  in
                let uu____24368 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____24369 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____24370 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____24371 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____24372 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____24373 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____24374 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____24375 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____24376 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                let uu____24377 =
                  erase_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                let uu____24378 =
                  erase_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                let uu____24379 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____24380 = erase_term ed.FStar_Syntax_Syntax.repr  in
                let uu____24381 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____24382 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____24383 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___179_24367.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___179_24367.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____24368;
                  FStar_Syntax_Syntax.signature = uu____24369;
                  FStar_Syntax_Syntax.ret_wp = uu____24370;
                  FStar_Syntax_Syntax.bind_wp = uu____24371;
                  FStar_Syntax_Syntax.if_then_else = uu____24372;
                  FStar_Syntax_Syntax.ite_wp = uu____24373;
                  FStar_Syntax_Syntax.stronger = uu____24374;
                  FStar_Syntax_Syntax.close_wp = uu____24375;
                  FStar_Syntax_Syntax.assert_p = uu____24376;
                  FStar_Syntax_Syntax.assume_p = uu____24377;
                  FStar_Syntax_Syntax.null_wp = uu____24378;
                  FStar_Syntax_Syntax.trivial = uu____24379;
                  FStar_Syntax_Syntax.repr = uu____24380;
                  FStar_Syntax_Syntax.return_repr = uu____24381;
                  FStar_Syntax_Syntax.bind_repr = uu____24382;
                  FStar_Syntax_Syntax.actions = uu____24383;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___179_24367.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___180_24399 = se  in
                  let uu____24400 =
                    let uu____24401 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____24401  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____24400;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___180_24399.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___180_24399.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___180_24399.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___180_24399.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___181_24405 = se  in
                  let uu____24406 =
                    let uu____24407 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____24407
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____24406;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___181_24405.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___181_24405.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___181_24405.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___181_24405.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____24409 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____24410 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____24410 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____24422 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____24422
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____24424 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____24424)
  